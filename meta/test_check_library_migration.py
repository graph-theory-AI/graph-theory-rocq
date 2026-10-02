#!/usr/bin/env python3
"""Real pinned-Rocq regressions for exact migration source-closure builds."""
from __future__ import annotations

from collections import Counter
import contextlib
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

import check_library_migration as M


class MigrationBuildTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="migration-build-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.env = M.ROCQ.environment()
        for name, value in (("ROOT", self.root), ("NAMESPACE_PACKAGES", {
                "Fixture": "fixture", "Support": "support", "Leaf": "leaf", "Unused": "unused"})):
            replacement = patch.object(M, name, value)
            replacement.start()
            self.addCleanup(replacement.stop)
        self.write("leaf/theories/base.v", "Definition claim : Prop := 2 = 2.\n"
                   "Lemma witness : claim. Proof. reflexivity. Qed.\n")
        self.write("leaf/theories/alt.v", (self.root / "leaf/theories/base.v").read_text())
        self.write("support/theories/middle.v", "From Leaf Require Export base.\n"
                   "Lemma middle : claim. Proof. exact witness. Qed.\n")
        self.write("support/theories/unrelated.v", "Lemma unrelated : True. Proof. exact I. Qed.\n")
        self.write("unused/theories/unrelated.v", "Lemma unrelated : True. Proof. exact I. Qed.\n")
        self.write("fixture/theories/helper.v", "From Support Require Export middle.\n"
                   "Lemma helper : claim. Proof. exact middle. Qed.\n")
        self.write("fixture/theories/cert.v", "From Fixture Require Import helper.\n"
                   "Theorem closed : claim. Proof. exact helper. Qed.\n")
        self.write("leaf/_CoqProject", "-Q theories Leaf\ntheories/base.v\ntheories/alt.v\n")
        self.write("support/_CoqProject", "-Q theories Support\n-Q ../leaf/theories Leaf\n"
                   "theories/middle.v\ntheories/unrelated.v\n")
        self.write("unused/_CoqProject", "-Q theories Unused\ntheories/unrelated.v\n")
        self.write("fixture/_CoqProject", "-R theories Fixture\n-Q ../support/theories Support\n"
                   "-Q ../leaf/theories Leaf\n-Q ../unused/theories Unused\n"
                   "-arg -w -arg -notation-overridden,-ambiguous-paths\n"
                   "theories/helper.v\ntheories/cert.v\n")
        self.primitive = {
            "canonical_name": "Leaf.base.claim", "owner": "leaf", "status": "canonical",
            "fidelity": "FAITHFUL", "normalized_names": ["fixture"],
            "source_definitions": [], "consumers_remaining": 0, "upstream_audit": {},
            "api_theorems": ["Fixture.cert.closed"], "compatibility_theorems": [],
        }
        self.write_registry()

    def write(self, relative, text):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def write_registry(self):
        self.write("meta/library_primitives/fixture.json", json.dumps({
            "schema_version": 1, "family": "fixture", "primitive": self.primitive}))

    def append_source(self, package, name, text):
        path = self.write(f"{package}/theories/{name}.v", text)
        with (self.root / package / "_CoqProject").open("a") as project:
            project.write(f"theories/{name}.v\n")
        return path

    def preserved_mtime_edit(self, path, text):
        before = path.stat()
        path.write_text(text)
        os.utime(path, ns=(before.st_atime_ns, before.st_mtime_ns))

    def build_targets(self, package, *targets):
        directory = self.root / package
        M.run_build_tool(["rocq", "makefile", "-f", "_CoqProject", "-o", "Makefile.coq"],
                         directory, self.env)
        return M.run_build_tool(["make", "-f", "Makefile.coq", *targets], directory, self.env)

    def gate(self):
        output = io.StringIO()
        with contextlib.redirect_stdout(output), contextlib.redirect_stderr(output):
            code = M.main()
        return code, output.getvalue()

    def assert_gate_passes(self):
        code, output = self.gate()
        self.assertEqual(code, 0, output)
        return output

    def assert_gate_fails(self, text):
        code, output = self.gate()
        self.assertEqual(code, 1, output)
        self.assertIn(text, output)

    def test_clean_cross_package_closure_excludes_unrelated_loaded_modules(self):
        unrelated = [self.root / "support/theories/unrelated.v",
                     self.root / "unused/theories/unrelated.v"]
        for path in unrelated:
            self.build_targets(path.relative_to(self.root).parts[0], "theories/unrelated.vo")
            self.preserved_mtime_edit(path, "Lemma unrelated : False. Proof. exact I. Qed.\n")
        mtimes = [path.with_suffix(".vo").stat().st_mtime_ns for path in unrelated]
        output = self.assert_gate_passes()
        self.assertIn("4 local source targets across 3 packages", output)
        self.assertEqual([path.with_suffix(".vo").stat().st_mtime_ns for path in unrelated], mtimes)

    def test_stale_unregistered_transitive_proof_is_recompiled(self):
        self.assert_gate_passes()
        leaf = self.root / "leaf/theories/base.v"
        self.preserved_mtime_edit(leaf, "Definition claim : Prop := 2 = 2.\n"
                                 "Lemma witness : claim. Proof. exact I. Qed.\n")
        self.assertTrue(leaf.with_suffix(".vo").exists())
        self.assert_gate_fails("leaf: make -B")

    def test_inherited_make_and_compiler_overrides_cannot_hide_a_stale_proof(self):
        leaf = self.root / "leaf/theories/base.v"
        clean_source = leaf.read_text()
        overrides = [
            {"MAKEFLAGS": "n -j2"},
            {"MAKEFLAGS": "t"},
            {"GNUMAKEFLAGS": "-n", "MFLAGS": "-n"},
            {"MAKEFLAGS": "ROCQ=true", "MAKEOVERRIDES": "ROCQ=true"},
            {"ROCQ": "true", "TIMER": "true"},
            {"COQFLAGS": "-vos"},
        ]
        for override in overrides:
            with self.subTest(override=override):
                leaf.write_text(clean_source)
                self.assert_gate_passes()
                self.preserved_mtime_edit(leaf, "Definition claim : Prop := 2 = 2.\n"
                                         "Lemma witness : claim. Proof. exact I. Qed.\n")
                with patch.dict(os.environ, override):
                    self.assert_gate_fails("leaf: make -B")

    def test_numeric_parallelism_survives_environment_sanitization(self):
        actual_run = M.subprocess.run
        build_environments = []

        def recording(command, **options):
            if command[0] == "make":
                build_environments.append(options["env"])
            return actual_run(command, **options)

        with patch.dict(os.environ, {"MAKEFLAGS": "-n --jobs=2 --eval=ROCQ=true",
                                     "MAKEFILES": "/nonexistent/injected.mk",
                                     "COQFLAGS": "-vos", "OCAMLRUNPARAM": "s=1M,o=20,v=0x400"}), \
                patch.object(M.subprocess, "run", side_effect=recording):
            self.assert_gate_passes()
        self.assertEqual(len(build_environments), 3)
        self.assertTrue((self.root / "fixture/theories/cert.vo").is_file())
        for env in build_environments:
            self.assertEqual(env["MAKEFLAGS"], "-j2")
            self.assertEqual(env["OCAMLRUNPARAM"], "s=1M,o=20,v=0x400")
            self.assertNotIn("MAKEFILES", env)
            self.assertNotIn("COQFLAGS", env)

    def test_changed_require_ignores_stale_dependency_file_and_timestamps(self):
        self.assert_gate_passes()
        self.build_targets("leaf", "theories/alt.vo")
        alt = self.root / "leaf/theories/alt.v"
        self.preserved_mtime_edit(alt, "Definition claim : Prop := 2 = 2.\n"
                                 "Lemma witness : claim. Proof. exact I. Qed.\n")
        middle = self.root / "support/theories/middle.v"
        old_dependencies = (self.root / "support/.Makefile.coq.d").read_bytes()
        self.preserved_mtime_edit(middle, middle.read_text().replace("Export base", "Export alt"))
        self.assertEqual((self.root / "support/.Makefile.coq.d").read_bytes(), old_dependencies)
        self.assert_gate_fails("leaf: make -B")

    def test_load_fragment_is_reread_and_its_changed_import_is_forced(self):
        self.write("fixture/theories/cert.v", "Load \"snippet\".\n"
                   "Theorem closed : claim. Proof. exact witness. Qed.\n")
        snippet = self.write("fixture/theories/snippet.v", "From Leaf Require Import base.\n")
        self.assert_gate_passes()
        self.assertFalse(snippet.with_suffix(".vo").exists())
        self.build_targets("leaf", "theories/alt.vo")
        alt = self.root / "leaf/theories/alt.v"
        self.preserved_mtime_edit(alt, "Definition claim : Prop := 2 = 2.\n"
                                 "Lemma witness : claim. Proof. exact I. Qed.\n")
        self.preserved_mtime_edit(snippet, "From Leaf Require Import alt.\n")
        self.assert_gate_fails("leaf: make -B")

    def test_mutable_external_object_cannot_replace_local_source_ownership(self):
        self.assert_gate_passes()
        with tempfile.TemporaryDirectory(prefix="unowned-library-") as temporary:
            external = Path(temporary) / "leaf"
            shutil.move(self.root / "leaf", external)
            source = external / "theories/base.v"
            self.preserved_mtime_edit(source, "Definition claim : Prop := 2 = 2.\n"
                                     "Lemma witness : claim. Proof. exact I. Qed.\n")
            for package in ("fixture", "support"):
                project = self.root / package / "_CoqProject"
                project.write_text(project.read_text().replace(
                    "../leaf/theories", str(external / "theories")))
            self.assert_gate_fails("non-pinned external dependency")

    def test_local_object_alias_into_pinned_library_cannot_hide_invalid_source(self):
        library = Path(M.run_build_tool(["rocq", "compile", "-where"], self.root,
                                       self.env).strip())
        installed = library / "theories/Init/Logic.vo"
        self.assertTrue(installed.is_file())
        source = self.write("localcore/theories/Logic.v",
                            "Lemma invalid : False. Proof. exact I. Qed.\n")
        self.write("localcore/_CoqProject", "-Q theories Corelib.Init\ntheories/Logic.v\n")
        source.with_suffix(".vo").symlink_to(installed)
        self.write("fixture/_CoqProject", "-Q theories Fixture\n"
                   "-Q ../localcore/theories Corelib.Init\ntheories/cert.v\n")
        self.write("fixture/theories/cert.v", "From Corelib.Init Require Import Logic.\n"
                   "Theorem closed : True. Proof. exact I. Qed.\n")
        self.assert_gate_fails("local object alias")

    def test_registered_object_alias_cannot_relocate_its_dependency_rule(self):
        self.assert_gate_passes()
        cert = self.root / "fixture/theories/cert.v"
        alias = self.root / "saved.vo"
        cert.with_suffix(".vo").rename(alias)
        cert.with_suffix(".vo").symlink_to(alias)
        self.preserved_mtime_edit(cert, "From Fixture Require Import helper.\n"
                                 "Theorem closed : claim. Proof. exact I. Qed.\n")
        self.assert_gate_fails("local object alias")

    def test_external_object_alias_cannot_claim_pinned_ownership(self):
        library = Path(M.run_build_tool(["rocq", "compile", "-where"], self.root,
                                       self.env).strip())
        with tempfile.TemporaryDirectory(prefix="unowned-alias-") as temporary:
            external = Path(temporary)
            (external / "Logic.v").write_text("Lemma invalid : False. Proof. exact I. Qed.\n")
            (external / "Logic.vo").symlink_to(library / "theories/Init/Logic.vo")
            self.write("fixture/_CoqProject", "-Q theories Fixture\n"
                       f"-Q {external} Corelib.Init\ntheories/cert.v\n")
            self.write("fixture/theories/cert.v", "From Corelib.Init Require Import Logic.\n"
                       "Theorem closed : True. Proof. exact I. Qed.\n")
            self.assert_gate_fails("non-pinned external dependency")

    def test_local_object_directory_alias_into_pinned_library_is_rejected(self):
        library = Path(M.run_build_tool(["rocq", "compile", "-where"], self.root,
                                       self.env).strip())
        (self.root / "fixture/pinned-alias").symlink_to(library / "theories/Init",
                                                      target_is_directory=True)
        self.write("fixture/_CoqProject", "-Q theories Fixture\n"
                   "-Q pinned-alias Corelib.Init\ntheories/cert.v\n")
        self.write("fixture/theories/cert.v", "From Corelib.Init Require Import Logic.\n"
                   "Theorem closed : True. Proof. exact I. Qed.\n")
        self.assert_gate_fails("local object alias")

    def test_all_roots_and_diamond_compile_each_local_source_once(self):
        for name in ("left", "right"):
            self.append_source("fixture", name, "From Support Require Export middle.\n"
                               f"Lemma {name} : claim. Proof. exact middle. Qed.\n")
        self.write("fixture/theories/cert.v", "From Fixture Require Import left right.\n"
                   "Theorem closed : claim. Proof. exact left. Qed.\n")
        self.primitive["api_theorems"].append("Fixture.helper.helper")
        self.write_registry()
        calls = []
        original = M.run_build_tool

        def recording(command, directory, env, **options):
            output = original(command, directory, env, **options)
            if command[0] == "make":
                calls.append((directory.name, command, output))
            return output

        with patch.object(M, "run_build_tool", side_effect=recording):
            self.assert_gate_passes()
        self.assertEqual([package for package, _, _ in calls], ["leaf", "support", "fixture"])
        compiled = Counter()
        for package, command, output in calls:
            self.assertEqual(command[:4], ["make", "-B", "-f", "Makefile.coq"])
            self.assertTrue(command[4:])
            for line in output.splitlines():
                if line.startswith("ROCQ compile "):
                    compiled[(package, line.removeprefix("ROCQ compile "))] += 1
        expected = {("leaf", "theories/base.v"), ("support", "theories/middle.v")}
        expected.update(("fixture", f"theories/{name}.v")
                        for name in ("left", "right", "helper", "cert"))
        self.assertEqual(set(compiled), expected)
        self.assertEqual(set(compiled.values()), {1})

    def test_project_flags_preserve_prebuilt_dependents_and_object_digests(self):
        self.write("leaf/theories/base.v", "From mathcomp Require Import all_boot.\n"
                   "Definition claim : Prop := forall T : Type, T = T.\n"
                   "Lemma witness : claim. Proof. intros T; reflexivity. Qed.\n")
        with (self.root / "leaf/_CoqProject").open("a") as project:
            project.write("-arg -w -arg -notation-overridden,-ambiguous-paths\n")
        dependent = self.append_source("fixture", "dependent", "From Fixture Require Import cert.\n"
                                       "Theorem derived : Leaf.base.claim. Proof. exact closed. Qed.\n")
        self.assert_gate_passes()
        self.build_targets("fixture", "theories/dependent.vo")
        objects = [self.root / path for path in ("leaf/theories/base.vo", "support/theories/middle.vo",
                   "fixture/theories/helper.vo", "fixture/theories/cert.vo")]
        digests = [hashlib.sha256(path.read_bytes()).hexdigest() for path in objects]
        stamp = dependent.with_suffix(".vo").stat().st_mtime_ns
        self.assert_gate_passes()
        probe = self.write("Probe.v", "From Fixture Require Import dependent.\nCheck derived.\n")
        M.run_build_tool(["rocq", "compile", *M.include_flags(self.root / "fixture/_CoqProject"), str(probe)],
                         self.root / "fixture", self.env)
        self.assertEqual(dependent.with_suffix(".vo").stat().st_mtime_ns, stamp)
        self.assertEqual([hashlib.sha256(path.read_bytes()).hexdigest() for path in objects], digests)

    def test_missing_source_cannot_be_hidden_by_existing_object(self):
        self.assert_gate_passes()
        (self.root / "leaf/theories/base.v").unlink()
        self.assert_gate_fails("missing or non-owned project source")

    def test_required_unlisted_source_cannot_be_hidden_by_existing_object(self):
        self.assert_gate_passes()
        project = self.root / "leaf/_CoqProject"
        project.write_text(project.read_text().replace("theories/base.v\n", ""))
        self.assert_gate_fails("absent from its _CoqProject")

    def test_missing_owning_project_is_fatal(self):
        (self.root / "leaf/_CoqProject").unlink()
        self.assert_gate_fails("absent from its _CoqProject")

    def test_unresolved_require_warning_is_fatal(self):
        self.write("fixture/theories/cert.v", "From Leaf Require Import missing.\n")
        with patch.dict(os.environ, {"OCAMLRUNPARAM": "s=1M,o=20,v=0x400"}):
            self.assert_gate_fails("has not been found in the loadpath")

    def test_duplicate_or_foreign_project_ownership_is_fatal(self):
        with (self.root / "fixture/_CoqProject").open("a") as project:
            project.write("../leaf/theories/base.v\n")
        self.assert_gate_fails("non-owned project source")

    def test_source_dependency_cycle_is_fatal(self):
        self.write("fixture/theories/helper.v", "From Fixture Require Import cert.\n")
        self.assert_gate_fails("source dependency cycle")

    def test_package_cycle_is_fatal_even_with_acyclic_source_graph(self):
        self.append_source("fixture", "leaf_bridge", "Definition bridge := 0.\n")
        project = self.root / "leaf/_CoqProject"
        project.write_text(project.read_text() + "-Q ../fixture/theories Fixture\n")
        source = self.root / "leaf/theories/base.v"
        source.write_text("From Fixture Require Import leaf_bridge.\n" + source.read_text())
        self.assert_gate_fails("package dependency cycle")

    def test_recursive_short_require_is_supported(self):
        self.write("fixture/theories/cert.v", "Require Import helper.\n"
                   "Theorem closed : claim. Proof. exact helper. Qed.\n")
        self.assert_gate_passes()

    def test_hidden_load_resolution_and_non_vo_compiler_flags_are_rejected(self):
        project = self.root / "fixture/_CoqProject"
        original = project.read_text()
        for flag in ("-load-vernac-source", "-require-import", "-require-from", "-init-file",
                     "-Q", "-R", "-I", "-include", "-coqlib", "-vos", "-vok", "-o",
                     "-where", "-config", "--config", "-v", "--version", "-print-version",
                     "-list-tags", "-h", "-help", "--help", "-compat"):
            with self.subTest(flag=flag):
                project.write_text(original + f"-arg {flag} -arg hidden\n")
                self.assert_gate_fails(f"unsupported compiler flag {flag}")
        project.write_text(original)
        for custom in ("Makefile.coq.local", "Makefile.coq.local-late"):
            with self.subTest(custom=custom):
                path = self.write(f"fixture/{custom}", "COQEXTRAFLAGS = -require Hidden\n")
                self.assert_gate_fails(f"custom {custom}")
                path.unlink()

    def test_hidden_compiler_require_cannot_lend_a_stale_local_proof(self):
        self.write("fixture/theories/cert.v", "From Leaf Require Import base.\n"
                   "Theorem closed : claim. Proof. exact witness. Qed.\n")
        self.assert_gate_passes()
        leaf = self.root / "leaf/theories/base.v"
        self.preserved_mtime_edit(leaf, "Definition claim : Prop := 2 = 2.\n"
                                 "Lemma witness : claim. Proof. exact I. Qed.\n")
        self.write("fixture/theories/cert.v", "Theorem closed : Leaf.base.claim.\n"
                   "Proof. exact Leaf.base.witness. Qed.\n")
        with (self.root / "fixture/_CoqProject").open("a") as project:
            project.write("-arg -require-import -arg Leaf.base\n")
        self.assert_gate_fails("unsupported compiler flag -require-import")

    def test_vos_mode_cannot_leave_a_stale_clean_registered_object(self):
        self.assert_gate_passes()
        cert = self.root / "fixture/theories/cert.v"
        self.preserved_mtime_edit(cert, "From Fixture Require Import helper.\n"
                                 "Theorem closed : claim. Proof. exact I. Qed.\n")
        with (self.root / "fixture/_CoqProject").open("a") as project:
            project.write("-arg -vos\n")
        self.assert_gate_fails("unsupported compiler flag -vos")

    def test_compiler_query_cannot_leave_a_stale_clean_registered_object(self):
        self.assert_gate_passes()
        cert = self.root / "fixture/theories/cert.v"
        self.preserved_mtime_edit(cert, "From Fixture Require Import helper.\n"
                                 "Theorem closed : claim. Proof. exact I. Qed.\n")
        with (self.root / "fixture/_CoqProject").open("a") as project:
            project.write("-arg -where\n")
        self.assert_gate_fails("unsupported compiler flag -where")

    def test_custom_project_overrides_are_rejected(self):
        project = self.root / "fixture/_CoqProject"
        original = project.read_text()
        for override in ("-f hidden.project", "-coqlib /tmp/hidden", "COQEXTRAFLAGS = -require Hidden"):
            with self.subTest(override=override):
                project.write_text(original + override + "\n")
                self.assert_gate_fails("unsupported project override")

    def test_missing_dependency_rule_is_fatal(self):
        original = M.run_build_tool

        def missing(command, directory, env, **options):
            if command[:2] == ["rocq", "dep"]:
                return ""
            return original(command, directory, env, **options)

        with patch.object(M, "run_build_tool", side_effect=missing):
            self.assert_gate_fails("missing source dependency rule")

    def test_missing_load_source_is_fatal(self):
        self.write("fixture/theories/cert.v", 'Load "missing".\n')
        self.assert_gate_fails("failed")

    def test_dependency_parser_preserves_escaped_paths_and_continuations(self):
        self.assertEqual(M.dependency_rules(
            "theories/a.vo theories/a.glob: theories/a.v \\\n"
            " ../with\\ space/b.vo snippets/a\\#b.v dollar$$/c.vo\n"), {
                "theories/a.vo": {"theories/a.v", "../with space/b.vo", "snippets/a#b.v", "dollar$/c.vo"}})
        for text in ("malformed", "a.vo: a.v\na.vo: b.v\n", "a.vo: $(unknown)/b.vo\n"):
            with self.subTest(text=text), self.assertRaises(M.BuildError):
                M.dependency_rules(text)


if __name__ == "__main__":
    unittest.main(verbosity=2)

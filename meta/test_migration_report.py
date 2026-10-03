#!/usr/bin/env python3
"""Mutation regressions for report coverage and certificate correspondence.

Default tests are toolchain-free. --kernel also compiles three tiny standalone
fixture modules, including a closed but incorrectly guarded compatibility lemma.
No corpus package is built and no repository source or report is modified.
"""

from __future__ import annotations

import contextlib
import copy
import io
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import migration_report as REPORT


KERNEL = "--kernel" in sys.argv
if KERNEL:
    sys.argv.remove("--kernel")


class ReportTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="migration-report-test-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.root_patch = patch.object(REPORT, "ROOT", self.root)
        self.root_patch.start()
        self.addCleanup(self.root_patch.stop)
        self.reports_patch = patch.object(REPORT, "REPORTS", self.root / "meta/migration_reports")
        self.reports_patch.start()
        self.addCleanup(self.reports_patch.stop)
        self.source = "base/theories/conjectures/X0.v"
        self.certificate = "base/theories/migration/test_family.v"
        self.module = "GTBase.migration.test_family"
        self.helper = "GTBase.conjectures.X0.local_helper"
        self.statement = "GTBase.conjectures.X0.test_statement"
        self.original = (
            "From GTBase Require Import common.\n"
            "Definition local_helper (n : nat) : Prop := n = n.\n"
            "(** Corpus row: test\n    English statement: every number equals itself. *)\n"
            "Definition test_statement : Prop := forall n, local_helper n.\n"
        )
        self.write(self.source, self.original)
        self.write("base/theories/common.v", "Definition canonical (n : nat) : Prop := n = n.\n"
                   "Lemma unrelated : True. Proof. exact I. Qed.\n")
        self.write("base/_CoqProject", "-Q theories GTBase\ntheories/common.v\n"
                   "theories/conjectures/X0.v\ntheories/migration/test_family.v\n")
        self.registry = {"primitives": {"test-family": {
            "canonical_name": "GTBase.common.canonical",
            "owner": "base", "status": "migrating", "fidelity": "FAITHFUL",
            "normalized_names": ["local_helper"], "consumers_remaining": 1,
            "upstream_audit": {},
            "source_definitions": [self.helper],
            "compatibility_theorems": [self.module + ".helper_compat",
                                       self.module + ".statement_compat", "GTBase.common.unrelated"],
            "api_theorems": [],
        }}}
        self.write_json("meta/library_primitives/test-family.json", {
            "schema_version": 1, "family": "test-family",
            "primitive": self.registry["primitives"]["test-family"],
        })
        self.write_json("meta/library_helper_inventory.json", {"helpers": [{
            "qualified_name": self.helper,
            "declaration_hash": REPORT.sha256(REPORT.find_decl(self.original, "local_helper")["text"]),
        }]})
        self.row = {"formal_name": "test_statement", "repo": "base", "slug": "test",
                    "row_id": "test:0", "phase": "X0", "status": "open",
                    "legs": {"statement": "done"}}
        self.write_manifests("v2")
        self.command("git", "init", "-q")
        self.command("git", "config", "user.name", "Report test")
        self.command("git", "config", "user.email", "report-test@example.invalid")
        self.baseline = self.commit()
        self.live = self.original.replace(":= n = n.", ":= canonical n.")
        self.write(self.source, self.live)
        self.cert_source = (
            "From GTBase Require Import common.\n"
            "From GTBase.conjectures Require Import X0.\n"
            "Module Legacy.\n"
            "Definition local_helper (n : nat) : Prop := n = n.\n"
            "End Legacy.\n"
            "Module X0Legacy.\n"
            "Definition statement : Prop := forall n, Legacy.local_helper n.\n"
            "End X0Legacy.\n"
            "Lemma helper_compat (n : nat) : Legacy.local_helper n <-> local_helper n.\n"
            "Proof. split; trivial. Qed.\n"
            "Lemma statement_compat : X0Legacy.statement <-> test_statement.\n"
            "Proof. split; intros h n; apply h. Qed.\n"
        )
        self.write(self.certificate, self.cert_source)
        self.spec = {
            "family": "test-family", "report_name": "test_family", "baseline_commit": self.baseline,
            "canonical_name": "GTBase.common.canonical", "canonical_short_name": "canonical",
            "relation": "logical equivalence", "namespaces": {"base": "GTBase"},
            "certificate_files": [self.certificate, "base/theories/common.v"],
            "frozen": [
                {"kind": "source", "qualified": self.helper, "path": self.source,
                 "name": "local_helper", "frozen_path": self.certificate,
                 "frozen": "Legacy.local_helper", "certificate": self.module + ".helper_compat",
                 "live_unfolds_to": "canonical n"},
                {"kind": "statement", "qualified": self.statement, "path": self.source,
                 "name": "test_statement", "frozen_path": self.certificate,
                 "frozen": "X0Legacy.statement", "certificate": self.module + ".statement_compat",
                 "substitutions": {"test_statement": "statement", "local_helper": "Legacy.local_helper"}},
            ],
        }

    def write(self, path, value):
        dest = self.root / path
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(value)

    def write_json(self, path, value):
        self.write(path, json.dumps(value))

    def command(self, *args):
        result = subprocess.run(args, cwd=self.root, text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result.stdout.strip()

    def commit(self):
        self.command("git", "add", ".")
        self.command("git", "commit", "-qm", "fixture")
        return self.command("git", "rev-parse", "HEAD")

    def write_manifests(self, corpus):
        for name, paths in REPORT.REG.CORPORA.items():
            self.write_json("meta/" + paths["manifest"], {"rows": [self.row] if name == corpus else []})
            self.write_json("meta/" + paths["overlay"], {"entries": {"test": {"statement": "done"}}
                                                        if name == corpus else {}})

    def report(self):
        return REPORT.build_report(copy.deepcopy(self.spec))

    def failures(self):
        return [item["check"] for item in self.report()["checks"] if not item["ok"]]

    def rebaseline(self):
        self.write(self.source, self.original)
        # The certificate exists only after migration, as in the real corpus.
        certificate_text = (self.root / self.certificate).read_text()
        (self.root / self.certificate).unlink()
        self.spec["baseline_commit"] = self.commit()
        self.write(self.source, self.live)
        self.write(self.certificate, certificate_text)

    def test_complete_family_passes(self):
        self.assertEqual(self.failures(), [])

    def test_omitted_statement_is_rejected(self):
        self.spec["frozen"] = self.spec["frozen"][:1]
        self.assertIn("affected statement coverage matches baseline dependencies", self.failures())

    def test_omitted_source_is_rejected(self):
        self.spec["frozen"] = self.spec["frozen"][1:]
        self.assertIn("migrated source coverage matches the registry", self.failures())

    def test_unrelated_registered_certificate_is_rejected(self):
        self.spec["frozen"][1]["certificate"] = "GTBase.common.unrelated"
        self.assertIn(self.statement + ": certificate text names its frozen and live endpoints", self.failures())

    def test_qualified_live_reference_in_frozen_snapshot_is_rejected(self):
        self.write(self.certificate, self.cert_source + "Module OtherLegacy.\n"
                   "Definition bad : Prop := GTBase.conjectures.X0.local_helper 0.\nEnd OtherLegacy.\n")
        self.assertTrue(any("OtherLegacy.bad resolves through live" in error for error in self.failures()))

    def test_qualified_cross_module_statement_is_discovered(self):
        self.write("base/theories/conjectures/X1.v",
                   "Definition cross_statement : Prop := GTBase.conjectures.X0.local_helper 0.\n")
        project = self.root / "base/_CoqProject"
        project.write_text(project.read_text() + "theories/conjectures/X1.v\n")
        self.rebaseline()
        self.assertIn("affected statement coverage matches baseline dependencies", self.failures())

    def test_record_and_inductive_dependency_bodies_are_discovered(self):
        scaffolds = (
            "Record Wrapper := Build_Wrapper { number : nat; premise : local_helper number }.\n",
            "Inductive Wrapper : Type := Wrap : forall n, local_helper n -> Wrapper.\n",
        )
        for scaffold in scaffolds:
            with self.subTest(scaffold=scaffold):
                self.original = (
                    "From GTBase Require Import common.\n"
                    "Definition local_helper (n : nat) : Prop := n = n.\n" + scaffold +
                    "Definition test_statement : Prop := forall w : Wrapper, True.\n")
                self.live = self.original.replace(":= n = n.", ":= canonical n.")
                self.rebaseline()
                rows, _ = REPORT.manifest_rows(self.spec["baseline_commit"])
                affected = REPORT.affected_statements(self.spec["baseline_commit"], {self.helper}, rows)
                self.assertIn(self.statement, affected)

    def test_opg_row_and_overlay_are_supported(self):
        self.write_manifests("opg")
        self.rebaseline()
        self.spec["frozen"][1]["corpus"] = "opg"
        self.assertEqual(self.failures(), [])
        self.write_json("meta/opg_legs_state.json", {"entries": {"test": {"statement": "blocked"}}})
        self.assertIn("test_statement: leg-state entry unchanged since baseline", self.failures())

    def test_non_corpus_requires_explicit_marker(self):
        self.write_manifests(None)
        self.rebaseline()
        self.assertIn("test_statement: manifest row unchanged since baseline", self.failures())
        self.spec["frozen"][1]["non_corpus"] = True
        self.assertEqual(self.failures(), [])

    def test_non_corpus_cannot_hide_existing_row(self):
        self.spec["frozen"][1]["non_corpus"] = True
        self.assertIn("test_statement: explicitly non-corpus statement has no manifest row", self.failures())

    def test_corpus_selector_must_name_a_supported_corpus(self):
        for selector in ("", None, False, 0, [], {}, "other"):
            with self.subTest(selector=selector):
                self.spec["frozen"][1]["corpus"] = selector
                self.assertIn("test_statement: corpus selection is valid", self.failures())
        self.spec["frozen"][1]["corpus"] = "v2"
        self.assertEqual(self.failures(), [])

    def test_non_corpus_cannot_also_select_a_corpus(self):
        self.write_manifests(None)
        self.rebaseline()
        self.spec["frozen"][1]["non_corpus"] = True
        for selector in (None, "", "v2", "opg"):
            with self.subTest(selector=selector):
                self.spec["frozen"][1]["corpus"] = selector
                self.assertIn("test_statement: corpus selection is valid", self.failures())

    def test_missing_history_is_fatal(self):
        self.spec["baseline_commit"] = "0" * 40
        with self.assertRaises(subprocess.CalledProcessError):
            self.report()

    def test_all_check_detects_report_drift(self):
        self.write_json("meta/migration_reports/test_family.spec.json", self.spec)
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(REPORT.main(["--all", "--write"]), 0)
            self.assertFalse((REPORT.REPORTS / "test_family.json").exists())
            self.assertEqual(REPORT.main(["--all", "--check"]), 0)
            self.write("meta/migration_reports/test_family.md", "stale\n")
            self.assertEqual(REPORT.main(["--all", "--check"]), 1)

    def test_only_write_bootstraps_a_registered_report(self):
        spec_path = "meta/migration_reports/test_family.spec.json"
        report_path = "meta/migration_reports/test_family.md"
        self.write_json(spec_path, self.spec)
        entry = self.registry["primitives"]["test-family"]
        entry.update(migration_spec=spec_path, migration_report=report_path)
        self.write_json("meta/library_primitives/test-family.json", {
            "schema_version": 1, "family": "test-family", "primitive": entry,
        })
        report = self.root / report_path
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            for selector in ("test_family", "--all"):
                with self.subTest(selector=selector):
                    for mode in ([], ["--check"], ["--details", str(self.root / "details")]):
                        self.assertEqual(REPORT.main([selector, *mode]), 1)
                        self.assertFalse(report.exists())
                    self.assertEqual(REPORT.main([selector, "--write"]), 0)
                    self.assertTrue(report.is_file())
                    self.assertEqual(REPORT.main([selector, "--check"]), 0)
                    report.unlink()
            (self.root / spec_path).unlink()
            self.assertEqual(REPORT.main(["test_family", "--write"]), 1)
            self.assertFalse(report.exists())

    def test_details_are_deterministic_and_independent_of_compact_check(self):
        self.write_json("meta/migration_reports/test_family.spec.json", self.spec)
        details = self.root / "on-demand-details"
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(REPORT.main(["--all", "--write", "--details", str(details)]), 0)
            before = {path.name: path.read_bytes() for path in details.iterdir()}
            self.assertEqual(REPORT.main(["--all", "--check", "--details", str(details)]), 0)
            self.assertEqual(before, {path.name: path.read_bytes() for path in details.iterdir()})
            (details / "test_family.json").write_text("untracked details may be discarded\n")
            self.assertEqual(REPORT.main(["--all", "--check"]), 0)

    def test_all_check_rejects_verbose_json_but_allows_specs_and_docs(self):
        self.write_json("meta/migration_reports/test_family.spec.json", self.spec)
        self.write("meta/migration_reports/README.md", "Report documentation.\n")
        self.write("meta/migration_reports/docs/format.txt", "Format documentation.\n")
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(REPORT.main(["--all", "--write"]), 0)
            self.assertEqual(REPORT.main(["--all", "--check"]), 0)
            for name in ("test_family.json", "details/test_family.json"):
                with self.subTest(name=name):
                    path = REPORT.REPORTS / name
                    self.write_json(str(path.relative_to(self.root)), {"frozen": [], "checks": []})
                    errors = io.StringIO()
                    with contextlib.redirect_stderr(errors):
                        self.assertEqual(REPORT.main(["--all", "--check"]), 1)
                    self.assertIn("unexpected non-specification JSON", errors.getvalue())
                    self.assertIn(name, errors.getvalue())
                    path.unlink()
            self.assertEqual(REPORT.main(["--all", "--check"]), 0)

    def test_details_cannot_write_inside_report_tree_even_through_symlinks(self):
        self.write_json("meta/migration_reports/test_family.spec.json", self.spec)
        alias = self.root / "report-alias"
        alias.symlink_to(REPORT.REPORTS, target_is_directory=True)
        destinations = (REPORT.REPORTS, REPORT.REPORTS / "details" / "nested",
                        alias, alias / "details")
        for destination in destinations:
            for selector in ("test_family", "--all"):
                with self.subTest(destination=destination, selector=selector):
                    errors = io.StringIO()
                    with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(errors):
                        self.assertEqual(REPORT.main([
                            selector, "--write", "--details", str(destination)]), 1)
                    self.assertIn("outside the report directory and its descendants", errors.getvalue())
                    self.assertFalse((REPORT.REPORTS / "test_family.md").exists())
                    self.assertFalse((destination / "test_family.json").exists())
        self.assertFalse((REPORT.REPORTS / "details").exists())

    def compile_fixture(self):
        for relative in ("theories/common.v", "theories/conjectures/X0.v", "theories/migration/test_family.v"):
            result = subprocess.run(["coqc", "-Q", "theories", "GTBase", relative],
                                    cwd=self.root / "base", env=REPORT.ROCQ.environment(),
                                    text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    @unittest.skipUnless(KERNEL, "use --kernel for tiny compiled probes")
    def test_kernel_accepts_exact_statement_type(self):
        self.compile_fixture()
        self.assertEqual(REPORT.check_kernel(self.spec), [])

    @unittest.skipUnless(KERNEL, "use --kernel for tiny compiled probes")
    def test_kernel_rejects_extra_false_guard_even_when_closed(self):
        bad = self.cert_source.replace(
            "Lemma statement_compat : X0Legacy.statement <-> test_statement.\n"
            "Proof. split; intros h n; apply h. Qed.",
            "Lemma statement_compat : False -> (X0Legacy.statement <-> test_statement).\n"
            "Proof. intros h; destruct h. Qed.")
        self.write(self.certificate, bad)
        self.assertEqual(self.failures(), [], "Text-only mode must not claim a type proof")
        self.compile_fixture()
        self.assertTrue(REPORT.check_kernel(self.spec))


class RepositorySourceTests(unittest.TestCase):
    """A real public source -> foundation intermediary -> two corpus rows."""

    write = ReportTests.write
    write_json = ReportTests.write_json
    command = ReportTests.command
    commit = ReportTests.commit
    report = ReportTests.report
    failures = ReportTests.failures

    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="repository-source-test-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        for module, name, value in ((REPORT, "ROOT", self.root),
                                    (REPORT, "REPORTS", self.root / "meta/migration_reports"),
                                    (REPORT.INV, "ROOT", self.root)):
            patcher = patch.object(module, name, value)
            patcher.start()
            self.addCleanup(patcher.stop)
        self.source = "base/theories/original.v"
        self.helper = "GTBase.original.local_helper"
        self.middle_path = "chromatic-theory/theories/foundations/intermediary.v"
        self.middle = "Chromatic.foundations.intermediary.middle"
        self.certificate = "spectral-graph-theory/theories/migration/test_family.v"
        self.module = "Spectral.migration.test_family"
        self.original = "Definition local_helper (n : nat) : Prop := n = n.\n"
        self.write(self.source, self.original)
        self.write("base/theories/common.v", "Definition canonical (n : nat) : Prop := n = n.\n")
        self.write(self.middle_path, "From GTBase Require Import original.\n"
                   "Definition middle (n : nat) : Prop := original.local_helper n.\n")
        self.rows = []
        self.statements = []
        for index in (0, 1):
            name = f"test{index}_statement"
            package, namespace = (("chromatic-theory", "Chromatic") if index == 0
                                  else ("spectral-graph-theory", "Spectral"))
            path = f"{package}/theories/conjectures/X{index}.v"
            qualified = f"{namespace}.conjectures.X{index}.{name}"
            self.write(path, "From Chromatic.foundations Require Import intermediary.\n"
                       f"(** Corpus row: test{index}\n    English statement: reflexivity. *)\n"
                       f"Definition {name} : Prop := forall n, intermediary.middle n.\n")
            self.rows.append({"formal_name": name, "repo": package,
                              "slug": f"test{index}", "row_id": f"test:{index}",
                              "phase": f"X{index}", "status": "open",
                              "legs": {"statement": "done"}})
            self.statements.append({"kind": "statement", "qualified": qualified,
                "path": path, "name": name, "frozen_path": self.certificate,
                "frozen": f"Legacy.{name}", "certificate": self.module + f".statement{index}_compat",
                "substitutions": {"intermediary.middle": "Legacy.middle"}})
        self.write("base/_CoqProject", "-Q theories GTBase\ntheories/common.v\ntheories/original.v\n")
        self.write("chromatic-theory/_CoqProject", "-Q theories Chromatic\n-Q ../base/theories GTBase\n"
                   "theories/foundations/intermediary.v\ntheories/conjectures/X0.v\n")
        self.write("spectral-graph-theory/_CoqProject", "-Q theories Spectral\n-Q ../base/theories GTBase\n"
                   "-Q ../chromatic-theory/theories Chromatic\n"
                   "theories/conjectures/X1.v\ntheories/migration/test_family.v\n")
        for corpus, paths in REPORT.REG.CORPORA.items():
            self.write_json("meta/" + paths["manifest"], {"rows": self.rows if corpus == "v2" else []})
            self.write_json("meta/" + paths["overlay"], {"entries": {
                row["slug"]: {"statement": "done"} for row in self.rows} if corpus == "v2" else {}})
        self.write_json("meta/library_helper_inventory.json", {"helpers": []})
        self.command("git", "init", "-q")
        self.command("git", "config", "user.name", "Source test")
        self.command("git", "config", "user.email", "source-test@example.invalid")
        self.baseline = self.commit()
        self.pin = {"path": self.source, "commit": self.baseline,
                    "blob": self.command("git", "rev-parse", self.baseline + ":" + self.source),
                    "declaration_hash": REPORT.sha256(REPORT.find_decl(self.original, "local_helper")["text"])}
        self.primitive = {"canonical_name": "GTBase.common.canonical", "owner": "base",
            "status": "migrating", "fidelity": "FAITHFUL", "normalized_names": ["local_helper"],
            "consumers_remaining": 0, "upstream_audit": {
                "searched_modules": ["fixture"], "result": "fixture", "note": "fixture", "audited_at": "fixture"},
            "source_definitions": [self.helper], "repository_sources": {self.helper: self.pin},
            "compatibility_theorems": [self.module + "." + name for name in
                ("helper_compat", "middle_compat", "statement0_compat", "statement1_compat")],
            "api_theorems": []}
        self.write_registry()
        self.write(self.source, "From GTBase Require Import common.\n"
                   "Definition local_helper (n : nat) : Prop := canonical n.\n")
        self.cert_source = (
            "From GTBase Require Import original.\n"
            "From Chromatic.foundations Require Import intermediary.\n"
            "From Chromatic.conjectures Require Import X0.\n"
            "From Spectral.conjectures Require Import X1.\n"
            "Module Legacy.\n"
            "Definition local_helper (n : nat) : Prop := n = n.\n"
            "Definition middle (n : nat) : Prop := Legacy.local_helper n.\n"
            "Definition test0_statement : Prop := forall n, Legacy.middle n.\n"
            "Definition test1_statement : Prop := forall n, Legacy.middle n.\n"
            "End Legacy.\n"
            "Lemma helper_compat n : Legacy.local_helper n <-> GTBase.original.local_helper n.\n"
            "Proof. split; trivial. Qed.\n"
            "Lemma middle_compat n : Legacy.middle n <-> Chromatic.foundations.intermediary.middle n.\n"
            "Proof. split; trivial. Qed.\n"
            "Lemma statement0_compat : Legacy.test0_statement <-> Chromatic.conjectures.X0.test0_statement.\n"
            "Proof. split; intros h n; apply h. Qed.\n"
            "Lemma statement1_compat : Legacy.test1_statement <-> Spectral.conjectures.X1.test1_statement.\n"
            "Proof. split; intros h n; apply h. Qed.\n")
        self.write(self.certificate, self.cert_source)
        self.spec = {"family": "test-family", "report_name": "test_family",
            "baseline_commit": self.baseline, "canonical_name": "GTBase.common.canonical",
            "canonical_short_name": "canonical", "relation": "logical equivalence",
            "namespaces": {"base": "GTBase", "chromatic-theory": "Chromatic", "spectral-graph-theory": "Spectral"},
            "cross_module_consumers": [{"path": self.middle_path, "name": "local_helper"},
                *({"path": obj["path"], "name": "middle"} for obj in self.statements)],
            "certificate_files": [self.certificate], "frozen": [
                {"kind": "source", "qualified": self.helper, "path": self.source,
                 "name": "local_helper", "frozen_path": self.certificate,
                 "frozen": "Legacy.local_helper", "certificate": self.module + ".helper_compat",
                 "live_unfolds_to": "canonical n"},
                {"kind": "chain", "qualified": self.middle, "path": self.middle_path,
                 "name": "middle", "frozen_path": self.certificate,
                 "frozen": "Legacy.middle", "certificate": self.module + ".middle_compat",
                 "substitutions": {"original.local_helper": "Legacy.local_helper"}},
                *self.statements]}

    def write_registry(self):
        self.write_json("meta/library_primitives/test-family.json", {
            "schema_version": 1, "family": "test-family", "primitive": self.primitive})

    def records(self):
        return REPORT.INV.repository_source_records(self.root, self.primitive)

    def test_public_source_accepts_changed_live_alias_without_inventory_enrollment(self):
        self.assertEqual(self.failures(), [])
        records = self.records()
        self.assertEqual(set(records), {self.helper})
        self.assertNotEqual(records[self.helper]["declaration_hash"], self.pin["declaration_hash"])
        _, errors = REPORT.INV.validate_registry({"helpers": []})
        self.assertEqual(errors, [])
        self.assertEqual(json.loads((self.root / "meta/library_helper_inventory.json").read_text()), {"helpers": []})

    def test_missing_public_intermediary_and_each_row_are_rejected(self):
        self.assertEqual(self.failures(), [])
        original = copy.deepcopy(self.spec["frozen"])
        for obj in original[1:]:
            with self.subTest(omitted=obj["qualified"]):
                self.spec["frozen"] = [item for item in original if item != obj]
                failures = self.failures()
                expected = ("public source paths have complete frozen intermediary coverage"
                            if obj["kind"] == "chain" else "affected statement coverage matches baseline dependencies")
                self.assertIn(expected, failures)
        self.spec["frozen"] = original

    def test_source_is_not_an_optional_alternative_to_authoritative_list(self):
        self.primitive["source_definitions"] = []
        self.write_registry()
        with self.assertRaisesRegex(REPORT.RegistryError, "source_definitions"):
            self.report()

    def test_no_missing_conjecture_inventory_fallback(self):
        self.primitive.pop("repository_sources")
        self.write_registry()
        self.assertTrue(any("inventory" in failure for failure in self.failures()))
        _, errors = REPORT.INV.validate_registry({"helpers": []})
        self.assertTrue(any("missing from inventory" in error for error in errors))

    def test_immutable_blob_hash_and_declaration_hash_are_checked(self):
        for field in ("blob", "declaration_hash"):
            with self.subTest(field=field):
                before = self.pin[field]
                self.pin[field] = "0" * len(before)
                self.write_registry()
                with self.assertRaisesRegex(REPORT.RegistryError, "differs from pin"):
                    self.report()
                self.pin[field] = before

    def test_pin_must_be_commit_not_blob(self):
        self.pin["commit"] = self.pin["blob"]
        with self.assertRaisesRegex(REPORT.RegistryError, "not a commit"):
            self.records()

    def test_report_cannot_use_another_original_commit(self):
        other = self.commit()
        self.spec["frozen"][0]["commit"] = other
        self.assertIn(self.helper + ": repository source baseline agrees with pin", self.failures())

    def test_current_definition_and_build_ownership_are_required(self):
        for path, replacement, message in (
            (self.source, "Definition missing := True.\n", "one top-level Definition"),
            (self.source, "Module Nested.\n" + self.original + "End Nested.\n", "nested-module"),
            (self.source, "Module Hidden <: Sig.\n" + self.original + "End Hidden.\n", "nested-module"),
            (self.source, "Module Hidden (X : Sig).\n" + self.original + "End Hidden.\n", "nested-module"),
            (self.source, "Module Hidden <: Sig with Definition t := nat.\n" + self.original + "End Hidden.\n", "nested-module"),
            (self.source, "Local " + self.original, "one top-level Definition"),
            ("base/_CoqProject", "-Q theories GTBase\ntheories/common.v\n", "not build-listed"),
            ("base/_CoqProject", "-Q theories Wrong\ntheories/original.v\n", "namespace ownership"),
            ("base/_CoqProject", "-Q theories GTBase\n-Q theories Alias\ntheories/original.v\n", "namespace ownership")):
            with self.subTest(path=path, replacement=replacement):
                before = (self.root / path).read_text()
                self.write(path, replacement)
                with self.assertRaisesRegex(REPORT.RegistryError, message):
                    self.records()
                self.write(path, before)

    def test_hidden_compiler_namespace_overrides_are_rejected(self):
        project = (self.root / 'base/_CoqProject').read_text()
        for option in ('-arg -Q', '-arg "-Q theories Hidden"', '-arg "-Q=theories"',
                       '-arg "-top Hidden"', '-arg -top=Hidden', 'COQFLAGS=-top',
                       f'-Q {self.root}/base/theories Hidden'):
            with self.subTest(option=option):
                self.write('base/_CoqProject', project + option + '\n')
                with self.assertRaisesRegex(REPORT.RegistryError, 'unsupported (absolute )?project'):
                    self.records()

    def test_public_section_definition_is_supported(self):
        self.write(self.source, 'Section Public.\n' + self.original + 'End Public.\n')
        self.assertEqual(set(self.records()), {self.helper})

    def test_ordinary_normalized_family_completeness_is_preserved(self):
        _, errors = REPORT.INV.validate_registry({'helpers': []})
        self.assertEqual(errors, [])
        extra = {'qualified_name': 'Chromatic.conjectures.X2.x2_local_helper',
                 'normalized_name': 'local_helper', 'direct_consumers': []}
        _, errors = REPORT.INV.validate_registry({'helpers': [extra]})
        self.assertTrue(any('source_definitions drift' in error for error in errors))

    def test_inventory_entries_cannot_be_reclassified_as_repository_sources(self):
        extra = {'qualified_name': self.helper, 'normalized_name': 'local_helper',
                 'direct_consumers': []}
        _, errors = REPORT.INV.validate_registry({'helpers': [extra]})
        self.assertTrue(any('already a conjecture inventory source' in error for error in errors))

    def test_public_source_missing_from_baseline_graph_is_fatal(self):
        with self.assertRaisesRegex(REPORT.RegistryError, 'missing from baseline dependency index'):
            REPORT.statement_dependencies(self.baseline, {self.helper + '_missing'}, {}, include_public=True)

    def test_foundation_row_cannot_be_hidden_as_non_corpus(self):
        self.spec['frozen'][-1]['non_corpus'] = True
        self.assertIn('test1_statement: explicitly non-corpus statement has no manifest row', self.failures())

    def test_original_build_membership_is_required(self):
        self.write("base/_CoqProject", "-Q theories GTBase\ntheories/common.v\n")
        self.write(self.source, self.original)
        self.pin["commit"] = self.commit()
        self.write("base/_CoqProject", "-Q theories GTBase\ntheories/common.v\ntheories/original.v\n")
        with self.assertRaisesRegex(REPORT.RegistryError, "not build-listed"):
            self.records()

    def test_current_source_and_project_aliases_are_rejected(self):
        for relative in (self.source, "base/_CoqProject"):
            with self.subTest(relative=relative):
                path = self.root / relative
                text = path.read_text()
                target = path.with_name(path.name + ".real")
                path.rename(target)
                path.symlink_to(target)
                with self.assertRaisesRegex(REPORT.RegistryError, "aliased"):
                    self.records()
                path.unlink()
                target.rename(path)
                self.assertEqual(path.read_text(), text)

    def test_pinned_symlink_blob_is_rejected(self):
        path = self.root / self.source
        path.unlink()
        path.symlink_to("common.v")
        self.pin["commit"] = self.commit()
        path.unlink()
        path.write_text(self.original)
        with self.assertRaisesRegex(REPORT.RegistryError, "regular"):
            self.records()

    def test_ordinary_row_status_and_frozen_body_guards_still_apply(self):
        self.assertEqual(self.failures(), [])
        self.write(self.certificate, self.cert_source.replace("n = n.", "False."))
        self.assertTrue(any("frozen copy Legacy.local_helper" in failure for failure in self.failures()))
        self.write(self.certificate, self.cert_source)
        paths = REPORT.REG.CORPORA["v2"]
        self.rows[0]["status"] = "changed"
        self.write_json("meta/" + paths["manifest"], {"rows": self.rows})
        self.assertIn("test0_statement: manifest row unchanged since baseline", self.failures())

    def compile_fixture(self):
        for package in ("base", "chromatic-theory", "spectral-graph-theory"):
            for args in (("rocq", "makefile", "-f", "_CoqProject", "-o", "Makefile.coq"),
                         ("make", "-f", "Makefile.coq", "-j1")):
                proc = subprocess.run(args, cwd=self.root / package, env=REPORT.ROCQ.environment(),
                                      text=True, capture_output=True)
                self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)

    @unittest.skipUnless(KERNEL, "use --kernel for tiny compiled probes")
    def test_kernel_checks_public_source_and_both_transitive_rows(self):
        self.compile_fixture()
        self.assertEqual(REPORT.check_kernel(self.spec), [])

    @unittest.skipUnless(KERNEL, "use --kernel for tiny compiled probes")
    def test_kernel_rejects_extra_guard_on_foundation_dependent_row(self):
        before = ("Lemma statement1_compat : Legacy.test1_statement <-> Spectral.conjectures.X1.test1_statement.\n"
                  "Proof. split; intros h n; apply h. Qed.")
        after = ("Lemma statement1_compat : False -> (Legacy.test1_statement <-> Spectral.conjectures.X1.test1_statement).\n"
                 "Proof. intros h; destruct h. Qed.")
        self.write(self.certificate, self.cert_source.replace(before, after))
        self.assertEqual(self.failures(), [])
        self.compile_fixture()
        self.assertTrue(REPORT.check_kernel(self.spec))


if __name__ == "__main__":
    unittest.main(verbosity=2)

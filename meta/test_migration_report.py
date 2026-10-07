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
import os
import shutil
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

    def distinct_variant_fixture(self):
        declaration = "\nDefinition distinct_helper : nat := 7.\n"
        self.original += declaration
        self.live += declaration
        self.rebaseline()
        self.spec["distinct_variants"] = [{
            "qualified": "GTBase.conjectures.X0.distinct_helper",
            "path": self.source, "name": "distinct_helper",
        }]

    def test_details_distinct_variant_without_optional_note(self):
        self.distinct_variant_fixture()
        report = self.report()
        self.assertTrue(report["ok"])
        before = copy.deepcopy(report)
        item = report["distinct_variants"][0]
        expected = (f"- `{item['qualified']}` "
                    f"(sha256 `{item['declaration_sha256'][:16]}…`, unchanged)")
        self.assertIn(expected + "\n", REPORT.render_details(report, self.spec))
        self.assertEqual(report, before)

    def test_details_preserves_present_note_including_empty(self):
        self.distinct_variant_fixture()
        for note in ("Different contract; retained unchanged.", ""):
            with self.subTest(note=note):
                self.spec["distinct_variants"][0]["note"] = note
                report = self.report()
                self.assertTrue(report["ok"])
                item = report["distinct_variants"][0]
                expected = (f"- `{item['qualified']}` "
                            f"(sha256 `{item['declaration_sha256'][:16]}…`, "
                            f"unchanged): {note}\n")
                self.assertIn(expected, REPORT.render_details(report, self.spec))

    def test_optional_note_does_not_make_required_identity_optional(self):
        self.distinct_variant_fixture()
        original = copy.deepcopy(self.spec["distinct_variants"][0])
        for key in ("qualified", "path", "name"):
            with self.subTest(key=key):
                self.spec["distinct_variants"][0] = copy.deepcopy(original)
                del self.spec["distinct_variants"][0][key]
                with self.assertRaises(KeyError):
                    self.report()
        self.spec["distinct_variants"][0] = original
        report = self.report()
        del report["distinct_variants"][0]["declaration_sha256"]
        with self.assertRaises(KeyError):
            REPORT.render_details(report, self.spec)

    def test_noteless_distinct_variant_still_requires_unchanged_source(self):
        self.distinct_variant_fixture()
        self.write(self.source, self.live.replace(
            "Definition distinct_helper : nat := 7.",
            "Definition distinct_helper : nat := 8."))
        self.assertIn("distinct variant GTBase.conjectures.X0.distinct_helper unchanged",
                      self.failures())


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


class FrozenRoleTests(unittest.TestCase):
    """A primary row must not hide a mislabeled additional complete Original."""

    setUp = ReportTests.setUp
    write = ReportTests.write
    write_json = ReportTests.write_json
    command = ReportTests.command
    commit = ReportTests.commit
    write_manifests = ReportTests.write_manifests
    report = ReportTests.report
    failures = ReportTests.failures
    rebaseline = ReportTests.rebaseline
    compile_fixture = ReportTests.compile_fixture

    def register(self, name):
        self.registry["primitives"]["test-family"]["compatibility_theorems"].append(
            self.module + "." + name)
        self.write_json("meta/library_primitives/test-family.json", {
            "schema_version": 1, "family": "test-family",
            "primitive": self.registry["primitives"]["test-family"],
        })

    def add_original(self, guarded=False, *, module="X0Original", certificate="original_compat"):
        obj = copy.deepcopy(self.spec["frozen"][1])
        obj.update(kind="original-statement", frozen=module + ".statement",
                   certificate=self.module + "." + certificate)
        self.spec["frozen"].append(obj)
        guard = "False -> " if guarded else ""
        proof = "intros h; destruct h" if guarded else "split; intros h n; apply h"
        self.cert_source += (
            f"Module {module}.\n"
            "Definition statement : Prop := forall n, Legacy.local_helper n.\n"
            f"End {module}.\n"
            f"Lemma {certificate} : {guard}({module}.statement <-> test_statement).\n"
            f"Proof. {proof}. Qed.\n")
        self.write(self.certificate, self.cert_source)
        self.register(certificate)
        return obj

    def assert_role_rejected(self, obj):
        self.assertTrue(any("complete statement requires" in error for error in self.failures()))
        objects, errors = REPORT.statement_obligations(self.spec)
        self.assertIn(obj, objects, "The full Original remains a required obligation")
        self.assertTrue(errors)
        with patch.object(REPORT.ROCQ, "environment", side_effect=AssertionError("must reject before Rocq")):
            self.assertTrue(REPORT.check_kernel(self.spec))

    def test_unknown_missing_and_nonstring_kinds_fail_both_entries(self):
        obj = self.add_original(guarded=True)
        for kind in (None, False, 1, [], {}, "original", "future-frozen"):
            with self.subTest(kind=kind):
                obj["kind"] = kind
                with self.assertRaisesRegex(ValueError, "unsupported kind"):
                    self.report()
                self.assertIn("unsupported kind", " ".join(REPORT.check_kernel(self.spec)))
        del obj["kind"]
        with self.assertRaisesRegex(ValueError, "unsupported kind"):
            self.report()
        self.assertIn("unsupported kind", " ".join(REPORT.check_kernel(self.spec)))

    def test_known_nonstatement_roles_cannot_hide_an_original(self):
        obj = self.add_original(guarded=True)
        for kind in ("chain", "original-chain", *sorted(REPORT.HISTORICAL_KINDS)):
            with self.subTest(kind=kind):
                obj["kind"] = kind
                self.assert_role_rejected(obj)

    def test_corpus_claims_cannot_hide_the_original_identity(self):
        obj = self.add_original(guarded=True)
        obj["kind"] = "historical"
        for claim in ({"corpus": "opg"}, {"corpus": "other"},
                      {"corpus": []}, {"non_corpus": True},
                      {"corpus": "opg", "non_corpus": True}):
            with self.subTest(claim=claim):
                obj.pop("corpus", None)
                obj.pop("non_corpus", None)
                obj.update(claim)
                self.assert_role_rejected(obj)

    def test_direct_kernel_also_validates_statement_corpus_selection(self):
        obj = self.add_original()
        for claim in ({"corpus": "opg"}, {"corpus": "other"},
                      {"non_corpus": True}, {"non_corpus": "yes"}):
            with self.subTest(claim=claim):
                obj.pop("corpus", None)
                obj.pop("non_corpus", None)
                obj.update(claim)
                self.assertTrue(self.failures())
                with patch.object(REPORT.ROCQ, "environment", side_effect=AssertionError("metadata rejected")):
                    self.assertTrue(REPORT.check_kernel(self.spec))

    def test_noncorpus_discovery_does_not_trust_the_original_marker(self):
        obj = self.add_original(guarded=True)
        self.write_manifests(None)
        self.rebaseline()
        self.spec["frozen"][1]["non_corpus"] = True
        for kind in ("chain", "original-chain", "historical", "a5-frozen"):
            for claim in ({}, {"non_corpus": True}, {"non_corpus": False}, {"corpus": "v2"}):
                with self.subTest(kind=kind, claim=claim):
                    obj["kind"] = kind
                    obj.pop("corpus", None)
                    obj.pop("non_corpus", None)
                    obj.update(claim)
                    self.assert_role_rejected(obj)

    def test_parameterized_prop_helpers_accept_all_historical_roles(self):
        for kind in sorted(REPORT.HISTORICAL_KINDS):
            with self.subTest(kind=kind):
                obj = copy.deepcopy(self.spec["frozen"][0])
                obj["kind"] = kind
                self.spec["frozen"].append(obj)
                self.assertEqual(self.failures(), [])
                objects, errors = REPORT.statement_obligations(self.spec)
                self.assertEqual(errors, [])
                self.assertNotIn(obj, objects)
                self.spec["frozen"].pop()

    def test_m1_frozen_keeps_its_existing_registration_exception(self):
        obj = copy.deepcopy(self.spec["frozen"][0])
        obj.update(kind="m1-frozen", certificate=None)
        self.spec["frozen"].append(obj)
        self.assertEqual(self.failures(), [])
        obj["kind"] = "historical"
        self.assertIn(self.helper + ": certificate is registered", self.failures())

    def add_historical_scaffolding(self):
        imports = "From mathcomp Require Import all_boot.\nFrom GraphTheory Require Import digraph sgraph.\n"
        declarations = (
            "Record Box := Build_Box { value : nat }.\n"
            "Definition edge0 : rel bool := fun _ _ => false.\n"
            "Lemma edge0_sym : symmetric edge0. Proof. by []. Qed.\n"
            "Lemma edge0_irrefl : irreflexive edge0. Proof. by []. Qed.\n")
        self.original = imports + self.original + declarations
        self.live = self.original.replace(":= n = n.", ":= canonical n.")
        self.cert_source = imports + self.cert_source.replace("End Legacy.\n", declarations + "End Legacy.\n")
        self.cert_source += (
            "Lemma box_compat : (exists _ : Legacy.Box, True) <-> (exists _ : Box, True).\n"
            "Proof. split; intros _; [exists (Build_Box 0)|exists (Legacy.Build_Box 0)]; exact I. Qed.\n"
            "Lemma edge0_compat : Legacy.edge0 = edge0. Proof. by []. Qed.\n"
            "Lemma graph_compat : SGraph Legacy.edge0_sym Legacy.edge0_irrefl "
            "≃ SGraph edge0_sym edge0_irrefl.\n"
            "Proof. by apply: eq_diso => x y. Qed.\n")
        self.write(self.certificate, self.cert_source)
        for name, certificate in (("Box", "box_compat"), ("edge0", "edge0_compat"),
                                  ("edge0_sym", "graph_compat"), ("edge0_irrefl", "graph_compat")):
            self.spec["frozen"].append({
                "kind": "historical", "qualified": "GTBase.conjectures.X0." + name,
                "path": self.source, "name": name, "frozen_path": self.certificate,
                "frozen": "Legacy." + name, "certificate": self.module + "." + certificate,
            })
        for name in ("box_compat", "edge0_compat", "graph_compat"):
            self.register(name)
        self.rebaseline()

    def test_record_and_opaque_graph_scaffolding_are_not_statement_objects(self):
        self.add_historical_scaffolding()
        self.assertEqual(self.failures(), [])
        objects, errors = REPORT.statement_obligations(self.spec)
        self.assertEqual(errors, [])
        self.assertEqual([obj["kind"] for obj in objects], ["statement"])

    @unittest.skipUnless(KERNEL, "use --kernel for tiny compiled probes")
    def test_kernel_rejects_guarded_original_with_primary_row_present(self):
        self.add_original()
        obj = self.add_original(guarded=True, module="SecondOriginal", certificate="second_original_compat")
        self.assertEqual(self.failures(), [], "Text-only mode must not claim a type proof")
        self.compile_fixture()
        self.assertTrue(any("exact-type/assumptions probe failed" in error
                            for error in REPORT.check_kernel(self.spec)))
        for kind in ("chain", "original-chain", "historical", "a5-frozen"):
            obj["kind"] = kind
            self.assert_role_rejected(obj)

    @unittest.skipUnless(KERNEL, "use --kernel for tiny compiled probes")
    def test_kernel_accepts_genuine_original_and_explicit_noncorpus_original(self):
        self.add_original()
        self.add_original(module="SecondOriginal", certificate="second_original_compat")
        self.assertEqual(self.failures(), [])
        self.compile_fixture()
        self.assertEqual(REPORT.check_kernel(self.spec), [])
        self.write_manifests(None)
        self.rebaseline()
        for obj in self.spec["frozen"][1:]:
            obj["non_corpus"] = True
        self.assertEqual(self.failures(), [])
        self.compile_fixture()
        self.assertEqual(REPORT.check_kernel(self.spec), [])

    @unittest.skipUnless(KERNEL, "use --kernel for tiny compiled probes")
    def test_kernel_accepts_record_and_opaque_graph_isomorphism(self):
        self.add_historical_scaffolding()
        self.compile_fixture()
        self.assertEqual(REPORT.check_kernel(self.spec), [])


class AdditionalStatementTests(unittest.TestCase):
    """A source reaches an unselected whole Prop across a separate intermediary."""

    write = ReportTests.write
    write_json = ReportTests.write_json
    command = ReportTests.command
    write_manifests = ReportTests.write_manifests
    report = ReportTests.report
    failures = ReportTests.failures
    rebaseline = ReportTests.rebaseline
    register = FrozenRoleTests.register

    def commit(self):
        self.command("git", "add", ".")
        self.command("git", "commit", "--allow-empty", "-qm", "fixture")
        return self.command("git", "rev-parse", "HEAD")

    def setUp(self):
        ReportTests.setUp(self)
        self.middle_path = "base/theories/conjectures/X1.v"
        self.extra_path = "base/theories/conjectures/X2.v"
        self.extra = "GTBase.conjectures.X2.extra_claim"
        self.middle_text = ("From GTBase.conjectures Require Import X0.\n"
                            "Definition middle (n : nat) : Prop := local_helper n.\n")
        self.extra_text = ("From GTBase.conjectures Require Import X1.\n"
                           "(** An unselected complete conjecture. *)\n"
                           "Definition extra_claim : Prop := forall n, middle n.\n")
        self.write(self.middle_path, self.middle_text)
        self.write(self.extra_path, self.extra_text)
        project = self.root / "base/_CoqProject"
        project.write_text(project.read_text() + "theories/conjectures/X1.v\n"
                           "theories/conjectures/X2.v\n")
        self.cert_source += (
            "From GTBase.conjectures Require Import X1 X2.\n"
            "Module MiddleLegacy.\n"
            "Definition middle (n : nat) : Prop := Legacy.local_helper n.\n"
            "End MiddleLegacy.\n"
            "Module ExtraLegacy.\n"
            "Definition extra_claim : Prop := forall n, MiddleLegacy.middle n.\n"
            "End ExtraLegacy.\n"
            "Lemma middle_compat (n : nat) : MiddleLegacy.middle n <-> middle n.\n"
            "Proof. split; trivial. Qed.\n"
            "Lemma extra_compat : ExtraLegacy.extra_claim <-> extra_claim.\n"
            "Proof. split; trivial. Qed.\n")
        self.write(self.certificate, self.cert_source)
        self.spec["additional_statements"] = [self.extra]
        self.spec["frozen"].extend([
            {"kind": "chain", "qualified": "GTBase.conjectures.X1.middle",
             "path": self.middle_path, "name": "middle", "frozen_path": self.certificate,
             "frozen": "MiddleLegacy.middle", "certificate": self.module + ".middle_compat",
             "substitutions": {"local_helper": "Legacy.local_helper"}},
            {"kind": "statement", "qualified": self.extra, "path": self.extra_path,
             "name": "extra_claim", "frozen_path": self.certificate,
             "frozen": "ExtraLegacy.extra_claim", "certificate": self.module + ".extra_compat",
             "non_corpus": True, "substitutions": {"middle": "MiddleLegacy.middle"}},
        ])
        self.spec["cross_module_consumers"] = [
            {"path": self.middle_path, "name": "local_helper", "note": "intermediary"},
            {"path": self.extra_path, "name": "middle", "note": "whole Prop"},
        ]
        self.register("middle_compat")
        self.register("extra_compat")
        self.rebaseline()

    def assert_invalid(self, match="additional statement"):
        with self.assertRaisesRegex(ValueError, match):
            self.report()
        # Direct kernel entry must also fail before invoking the compiler.
        with patch.object(REPORT.ROCQ, "environment", side_effect=AssertionError("metadata rejected")):
            self.assertTrue(REPORT.check_kernel(self.spec))

    def compile_fixture(self):
        for source in ("common", "conjectures/X0", "conjectures/X1", "conjectures/X2",
                       "migration/test_family"):
            proc = subprocess.run(["coqc", "-Q", "theories", "GTBase", "theories/" + source + ".v"],
                                  cwd=self.root / "base", env=REPORT.ROCQ.environment(),
                                  text=True, capture_output=True)
            self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)

    def test_explicit_reached_whole_prop_and_complete_path_pass(self):
        self.assertEqual(self.failures(), [])
        rows, _ = REPORT.manifest_rows(self.spec["baseline_commit"])
        found, path = REPORT.statement_dependencies(self.spec["baseline_commit"], {self.helper}, rows,
                                                   additional_statements={self.extra})
        self.assertEqual(found, {self.statement, self.extra})
        self.assertIn("GTBase.conjectures.X1.middle", path)

    def test_default_discovery_does_not_silently_enroll_other_props(self):
        del self.spec["additional_statements"]
        self.assertIn("affected statement coverage matches baseline dependencies", self.failures())
        self.spec["frozen"] = self.spec["frozen"][:2]
        without = self.report()
        self.spec["additional_statements"] = []
        self.assertEqual(self.report(), without)

    def test_cross_module_intermediary_cannot_be_omitted(self):
        del self.spec["frozen"][2]
        self.assertIn("additional statement paths have complete frozen intermediary coverage", self.failures())

    def test_bad_enrollment_list_is_rejected(self):
        for value in (None, "x", {}, [False], [self.extra, self.extra], ["bare"], ["GTBase.bad-name.x"]):
            with self.subTest(value=value):
                self.spec["additional_statements"] = value
                self.assert_invalid("additional_statements")

    def test_wrong_or_missing_mapping_is_rejected(self):
        original = copy.deepcopy(self.spec["frozen"][-1])
        for mutation in ({"kind": "chain"}, {"kind": "original-statement"},
                         {"non_corpus": False}, {"non_corpus": "true"}, {"corpus": "v2"},
                         {"path": self.middle_path}, {"name": "middle"}, {"certificate": None},
                         {"commit": "0" * 40}):
            with self.subTest(mutation=mutation):
                self.spec["frozen"][-1] = {**original, **mutation}
                self.assert_invalid()
        self.spec["frozen"][-1] = original
        self.spec["frozen"].append(copy.deepcopy(original))
        self.assert_invalid()
        self.spec["frozen"] = self.spec["frozen"][:-2]
        self.assert_invalid()

    def test_missing_unlisted_or_aliased_current_source_and_project_reject(self):
        for relative in (self.extra_path, "base/_CoqProject"):
            file = self.root / relative
            text = file.read_text()
            file.unlink()
            self.assert_invalid("missing or aliased")
            target = self.root / "copy"
            target.write_text(text)
            file.symlink_to(target)
            self.assert_invalid("missing or aliased")
            file.unlink()
            file.write_text(text)
        project = self.root / "base/_CoqProject"
        project.write_text(project.read_text().replace("theories/conjectures/X2.v\n", ""))
        self.assert_invalid("not build-listed")

    def test_original_source_and_ownership_must_be_present(self):
        project = self.root / "base/_CoqProject"
        original = project.read_text()
        for replacement in (original.replace("-Q theories GTBase", "-Q theories Wrong"),
                            original.replace("theories/conjectures/X2.v\n", "")):
            with self.subTest(replacement=replacement):
                project = self.root / "base/_CoqProject"
                project.write_text(replacement)
                self.rebaseline()
                self.assert_invalid("namespace ownership|not build-listed")

    def test_immutable_regular_original_and_current_declaration_are_required(self):
        target = self.root / self.extra_path
        target.write_text(self.extra_text.replace("extra_claim", "renamed"))
        self.assert_invalid("requires a nullary")
        target.write_text(self.extra_text)
        duplicate = self.root / "original-copy.v"
        duplicate.write_text(self.extra_text)
        target.unlink()
        target.symlink_to(duplicate.relative_to(target.parent) if duplicate.is_relative_to(target.parent)
                          else duplicate)
        self.rebaseline()
        target.unlink()
        target.write_text(self.extra_text)
        self.assert_invalid("expected regular source blob")

    def test_prop_shape_and_scopes_reject_helpers_and_hidden_parameters(self):
        cases = (
            "Definition extra_claim (n : nat) : Prop := middle n.\n",
            "Definition extra_claim := forall n, middle n.\n",
            "Definition extra_claim : bool := true.\n",
            "Section S.\nVariable n : nat.\nDefinition extra_claim : Prop := middle n.\nEnd S.\n",
            "Module Hidden.\nDefinition extra_claim : Prop := forall n, middle n.\nEnd Hidden.\n",
            "Module Hidden <: Sig.\nDefinition extra_claim : Prop := forall n, middle n.\nEnd Hidden.\n",
            "Module Hidden (X : Sig).\nDefinition extra_claim : Prop := forall n, middle n.\nEnd Hidden.\n",
            "Require Import Corelib.Init.Logic. Module Hidden.\nDefinition extra_claim : Prop := forall n, middle n.\nEnd Hidden.\n",
            "Require Import Corelib.Init.Logic. Section S.\nVariable n : nat.\nDefinition extra_claim : Prop := middle n.\nEnd S.\n",
            "Time Section S.\nVariable n : nat.\nDefinition extra_claim : Prop := middle n.\nEnd S.\n",
            "Time Module Hidden.\nDefinition extra_claim : Prop := forall n, middle n.\nEnd Hidden.\n",
            "Timeout 5 Section S.\nDefinition extra_claim : Prop := forall n, middle n.\nEnd S.\n",
            "Section S.\nSucceed End S.\nDefinition extra_claim : Prop := forall n, middle n.\nEnd S.\n",
        )
        for source in cases:
            for baseline in (False, True):
                with self.subTest(source=source, baseline=baseline):
                    self.write(self.extra_path, source)
                    if baseline:
                        self.rebaseline()
                        self.write(self.extra_path, self.extra_text)
                    self.assert_invalid()
                    self.write(self.extra_path, self.extra_text)
                    self.rebaseline()

    @unittest.skipUnless(KERNEL, "use --kernel for tiny compiled probes")
    def test_real_control_prefixed_scopes_are_rejected_at_both_pins(self):
        for source in ("common", "conjectures/X0", "conjectures/X1"):
            proc = subprocess.run(["coqc", "-Q", "theories", "GTBase", "theories/" + source + ".v"],
                                  cwd=self.root / "base", env=REPORT.ROCQ.environment(),
                                  text=True, capture_output=True)
            self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        for opener in ("Time Section S.", "Time Module S.", "Timeout 5 Section S."):
            with self.subTest(opener=opener):
                # An unused Section preserves the full Prop and compiles; place
                # it before the comment so documentation is not the rejection.
                scoped = self.extra_text.replace("(**", opener + "\n(**") + "End S.\n"
                self.write(self.extra_path, scoped)
                proc = subprocess.run(["coqc", "-Q", "theories", "GTBase", "theories/conjectures/X2.v"],
                                      cwd=self.root / "base", env=REPORT.ROCQ.environment(),
                                      text=True, capture_output=True)
                self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
                self.assert_invalid("outside Module/Section")
                self.rebaseline()
                self.write(self.extra_path, self.extra_text)
                self.assert_invalid("outside Module/Section")
                self.rebaseline()

    def test_ownership_lexer_masks_nested_comments_and_doubled_quote_strings(self):
        source = ('(* outer " (* inner *) *)\nRedirect "End ""S"" (*" Check nat.\n'
                  'Section S.\n')
        masked = REPORT.statement_ownership_text(source)
        self.assertEqual(len(masked), len(source))
        self.assertEqual([n for n, c in enumerate(masked) if c == "\n"],
                         [n for n, c in enumerate(source) if c == "\n"])
        self.assertIn("Section S.", masked)
        self.assertNotIn("End", masked)
        self.assertNotIn("(*", masked)
        for malformed in ('Redirect "unterminated', '(* unterminated', '*)'):
            with self.subTest(malformed=malformed), self.assertRaises(ValueError):
                REPORT.statement_ownership_text(malformed)

    @unittest.skipUnless(KERNEL, "use --kernel for tiny compiled probes")
    def test_real_quoted_commands_cannot_hide_or_close_scopes_at_either_pin(self):
        for source in ("common", "conjectures/X0", "conjectures/X1"):
            proc = subprocess.run(["coqc", "-Q", "theories", "GTBase", "theories/" + source + ".v"],
                                  cwd=self.root / "base", env=REPORT.ROCQ.environment(),
                                  text=True, capture_output=True)
            self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        for prefix in ('Section S.\nRedirect "End S" Check nat.\n',
                       'Section S.\nRedirect "escaped "" End S "" suffix" Check nat.\n',
                       'Redirect "(*" Check nat.\nSection S.\nRedirect "*)" Check nat.\n'):
            with self.subTest(prefix=prefix):
                scoped = self.extra_text.replace("(**", prefix + "(**") + "End S.\n"
                self.write(self.extra_path, scoped)
                proc = subprocess.run(["coqc", "-Q", "theories", "GTBase", "theories/conjectures/X2.v"],
                                      cwd=self.root / "base", env=REPORT.ROCQ.environment(),
                                      text=True, capture_output=True)
                self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
                self.assert_invalid("outside Module/Section")
                self.rebaseline()
                self.write(self.extra_path, self.extra_text)
                self.assert_invalid("outside Module/Section")
                self.rebaseline()
        self.write(self.extra_path, self.extra_text.replace("(**", 'Redirect "Section S" Check nat.\n(**'))
        self.rebaseline()
        self.assertEqual(self.failures(), [])
        self.compile_fixture()
        self.assertEqual(REPORT.check_kernel(self.spec), [])

    @unittest.skipUnless(KERNEL, "use --kernel for tiny compiled probes")
    def test_real_loaded_scope_is_rejected_at_both_pins(self):
        self.write("base/scope_fragment.v", "Section S.\n")
        scoped = self.extra_text.replace("(**", 'Load "scope_fragment".\n(**') + "End S.\n"
        self.write(self.extra_path, scoped)
        self.compile_fixture()
        self.assert_invalid("source-splicing Load")
        self.rebaseline()
        self.write(self.extra_path, self.extra_text)
        self.assert_invalid("source-splicing Load")

    @unittest.skipUnless(KERNEL, "use --kernel for tiny compiled probes")
    def test_real_non_ascii_and_prime_scopes_cannot_escape_at_either_pin(self):
        for source in ("common", "conjectures/X0", "conjectures/X1"):
            proc = subprocess.run(["coqc", "-Q", "theories", "GTBase", "theories/" + source + ".v"],
                                  cwd=self.root / "base", env=REPORT.ROCQ.environment(),
                                  text=True, capture_output=True)
            self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        for kind, label in (("Section", "é"), ("Module", "é"), ("Section", "Sπ"),
                            ("Module", "S'é"), ("Section", "S'")):
            with self.subTest(kind=kind, label=label):
                scoped = self.extra_text.replace("(**", f"{kind} {label}.\n(**") + f"End {label}.\n"
                self.write(self.extra_path, scoped)
                proc = subprocess.run(["coqc", "-Q", "theories", "GTBase", "theories/conjectures/X2.v"],
                                      cwd=self.root / "base", env=REPORT.ROCQ.environment(),
                                      text=True, capture_output=True)
                self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
                self.assert_invalid("Module/Section")
                self.rebaseline()
                self.write(self.extra_path, self.extra_text)
                self.assert_invalid("Module/Section")
                self.rebaseline()
        self.write(self.extra_path, self.extra_text.replace("(**", "Section S'.\nEnd S'.\n(**"))
        self.rebaseline()
        self.assertEqual(self.failures(), [])
        self.compile_fixture()
        self.assertEqual(REPORT.check_kernel(self.spec), [])

    def test_unreached_baseline_or_current_whole_prop_is_rejected(self):
        for baseline in (False, True):
            with self.subTest(baseline=baseline):
                self.write(self.middle_path, self.middle_text.replace("local_helper n", "True"))
                if baseline:
                    self.rebaseline()
                    self.write(self.middle_path, self.middle_text)
                self.assert_invalid("must be reached")
                self.write(self.middle_path, self.middle_text)
                self.rebaseline()

    def test_corpus_name_at_either_pin_cannot_be_enrolled(self):
        manifest = "meta/" + REPORT.REG.CORPORA["v2"]["manifest"]
        ordinary = json.loads((self.root / manifest).read_text())
        extra = {**self.row, "formal_name": "extra_claim"}
        for baseline in (False, True):
            with self.subTest(baseline=baseline):
                self.write_json(manifest, {"rows": [self.row, extra]})
                if baseline:
                    self.rebaseline()
                    self.write_json(manifest, ordinary)
                self.assert_invalid("outside both corpus manifests")
                self.write_json(manifest, ordinary)
                self.rebaseline()

    def test_existing_source_cannot_be_enrolled_as_extra_statement(self):
        self.spec["additional_statements"] = [self.helper]
        self.assert_invalid()
        rows, _ = REPORT.manifest_rows(self.spec["baseline_commit"])
        with self.assertRaisesRegex(ValueError, "cannot be source helpers"):
            REPORT.statement_dependencies(self.spec["baseline_commit"], {self.helper}, rows,
                                          additional_statements={self.helper})

    def test_frozen_body_and_whole_certificate_checks_still_apply(self):
        self.write(self.certificate, self.cert_source.replace(
            "Definition extra_claim : Prop := forall n, MiddleLegacy.middle n.",
            "Definition extra_claim : Prop := True."))
        self.assertTrue(any("frozen copy" in failure for failure in self.failures()))
        self.write(self.certificate, self.cert_source)
        self.spec["frozen"][-1]["certificate"] = "GTBase.common.unrelated"
        self.assertTrue(any("certificate text names its frozen and live endpoints" in f for f in self.failures()))

    @unittest.skipUnless(KERNEL, "use --kernel for tiny compiled probes")
    def test_kernel_accepts_full_enrolled_prop_and_rejects_guarded_certificate(self):
        self.compile_fixture()
        self.assertEqual(REPORT.check_kernel(self.spec), [])
        self.write(self.certificate, self.cert_source.replace(
            "Lemma extra_compat : ExtraLegacy.extra_claim <-> extra_claim.\nProof. split; trivial. Qed.",
            "Lemma extra_compat : False -> (ExtraLegacy.extra_claim <-> extra_claim).\n"
            "Proof. intros h; destruct h. Qed."))
        self.compile_fixture()
        self.assertTrue(REPORT.check_kernel(self.spec))

    @unittest.skipUnless(KERNEL, "use --kernel for tiny compiled probes")
    def test_kernel_rejects_inherited_axioms_without_an_exemption(self):
        self.write(self.certificate, self.cert_source.replace(
            "Lemma extra_compat : ExtraLegacy.extra_claim <-> extra_claim.\nProof. split; trivial. Qed.",
            "Axiom extra_axiom : ExtraLegacy.extra_claim <-> extra_claim.\n"
            "Lemma extra_compat : ExtraLegacy.extra_claim <-> extra_claim.\n"
            "Proof. exact extra_axiom. Qed."))
        self.compile_fixture()
        self.assertEqual(self.failures(), [])
        self.assertTrue(REPORT.check_kernel(self.spec))

    @unittest.skipUnless(KERNEL, "use --kernel for tiny compiled probes")
    def test_kernel_checks_unapplied_frozen_prop_even_with_inferable_implicit(self):
        changed = self.cert_source.replace(
            "Definition extra_claim : Prop := forall n, MiddleLegacy.middle n.",
            "Definition extra_claim {n : nat} : Prop := MiddleLegacy.middle n.")
        changed = changed.replace("Lemma extra_compat : ExtraLegacy.extra_claim <-> extra_claim.",
                                  "Lemma extra_compat : @ExtraLegacy.extra_claim 0 <-> extra_claim.")
        # Both propositions are provable; this deliberately malformed frozen
        # endpoint has an implicit value argument that Check may instantiate.
        changed = changed.replace(
            "Lemma extra_compat : @ExtraLegacy.extra_claim 0 <-> extra_claim.\n"
            "Proof. split; trivial. Qed.",
            "Lemma extra_compat : @ExtraLegacy.extra_claim 0 <-> extra_claim.\n"
            "Proof. change (0 = 0 <-> forall n : nat, n = n). split; auto. Qed.")
        self.write(self.certificate, changed)
        self.compile_fixture()
        self.assertTrue(REPORT.check_kernel(self.spec))


class PublicAdditionalStatementTests(unittest.TestCase):
    """An explicitly selected public Prop, including an older complete snapshot."""

    write = ReportTests.write
    write_json = ReportTests.write_json
    command = ReportTests.command
    write_manifests = ReportTests.write_manifests
    report = ReportTests.report
    failures = ReportTests.failures
    rebaseline = ReportTests.rebaseline
    register = FrozenRoleTests.register
    commit = AdditionalStatementTests.commit
    assert_invalid = AdditionalStatementTests.assert_invalid

    def setUp(self):
        AdditionalStatementTests.setUp(self)
        old_path = self.extra_path
        self.extra_path = "base/theories/foundations/X2.v"
        self.extra = "GTBase.foundations.X2.extra_claim"
        (self.root / old_path).unlink()
        self.write(self.extra_path, self.extra_text)
        project = self.root / "base/_CoqProject"
        project.write_text(project.read_text().replace(
            "theories/conjectures/X2.v", "theories/foundations/X2.v"))
        self.cert_source = self.cert_source.replace(
            "From GTBase.conjectures Require Import X1 X2.",
            "From GTBase.conjectures Require Import X1.\nFrom GTBase.foundations Require Import X2.")
        self.spec["additional_statements"] = [self.extra]
        self.spec["frozen"][-1].update(qualified=self.extra, path=self.extra_path)
        self.spec["cross_module_consumers"][-1]["path"] = self.extra_path
        self.write(self.certificate, self.cert_source)
        self.rebaseline()

    def compile_fixture(self):
        for source in ("common", "conjectures/X0", "conjectures/X1", "foundations/X2",
                       "migration/test_family"):
            proc = subprocess.run(["coqc", "-Q", "theories", "GTBase", "theories/" + source + ".v"],
                                  cwd=self.root / "base", env=REPORT.ROCQ.environment(),
                                  text=True, capture_output=True)
            self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)

    def add_original(self):
        old_text = self.extra_text.replace("forall n, middle n.", "forall n, middle n /\\ True.")
        self.write(self.extra_path, old_text)
        old_pin = self.commit()
        self.write(self.extra_path, self.extra_text)
        self.rebaseline()
        self.cert_source += (
            "Module Original.\n"
            "Definition extra_claim : Prop := forall n, MiddleLegacy.middle n /\\ True.\n"
            "End Original.\n"
            "Lemma original_extra_compat : Original.extra_claim <-> extra_claim.\n"
            "Proof. split; intros H n; [exact (proj1 (H n)) | split; [apply H | exact I]]. Qed.\n")
        original = {**copy.deepcopy(self.spec["frozen"][-1]), "kind": "original-statement",
                    "commit": old_pin, "frozen": "Original.extra_claim",
                    "certificate": self.module + ".original_extra_compat"}
        self.spec["frozen"].append(original)
        self.register("original_extra_compat")
        self.write(self.certificate, self.cert_source)

    def test_public_prop_without_repository_source_enables_complete_index(self):
        self.assertNotIn("repository_sources", self.registry["primitives"]["test-family"])
        self.assertEqual(self.failures(), [])
        rows, _ = REPORT.manifest_rows(self.spec["baseline_commit"])
        for pin in (self.spec["baseline_commit"], None):
            found, closure = REPORT.statement_dependencies(
                pin, {self.helper}, rows, additional_statements={self.extra})
            self.assertEqual(found, {self.statement, self.extra})
            self.assertIn("GTBase.conjectures.X1.middle", closure)
        # Indexing public files never auto-enrolls other Prop-valued definitions.
        self.assertNotIn(self.extra, REPORT.statement_dependencies(
            self.spec["baseline_commit"], {self.helper}, rows, include_public=True)[0])
        del self.spec["frozen"][2]
        self.assertIn("additional statement paths have complete frozen intermediary coverage", self.failures())

    def test_public_current_and_original_keep_exact_source_provenance(self):
        self.add_original()
        self.assertEqual(self.failures(), [])
        original = copy.deepcopy(self.spec["frozen"][-1])
        self.spec["frozen"][-1]["commit"] = self.spec["baseline_commit"]
        self.assertTrue(any("frozen copy" in failure for failure in self.failures()))
        self.spec["frozen"][-1] = original
        self.write(self.certificate, self.cert_source.replace(
            "forall n, MiddleLegacy.middle n /\\ True.", "True."))
        self.assertTrue(any("frozen copy" in failure for failure in self.failures()))
        self.write(self.certificate, self.cert_source)
        self.spec["frozen"].append(copy.deepcopy(self.spec["frozen"][-2]))
        self.assert_invalid("one exact non_corpus")
        self.spec["frozen"].pop()
        del self.spec["frozen"][-2]
        self.assert_invalid("one exact non_corpus")

    def test_supported_public_paths_do_not_allow_arbitrary_files(self):
        for name in ("Reconstruction.foundations.kelly.claim", "GTBase.common.claim",
                     "ClassicalLemmas.konig.source.claim"):
            with self.subTest(name=name):
                self.assertTrue(REPORT.public_repository_path(REPORT.additional_statement_path(name)))
        for name in ("Unknown.foundations.source.claim", "GTBase.migration.source.claim",
                     "GTBase.examples.source.claim", "Chromatic.private.source.claim",
                     "GTBase.foundations._assum_probe.claim", "GTBase.scratch_probe.claim"):
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, "additional statement"):
                REPORT.additional_statement_path(name)

    def test_original_identity_and_immutable_commit_guards(self):
        self.add_original()
        original = copy.deepcopy(self.spec["frozen"][-1])
        self.command("git", "branch", "moving-history", original["commit"])
        for mutation in ({"commit": "moving-history"}, {"commit": None}, {"commit": "0" * 40},
                         {"commit": original["commit"][:7]}, {"non_corpus": False},
                         {"corpus": "v2"}, {"path": self.middle_path}, {"name": "middle"},
                         {"certificate": None}, {"kind": "chain"}):
            with self.subTest(mutation=mutation):
                self.spec["frozen"][-1] = {**original, **mutation}
                self.assert_invalid("additional statement|repository source git")
        self.spec["frozen"][-1] = original
        self.assertEqual(self.failures(), [])

    def historical_snapshot(self, source=None, project=None, alias=None):
        """Create a distinct old commit without changing the valid current files."""
        targets = (self.extra_path, "base/_CoqProject")
        current = {p: (self.root / p).read_text() for p in targets}
        old = self.spec["frozen"][-1]["commit"]
        self.write(self.extra_path, source if source is not None else
                   self.command("git", "show", old + ":" + self.extra_path))
        if project is not None:
            self.write("base/_CoqProject", project)
        if alias:
            file = self.root / alias
            self.write("snapshot-copy", file.read_text())
            file.unlink()
            file.symlink_to(self.root / "snapshot-copy")
        historical = self.commit()
        for p, text in current.items():
            file = self.root / p
            if file.is_symlink():
                file.unlink()
            self.write(p, text)
        self.spec["frozen"][-1]["commit"] = historical

    def test_original_project_namespace_and_regular_blob_guards(self):
        self.add_original()
        original = copy.deepcopy(self.spec["frozen"][-1])
        project = (self.root / "base/_CoqProject").read_text()
        for changed in (project.replace("theories/foundations/X2.v\n", ""),
                        project.replace("-Q theories GTBase", "-Q theories Wrong")):
            with self.subTest(project=changed):
                self.spec["frozen"][-1] = copy.deepcopy(original)
                self.historical_snapshot(project=changed)
                self.assert_invalid("not build-listed|namespace ownership")
        for alias in (self.extra_path, "base/_CoqProject"):
            with self.subTest(alias=alias):
                self.spec["frozen"][-1] = copy.deepcopy(original)
                self.historical_snapshot(alias=alias)
                self.assert_invalid("expected regular source blob")

    def test_original_missing_files_and_corpus_identity_are_rejected(self):
        self.add_original()
        original = copy.deepcopy(self.spec["frozen"][-1])
        for relative in (self.extra_path, "base/_CoqProject"):
            with self.subTest(missing=relative):
                file = self.root / relative
                text = file.read_text()
                file.unlink()
                self.spec["frozen"][-1] = {**original, "commit": self.commit()}
                self.write(relative, text)
                self.assert_invalid("repository source git|regular source blob")
        for paths in REPORT.REG.CORPORA.values():
            relative = "meta/" + paths["manifest"]
            file = self.root / relative
            text = file.read_text()
            manifest = json.loads(text)
            manifest["rows"].append({"formal_name": "extra_claim"})
            self.write(relative, json.dumps(manifest))
            self.spec["frozen"][-1] = {**original, "commit": self.commit()}
            self.write(relative, text)
            self.assert_invalid("outside historical corpus manifests")
        self.spec["frozen"][-1] = original
        self.assertEqual(self.failures(), [])

    def test_original_nullary_shape_scope_and_load_guards(self):
        self.add_original()
        original = copy.deepcopy(self.spec["frozen"][-1])
        raw = self.command("git", "show", original["commit"] + ":" + self.extra_path)
        for source in (raw.replace("(**", "Section S.\n(**") + "\nEnd S.\n",
                       raw.replace("(**", "Module S.\n(**") + "\nEnd S.\n",
                       raw.replace("(**", "Time Section é.\n(**") + "\nEnd é.\n",
                       raw.replace("(**", 'Load "scope_fragment".\n(**') + "\nEnd S.\n",
                       raw.replace("extra_claim : Prop", "extra_claim (n : nat) : Prop"),
                       raw.replace("extra_claim : Prop", "extra_claim")):
            with self.subTest(source=source):
                self.spec["frozen"][-1] = copy.deepcopy(original)
                self.historical_snapshot(source=source)
                self.assert_invalid("additional statement|unsupported Module/Section")

    @unittest.skipUnless(KERNEL, "use --kernel for tiny compiled probes")
    def test_compiled_unused_original_section_is_rejected(self):
        self.add_original()
        self.compile_fixture()
        raw = self.command("git", "show", self.spec["frozen"][-1]["commit"] + ":" + self.extra_path)
        scoped = raw.replace("(**", "Section Hidden.\n(**") + "\nEnd Hidden.\n"
        self.write(self.extra_path, scoped)
        proc = subprocess.run(["coqc", "-Q", "theories", "GTBase", "theories/foundations/X2.v"],
                              cwd=self.root / "base", env=REPORT.ROCQ.environment(),
                              text=True, capture_output=True)
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.write(self.extra_path, self.extra_text)
        self.historical_snapshot(source=scoped)
        self.assert_invalid("outside Module/Section")

    def test_public_regular_source_project_and_namespace_guards_stay_fresh(self):
        self.assertEqual(self.failures(), [])
        for relative in (self.extra_path, "base/_CoqProject"):
            file = self.root / relative
            text = file.read_text()
            file.unlink()
            self.assert_invalid("missing or aliased")
            target = self.root / "copy"
            target.write_text(text)
            file.symlink_to(target)
            self.assert_invalid("missing or aliased")
            file.unlink()
            file.write_text(text)
        project = self.root / "base/_CoqProject"
        original = project.read_text()
        project.write_text(original.replace("theories/foundations/X2.v\n", ""))
        self.assert_invalid("not build-listed")
        project.write_text(original.replace("-Q theories GTBase", "-Q theories Wrong"))
        self.assert_invalid("namespace ownership")
        project.write_text(original)
        self.write(self.extra_path, self.extra_text.replace("middle n", "False"))
        self.assert_invalid("must be reached")

    test_public_shape_and_scope_guards = AdditionalStatementTests.test_prop_shape_and_scopes_reject_helpers_and_hidden_parameters
    test_public_wrong_mapping_guards = AdditionalStatementTests.test_wrong_or_missing_mapping_is_rejected
    test_public_manifest_exclusion = AdditionalStatementTests.test_corpus_name_at_either_pin_cannot_be_enrolled
    test_public_frozen_body_and_whole_certificate = AdditionalStatementTests.test_frozen_body_and_whole_certificate_checks_still_apply
    test_public_kernel_guarded_certificate = AdditionalStatementTests.test_kernel_accepts_full_enrolled_prop_and_rejects_guarded_certificate
    test_public_kernel_axioms = AdditionalStatementTests.test_kernel_rejects_inherited_axioms_without_an_exemption
    test_public_kernel_implicit_parameter = AdditionalStatementTests.test_kernel_checks_unapplied_frozen_prop_even_with_inferable_implicit

    @unittest.skipUnless(KERNEL, "use --kernel for tiny compiled probes")
    def test_compiled_public_scopes_and_load_reject_at_both_pins(self):
        self.compile_fixture()
        self.write("base/scope_fragment.v", "Section S.\n")
        for prefix, label in (("Time Section S.\n", "S"), ("Section é.\n", "é"),
                              ('Section S.\nRedirect "escaped "" End S" Check nat.\n', "S"),
                              ('Load "scope_fragment".\n', "S")):
            with self.subTest(prefix=prefix):
                source = self.extra_text.replace("(**", prefix + "(**") + f"End {label}.\n"
                self.write(self.extra_path, source)
                proc = subprocess.run(["coqc", "-Q", "theories", "GTBase", "theories/foundations/X2.v"],
                                      cwd=self.root / "base", env=REPORT.ROCQ.environment(),
                                      text=True, capture_output=True)
                self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
                self.assert_invalid("Module/Section|source-splicing Load")
                self.rebaseline()
                self.write(self.extra_path, self.extra_text)
                self.assert_invalid("Module/Section|source-splicing Load")
                self.rebaseline()

    @unittest.skipUnless(KERNEL, "use --kernel for tiny compiled probes")
    def test_public_original_kernel_checks_every_complete_endpoint(self):
        self.add_original()
        self.compile_fixture()
        self.assertEqual(REPORT.check_kernel(self.spec), [])
        old_proof = "Proof. split; intros H n; [exact (proj1 (H n)) | split; [apply H | exact I]]. Qed."
        changed = self.cert_source.replace(
            "Lemma original_extra_compat : Original.extra_claim <-> extra_claim.",
            "Lemma original_extra_compat : False -> (Original.extra_claim <-> extra_claim).")
        self.write(self.certificate, changed.replace(old_proof, "Proof. intros H; destruct H. Qed."))
        self.compile_fixture()
        self.assertTrue(REPORT.check_kernel(self.spec))
        changed = self.cert_source.replace(
            "Definition extra_claim : Prop := forall n, MiddleLegacy.middle n /\\ True.",
            "Definition extra_claim {n : nat} : Prop := MiddleLegacy.middle n /\\ True.")
        changed = changed.replace("Original.extra_claim <->", "@Original.extra_claim 0 <->")
        changed = changed.replace(old_proof,
            "Proof. change ((0 = 0 /\\ True) <-> forall n : nat, n = n). "
            "split; intros; [reflexivity | split; [reflexivity | exact I]]. Qed.")
        self.write(self.certificate, changed)
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

    def select_public_independently(self):
        # A path family consumes a public model definition whose basename is
        # already the conjecture-discovery name of another family (B22/C20).
        self.primitive['normalized_names'] = ['path_view']
        self.write_registry()

    def conjecture_helper(self, name):
        path = 'chromatic-theory/theories/conjectures/X2.v'
        text = f'Definition {name} (n : nat) : Prop := n = n.\n'
        self.write(path, text)
        records, _ = REPORT.INV.parse_source(
            text, path, 'Chromatic.conjectures.X2', set())
        self.assertEqual(len(records), 1)
        return records[0]

    def write_other_family(self, helper):
        other = copy.deepcopy(self.primitive)
        other.update(canonical_name=None, status='auditing', fidelity='PENDING',
                     normalized_names=[helper['normalized_name']],
                     source_definitions=[helper['qualified_name']],
                     compatibility_theorems=[])
        other.pop('repository_sources')
        self.write_json('meta/library_primitives/other-family.json', {
            'schema_version': 1, 'family': 'other-family', 'primitive': other})

    def test_public_descriptor_does_not_claim_same_named_conjectures(self):
        self.select_public_independently()
        helper = self.conjecture_helper('x2_local_helper')
        self.write_other_family(helper)
        registry, errors = REPORT.INV.validate_registry({'helpers': [helper]})
        self.assertEqual(errors, [])
        self.assertEqual(registry['test-family']['source_definitions'], [self.helper])
        self.assertEqual(registry['other-family']['source_definitions'],
                         [helper['qualified_name']])
        self.assertEqual(set(self.records()), {self.helper})
        # The same explicit source still brings its public intermediary and
        # both whole statements into the report, without changing inventory.
        self.assertEqual(self.failures(), [])
        self.assertEqual(json.loads((self.root / 'meta/library_helper_inventory.json').read_text()),
                         {'helpers': []})

    def test_conjecture_completeness_never_skips_unowned_or_other_owned_names(self):
        self.select_public_independently()
        helper = self.conjecture_helper('x2_path_view')
        for other_owned in (False, True):
            with self.subTest(other_owned=other_owned):
                if other_owned:
                    self.write_other_family(helper)
                _, errors = REPORT.INV.validate_registry({'helpers': [helper]})
                self.assertTrue(any('test-family.json: source_definitions drift'
                                    in error for error in errors), errors)

    def test_independent_public_enrollment_preserves_deferred_source_accounting(self):
        self.select_public_independently()
        helper = self.conjecture_helper('x2_path_view')
        name = helper['qualified_name']
        self.primitive['source_definitions'].append(name)
        self.primitive['semantic_classes'] = {
            'public': {'members': [self.helper], 'state': 'migrated-public-source'},
            'different-contract': {'members': [name], 'state': 'deferred-excluded'},
        }
        self.write_registry()
        _, errors = REPORT.INV.validate_registry({'helpers': [helper]})
        self.assertEqual(errors, [])
        self.assertEqual(set(self.primitive['source_definitions']), {self.helper, name})
        self.assertEqual(REPORT.migrated_registry_sources(self.primitive), {self.helper})
        self.assertEqual(self.failures(), [])

    def test_duplicate_independent_public_ownership_is_rejected(self):
        self.select_public_independently()
        self.write_json('meta/library_primitives/other-family.json', {
            'schema_version': 1, 'family': 'other-family', 'primitive': self.primitive})
        _, errors = REPORT.INV.validate_registry({'helpers': []})
        self.assertTrue(any('duplicate source ownership' in error for error in errors), errors)

    def test_independent_public_enrollment_still_requires_exact_pin(self):
        self.select_public_independently()
        original = copy.deepcopy(self.primitive)
        for defect, message in (('missing-descriptor', 'missing from inventory'),
                                ('missing-commit', 'needs path, commit, blob'),
                                ('wrong-blob', 'differs from pin'),
                                ('wrong-declaration', 'differs from pin')):
            with self.subTest(defect=defect):
                self.primitive = copy.deepcopy(original)
                if defect == 'missing-descriptor':
                    self.primitive.pop('repository_sources')
                elif defect == 'missing-commit':
                    self.primitive['repository_sources'][self.helper].pop('commit')
                else:
                    field = 'blob' if defect == 'wrong-blob' else 'declaration_hash'
                    self.primitive['repository_sources'][self.helper][field] = (
                        '0' * len(self.pin[field]))
                self.write_registry()
                _, errors = REPORT.INV.validate_registry({'helpers': []})
                self.assertTrue(any(message in error for error in errors), errors)

    def test_independent_public_enrollment_rejects_unsupported_source_kind(self):
        self.select_public_independently()
        live = (self.root / self.source).read_text()
        for text in ('Record local_helper := MkHelper { value : nat }.\n',
                     'Lemma local_helper : True. Proof. exact I. Qed.\n'):
            for original in (False, True):
                with self.subTest(text=text, original=original):
                    self.write(self.source, text)
                    if original:
                        self.pin['commit'] = self.commit()
                        self.pin['blob'] = self.command(
                            'git', 'rev-parse', self.pin['commit'] + ':' + self.source)
                        self.write(self.source, live)
                    with self.assertRaisesRegex(REPORT.RegistryError,
                                                'needs one top-level Definition'):
                        self.records()
                    self.pin['commit'] = self.baseline
                    self.pin['blob'] = self.command(
                        'git', 'rev-parse', self.baseline + ':' + self.source)
                    self.write(self.source, live)

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
        self.select_public_independently()
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


class ClassicalSourceTests(unittest.TestCase):
    """An enrolled classical source reaches rows through a sibling and foundation."""

    write = RepositorySourceTests.write
    write_json = RepositorySourceTests.write_json
    command = RepositorySourceTests.command
    commit = RepositorySourceTests.commit
    report = RepositorySourceTests.report
    failures = RepositorySourceTests.failures
    records = RepositorySourceTests.records
    write_registry = RepositorySourceTests.write_registry

    def setUp(self):
        RepositorySourceTests.setUp(self)
        self.source = "classical-lemmas/theories/konig/source.v"
        self.helper = "ClassicalLemmas.konig.source.local_helper"
        self.bridge_path = "classical-lemmas/theories/konig/bridge.v"
        self.bridge = "ClassicalLemmas.konig.bridge.bridge"
        self.write(self.source, self.original)
        self.write(self.bridge_path, "From ClassicalLemmas.konig Require Import source.\n"
                   "Definition bridge (n : nat) : Prop := source.local_helper n.\n")
        self.write(self.middle_path, "From ClassicalLemmas.konig Require Import bridge.\n"
                   "Definition middle (n : nat) : Prop := bridge.bridge n.\n")
        self.write("classical-lemmas/_CoqProject", "-R theories ClassicalLemmas\n"
                   "-Q ../base/theories GTBase\ntheories/konig/source.v\ntheories/konig/bridge.v\n")
        for package in ("chromatic-theory", "spectral-graph-theory"):
            project = self.root / package / "_CoqProject"
            project.write_text(project.read_text() + "-Q ../classical-lemmas/theories ClassicalLemmas\n")
        self.baseline = self.commit()
        self.pin.update(path=self.source, commit=self.baseline,
                        blob=self.command("git", "rev-parse", self.baseline + ":" + self.source))
        self.primitive.update(source_definitions=[self.helper], repository_sources={self.helper: self.pin})
        self.primitive["compatibility_theorems"].append(self.module + ".bridge_compat")
        self.write_registry()
        self.write(self.source, "From GTBase Require Import common.\n"
                   "Definition local_helper (n : nat) : Prop := canonical n.\n")
        self.cert_source = self.cert_source.replace(
            "From GTBase Require Import original.", "From ClassicalLemmas.konig Require Import source bridge.")
        self.cert_source = self.cert_source.replace("GTBase.original.local_helper", self.helper)
        self.cert_source = self.cert_source.replace(
            "Definition middle (n : nat) : Prop := Legacy.local_helper n.",
            "Definition bridge (n : nat) : Prop := Legacy.local_helper n.\n"
            "Definition middle (n : nat) : Prop := Legacy.bridge n.")
        self.cert_source += ("Lemma bridge_compat n : Legacy.bridge n <-> " + self.bridge + " n.\n"
                             "Proof. split; trivial. Qed.\n")
        self.write(self.certificate, self.cert_source)
        self.spec["baseline_commit"] = self.baseline
        self.spec["namespaces"]["classical-lemmas"] = "ClassicalLemmas"
        self.spec["frozen"][0].update(path=self.source, qualified=self.helper)
        self.spec["frozen"][1]["substitutions"] = {"bridge.bridge": "Legacy.bridge"}
        self.spec["frozen"].insert(1, {
            "kind": "chain", "qualified": self.bridge, "path": self.bridge_path,
            "name": "bridge", "frozen_path": self.certificate, "frozen": "Legacy.bridge",
            "certificate": self.module + ".bridge_compat",
            "substitutions": {"source.local_helper": "Legacy.local_helper"}})
        self.spec["cross_module_consumers"] = [
            {"path": self.bridge_path, "name": "local_helper"},
            {"path": self.middle_path, "name": "bridge"},
            *({"path": obj["path"], "name": "middle"} for obj in self.statements)]

    def test_classical_sibling_and_both_rows_are_required(self):
        self.assertEqual(self.failures(), [])
        self.assertEqual(set(self.records()), {self.helper})
        self.assertNotEqual(self.records()[self.helper]["declaration_hash"], self.pin["declaration_hash"])
        original = copy.deepcopy(self.spec["frozen"])
        for obj in original[1:]:
            with self.subTest(omitted=obj["qualified"]):
                self.spec["frozen"] = [item for item in original if item != obj]
                expected = ("public source paths have complete frozen intermediary coverage"
                            if obj["kind"] == "chain" else "affected statement coverage matches baseline dependencies")
                self.assertIn(expected, self.failures())
        self.spec["frozen"] = original

    def test_classical_current_ownership_is_not_guessed(self):
        path = self.root / "classical-lemmas/_CoqProject"
        original = path.read_text()
        for replacement, message in (
            (original.replace("theories/konig/source.v\n", ""), "not build-listed"),
            (original.replace("-R theories ClassicalLemmas", "-R theories Wrong"), "namespace ownership"),
            (original + "-Q theories Alias\n", "namespace ownership")):
            with self.subTest(replacement=replacement):
                path.write_text(replacement)
                with self.assertRaisesRegex(REPORT.RegistryError, message):
                    self.records()
        path.write_text(original)

    def test_classical_original_membership_and_regular_blobs_are_required(self):
        project = self.root / "classical-lemmas/_CoqProject"
        original_project = project.read_text()
        for target in (self.source, "classical-lemmas/_CoqProject"):
            with self.subTest(aliased=target):
                path = self.root / target
                original = path.read_text()
                path.unlink()
                path.symlink_to("absent.v")
                pin = self.commit()
                path.unlink()
                path.write_text(original)
                with self.assertRaisesRegex(REPORT.RegistryError, "regular"):
                    REPORT.statement_dependencies(pin, {self.helper}, {}, include_public=True)
        project.write_text(original_project.replace("theories/konig/source.v\n", ""))
        pin = self.commit()
        project.write_text(original_project)
        with self.assertRaisesRegex(REPORT.RegistryError, "missing from baseline dependency index"):
            REPORT.statement_dependencies(pin, {self.helper}, {}, include_public=True)

    def test_classical_scan_excludes_unlisted_certificates_examples_and_scratch(self):
        project = self.root / "classical-lemmas/_CoqProject"
        for relative in ("migration/fake.v", "examples/fake.v", "konig/_faith_fake.v", "konig/unlisted.v"):
            self.write("classical-lemmas/theories/" + relative,
                       "Definition forbidden_statement : Prop := source.local_helper 0.\n")
            if "unlisted" not in relative:
                project.write_text(project.read_text() + "theories/" + relative + "\n")
        pin = self.commit()
        rows, _ = REPORT.manifest_rows(pin)
        reached, chain = REPORT.statement_dependencies(pin, {self.helper}, rows, include_public=True)
        self.assertEqual(reached, {obj["qualified"] for obj in self.statements})
        self.assertIn(self.bridge, chain)

    @unittest.skipUnless(KERNEL, "use --kernel for tiny compiled probes")
    def test_classical_chain_kernel_checks_both_complete_rows(self):
        env = REPORT.ROCQ.environment()
        for package, sources in (
            ("base", ["theories/common.v"]),
            ("classical-lemmas", ["theories/konig/source.v", "theories/konig/bridge.v"]),
            ("chromatic-theory", ["theories/foundations/intermediary.v", "theories/conjectures/X0.v"]),
            ("spectral-graph-theory", ["theories/conjectures/X1.v", "theories/migration/test_family.v"])):
            flags = REPORT.INV.project_sources((self.root / package / "_CoqProject").read_text())[1]
            includes = [item for directory, namespace in flags for item in ("-Q", directory, namespace)]
            for source in sources:
                result = subprocess.run(["rocq", "compile", *includes, source], cwd=self.root / package,
                                        env=env, text=True, capture_output=True)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(REPORT.check_kernel(self.spec), [])


class ProviderAttributionTests(unittest.TestCase):
    """Actual short-name collisions and conservative project-context boundaries."""

    write = ReportTests.write
    write_json = ReportTests.write_json
    command = ReportTests.command
    commit = ReportTests.commit
    write_manifests = ReportTests.write_manifests
    report = ReportTests.report
    failures = ReportTests.failures

    def setUp(self):
        ReportTests.setUp(self)
        old_source, old_cert = self.source, self.certificate
        self.source = "infinite-graph-theory/theories/conjectures/X0.v"
        self.certificate = "infinite-graph-theory/theories/migration/test_family.v"
        self.module = "Infinite.migration.test_family"
        self.helper = "Infinite.conjectures.X0.local_helper"
        self.statement = "Infinite.conjectures.X0.test_statement"
        self.other = "chromatic-theory/theories/conjectures/X1.v"
        self.other_cert = "chromatic-theory/theories/migration/collision.v"
        self.other_statement = "Chromatic.conjectures.X1.foreign_statement"
        self.infinite_project = ("-R theories Infinite\n-Q ../base/theories GTBase\n"
                                 "theories/conjectures/X0.v\n")
        self.other_project = ("-R theories Chromatic\n-Q ../base/theories GTBase\n"
                              "theories/conjectures/X1.v\n")
        self.write("base/_CoqProject", "-Q theories GTBase\ntheories/common.v\n")
        common = (self.root / "base/theories/common.v").read_text()
        self.write("base/theories/common.v", common + "Definition local_helper (n : nat) : Prop := n = 0.\n")
        self.write("infinite-graph-theory/_CoqProject", self.infinite_project)
        self.write("chromatic-theory/_CoqProject", self.other_project)
        self.write(self.source, self.original)
        self.write(self.other, "From GTBase Require Import common.\n"
                   "Definition foreign_statement : Prop := local_helper 0.\n")
        (self.root / old_source).unlink()
        (self.root / old_cert).unlink()
        self.row["repo"] = "infinite-graph-theory"
        self.write_manifests("v2")
        manifest_path = "meta/" + REPORT.REG.CORPORA["v2"]["manifest"]
        manifest = json.loads((self.root / manifest_path).read_text())
        manifest["rows"].append(dict(self.row, formal_name="foreign_statement", repo="chromatic-theory", slug="foreign"))
        self.write_json(manifest_path, manifest)
        primitive = self.registry["primitives"]["test-family"]
        primitive["owner"] = "infinite-graph-theory"
        primitive["source_definitions"] = [self.helper]
        primitive["compatibility_theorems"] = [self.module + ".helper_compat", self.module + ".statement_compat", "GTBase.common.unrelated"]
        self.write_json("meta/library_primitives/test-family.json", {"schema_version":1, "family":"test-family", "primitive":primitive})
        self.write_json("meta/library_helper_inventory.json", {"helpers":[{
            "qualified_name":self.helper,
            "declaration_hash":REPORT.sha256(REPORT.find_decl(self.original, "local_helper")["text"])}]})
        self.baseline = self.commit()
        self.spec["baseline_commit"] = self.baseline
        self.spec["namespaces"]["infinite-graph-theory"] = "Infinite"
        self.spec["certificate_files"][0] = self.certificate
        for obj in self.spec["frozen"]:
            obj["path"], obj["frozen_path"] = self.source, self.certificate
            obj["qualified"] = (self.helper if obj["kind"] == "source" else self.statement)
            obj["certificate"] = obj["certificate"].replace("GTBase.migration", "Infinite.migration")
        self.cert_source = self.cert_source.replace("From GTBase.conjectures", "From Infinite.conjectures")
        self.write(self.source, self.live)
        self.write(self.certificate, self.cert_source)
        self.write("infinite-graph-theory/_CoqProject", self.infinite_project + "theories/migration/test_family.v\n")
        self.write(self.other_cert, "From GTBase Require Import common.\nModule OtherLegacy.\n"
                   "Definition old_row : Prop := local_helper 0.\nEnd OtherLegacy.\n")
        self.write("chromatic-theory/_CoqProject", self.other_project + "theories/migration/collision.v\n")

    def dependencies(self, commit=None):
        rows, _ = REPORT.manifest_rows(commit)
        return REPORT.statement_dependencies(commit, {self.helper}, rows)[0]

    def test_all_three_attribution_sites_exclude_only_unavailable_provider(self):
        result = self.report()
        self.assertEqual([c for c in result["checks"] if not c["ok"]], [])
        self.assertEqual(self.dependencies(self.baseline), {self.statement})
        self.assertEqual(result["stale_snapshots"], [])
        self.assertFalse(any(c["path"].startswith("chromatic-theory/") for c in result["consumers"]))
        # A real family stale reference still fails, even in a newly added file.
        self.write("infinite-graph-theory/theories/migration/stale.v",
                   "Module PriorLegacy.\nDefinition bad : Prop := local_helper 0.\nEnd PriorLegacy.\n")
        self.assertTrue(any("resolves through live" in failure for failure in self.failures()))

    def test_mapped_ambiguity_transitive_import_and_qualified_references_stay(self):
        self.assertNotIn(self.other_statement, self.dependencies())
        self.write("chromatic-theory/_CoqProject", self.other_project + "-Q ../infinite-graph-theory/theories Infinite\n"
                   "theories/migration/collision.v\n")
        # Visibility is an over-approximation: no direct Require is necessary.
        self.assertIn(self.other_statement, self.dependencies())
        self.write("base/theories/relay.v", "Require Export Infinite.conjectures.X0.\n")
        self.write("base/_CoqProject", "-Q theories GTBase\n-Q ../infinite-graph-theory/theories Infinite\n"
                   "theories/common.v\ntheories/relay.v\n")
        self.write(self.other, "From GTBase Require Import relay.\nDefinition foreign_statement : Prop := local_helper 0.\n")
        self.assertIn(self.other_statement, self.dependencies())
        self.write("chromatic-theory/_CoqProject", self.other_project)
        for spelling in ("Infinite.conjectures.X0.local_helper", "X0.local_helper"):
            with self.subTest(spelling=spelling):
                self.write(self.other, "Definition foreign_statement : Prop := " + spelling + " 0.\n")
                self.assertIn(self.other_statement, self.dependencies())

    def test_mapping_edits_and_each_historical_snapshot_are_fresh(self):
        self.assertFalse(REPORT.ProviderContext(None).possible(self.other, self.source))
        project = self.root / "chromatic-theory/_CoqProject"
        old = project.stat()
        project.write_text(self.other_project + "-Q ../infinite-graph-theory/theories Infinite\n")
        os.utime(project, ns=(old.st_atime_ns, old.st_mtime_ns))
        current = self.commit()
        self.assertTrue(REPORT.ProviderContext(None).possible(self.other, self.source))
        self.assertTrue(REPORT.ProviderContext(current).possible(self.other, self.source))
        self.assertFalse(REPORT.ProviderContext(self.baseline).possible(self.other, self.source))
        project.write_text(self.other_project)
        self.assertFalse(REPORT.ProviderContext(None).possible(self.other, self.source))

    def test_reachable_chains_preserve_mixed_qualified_and_bare_edges(self):
        self.write(self.source, (self.root / self.source).read_text() +
                   "Definition bridge := local_helper 0.\n"
                   "Definition chained_statement := bridge /\\ test_statement.\n")
        self.write(self.other, "Definition foreign_bridge := local_helper 0.\n"
                   "Definition foreign_statement := foreign_bridge /\\ "
                   "Infinite.conjectures.X0.local_helper 0 /\\ local_helper 0.\n")
        rows, _ = REPORT.manifest_rows(None)
        statements, chains = REPORT.statement_dependencies(None, {self.helper}, rows)
        self.assertEqual(statements, {self.statement, self.other_statement,
                         "Infinite.conjectures.X0.chained_statement"})
        # The qualified occurrence preserves its edge even when the same pair
        # also occurs bare. The unavailable bare intermediary must stay absent.
        self.assertEqual(chains, statements | {self.helper, "Infinite.conjectures.X0.bridge"})

    def test_lazy_fallback_diagnostics_are_independent_of_hash_seed(self):
        # Two roots can reach one consumer through a qualified or a bare edge.
        # A deterministic walk must inspect the same contexts in either run.
        script = r'''
import json,sys
sys.path.insert(0, "meta")
import test_migration_report as T
c=T.ProviderAttributionTests("test_all_three_attribution_sites_exclude_only_unavailable_provider")
c.setUp(); M=T.REPORT
try:
    c.write(c.source,(c.root/c.source).read_text()+"Definition other_helper (n : nat) : Prop := n = n.\n")
    c.write(c.other,"Definition foreign_statement : Prop := Infinite.conjectures.X0.other_helper 0 /\\ local_helper 0.\n")
    c.write("chromatic-theory/_CoqProject",c.other_project+"-I plugins\n")
    context=M.ProviderContext(None);rows,_=M.manifest_rows(None)
    reached,chain=M.statement_dependencies(None,{c.helper,"Infinite.conjectures.X0.other_helper"},rows,provider_context=context)
    print(json.dumps([sorted(reached),sorted(chain),context.diagnostics()],sort_keys=True))
finally:
    c.doCleanups()
'''
        outputs = []
        for seed in range(1, 13):
            proc = subprocess.run([sys.executable, "-B", "-c", script],
                                  cwd=Path(__file__).resolve().parents[1],
                                  env={**os.environ, "PYTHONHASHSEED": str(seed)},
                                  capture_output=True, text=True)
            self.assertEqual(proc.returncode, 0, proc.stderr)
            outputs.append(proc.stdout)
        self.assertEqual(len(set(outputs)), 1)

    def test_unsupported_projects_keep_old_candidates(self):
        changes = ["-Q ../infinite-graph-theory/theories Alias\n",
                   "-Q ../base/theories OtherBase\n", "-Q ../base/theories GTBase\n",
                   "-Q ../base/theories/conjectures GTBase.conjectures\n",
                   "-Q /tmp/external Infinite\n", "-I plugins\n", "-include extra.project\n",
                   "-arg -require -arg Infinite.conjectures.X0\n", "-arg -compat -arg 8.20\n"]
        for extra in changes:
            with self.subTest(extra=extra):
                self.write("chromatic-theory/_CoqProject", self.other_project + extra)
                context = REPORT.ProviderContext(None)
                self.assertTrue(context.possible(self.other, self.source))
                self.assertTrue(context.diagnostics())
                if extra.startswith("-include"):
                    with self.assertRaises(REPORT.RegistryError):
                        self.dependencies()
                else:
                    self.assertIn(self.other_statement, self.dependencies())

    def test_noncanonical_mapping_spelling_cannot_hide_symlink_traversal(self):
        self.assertFalse(REPORT.ProviderContext(None).possible(self.other, self.source))
        self.assertFalse(REPORT.ProviderContext(self.baseline).possible(self.other, self.source))
        with tempfile.TemporaryDirectory() as temporary:
            outside = Path(temporary)
            (outside / "inner").mkdir()
            (outside / "base/theories").mkdir(parents=True)
            (self.root / "redirect").symlink_to(outside / "inner", target_is_directory=True)
            for spelling in ("../redirect/../base/theories", "../base/./theories",
                             "../base/theories/", "../base//theories"):
                with self.subTest(spelling=spelling):
                    self.write("chromatic-theory/_CoqProject",
                               self.other_project.replace("../base/theories", spelling))
                    if "redirect" in spelling:
                        self.assertNotEqual((self.root / "chromatic-theory" / spelling).resolve(),
                                            (self.root / "base/theories").resolve())
                    pin = self.commit()
                    for commit in (None, pin):
                        context = REPORT.ProviderContext(commit)
                        self.assertTrue(context.possible(self.other, self.source))
                        self.assertTrue(context.diagnostics())
            self.write("chromatic-theory/_CoqProject", self.other_project)
            self.assertFalse(REPORT.ProviderContext(None).possible(self.other, self.source))

    def test_loader_commands_and_ambient_overrides_keep_old_candidates(self):
        original = (self.root / self.other).read_text()
        for command in ('Load "fragment".', 'Time Add LoadPath "../infinite-graph-theory/theories" as Infinite.',
                        'Remove LoadPath "old".', 'Declare ML Module "plugin".'):
            with self.subTest(command=command):
                self.write(self.other, command + "\n" + original)
                context = REPORT.ProviderContext(None)
                self.assertTrue(context.possible(self.other, self.source))
                self.assertTrue(context.diagnostics())
        self.write(self.other, original)
        for name in ("COQPATH", "ROCQPATH", "COQLIB", "COQFLAGS", "ROCQ_UNKNOWN_LOADER"):
            with self.subTest(environment=name), patch.dict(os.environ, {name:"hidden"}):
                context = REPORT.ProviderContext(None)
                self.assertTrue(context.possible(self.other, self.source))
                self.assertTrue(context.diagnostics())
                self.assertIn(self.other_statement, self.dependencies())
        self.assertFalse(REPORT.ProviderContext(None).possible(self.other, self.source))

    def test_unlisted_or_missing_local_requires_keep_candidates(self):
        self.write("chromatic-theory/theories/hidden.v", "Definition hidden : True := I.\n")
        original = (self.root / self.other).read_text()
        for command in ("Require Chromatic.hidden.", "From Chromatic Require Import hidden.",
                        "From Chromatic Require Import absent.", "Require hidden.",
                        "Require conjectures.hidden.", "Time Require Chromatic.hidden."):
            with self.subTest(command=command):
                self.write(self.other, command + "\n" + original)
                context = REPORT.ProviderContext(None)
                self.assertTrue(context.possible(self.other, self.source))
                self.assertTrue(context.diagnostics())
                self.assertIn(self.other_statement, self.dependencies())
        self.write(self.other, original)
        # An unrelated deferred source is not itself a reason to fall back.
        self.assertFalse(REPORT.ProviderContext(None).possible(self.other, self.source))

    def test_recursive_project_require_keeps_all_suffix_candidates(self):
        original = (self.root / self.other).read_text()
        self.write(self.other, "Require Chromatic.X1.\n" + original)
        self.assertFalse(REPORT.ProviderContext(None).possible(self.other, self.source))
        self.write("chromatic-theory/theories/other/X1.v", "Definition hidden := True.\n")
        context = REPORT.ProviderContext(None)
        self.assertTrue(context.possible(self.other, self.source))
        self.assertTrue(context.diagnostics())
        self.write("chromatic-theory/_CoqProject", self.other_project + "theories/other/X1.v\n")
        self.assertFalse(REPORT.ProviderContext(None).possible(self.other, self.source))

    def test_masking_warning_lists_and_non_loader_settings(self):
        original = (self.root / self.other).read_text()
        self.write(self.other, '(* Load "bad". (* nested *) *)\n' + original)
        self.write("chromatic-theory/_CoqProject", self.other_project +
                   "-arg -w -arg -notation-overridden,-ambiguous-paths,-deprecated\n")
        with patch.dict(os.environ, {"ROCQ_STEP_TIMEOUT":"30", "ROCQ_QED_TIMEOUT":"180"}):
            self.assertFalse(REPORT.ProviderContext(None).possible(self.other, self.source))
        self.write(self.other, 'Definition quoted := "Add LoadPath ""bad""".\n' + original)
        self.assertFalse(REPORT.ProviderContext(None).possible(self.other, self.source))
        self.write(self.other, 'Definition quoted := "unterminated.\n' + original)
        self.assertTrue(REPORT.ProviderContext(None).possible(self.other, self.source))

    def test_non_regular_missing_and_cross_root_contexts_do_not_prune(self):
        self.assertFalse(REPORT.ProviderContext(None).possible(self.other, self.source))
        path = self.root / "chromatic-theory/_CoqProject"
        text = path.read_text()
        path.unlink()
        self.assertTrue(REPORT.ProviderContext(None).possible(self.other, self.source))
        self.write("hidden.project", text)
        path.symlink_to(self.root / "hidden.project")
        pin = self.commit()
        self.assertTrue(REPORT.ProviderContext(None).possible(self.other, self.source))
        self.assertTrue(REPORT.ProviderContext(pin).possible(self.other, self.source))
        path.unlink(); path.write_text(text)
        source = self.root / self.source
        saved = source.read_text(); source.unlink()
        self.write("hidden.v", saved); source.symlink_to(self.root / "hidden.v")
        self.assertTrue(REPORT.ProviderContext(None).possible(self.other, self.source))
        with tempfile.TemporaryDirectory() as other, patch.object(REPORT, "ROOT", Path(other)):
            self.assertTrue(REPORT.ProviderContext(None).possible(self.other, self.source))

    def test_source_audit_does_not_call_rocq_and_diagnostics_are_returned(self):
        original = subprocess.run
        def only_source_commands(args, *rest, **kwargs):
            self.assertEqual(args[0], "git")
            return original(args, *rest, **kwargs)
        with patch.object(REPORT.subprocess, "run", side_effect=only_source_commands):
            self.assertEqual(self.failures(), [])
            with patch.dict(os.environ, {"COQPATH":"unknown"}):
                result = self.report()
                self.assertFalse(result["ok"])
                self.assertTrue(result["provider_context_fallbacks"])
                self.assertTrue(any(c["path"] == self.other for c in result["consumers"]))

    @unittest.skipUnless(KERNEL, "requires --kernel")
    def test_real_compiled_distinct_providers_and_external_transitive_wrapper(self):
        env = REPORT.ROCQ.environment()
        def compile(path, extra=()):
            proc = subprocess.run(["coqc", "-Q", "base/theories", "GTBase", "-R",
                "infinite-graph-theory/theories", "Infinite", "-R", "chromatic-theory/theories", "Chromatic",
                *extra, path], cwd=self.root, env=env, text=True, capture_output=True)
            self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        for path in ("base/theories/common.v", self.source, self.certificate, self.other, self.other_cert):
            compile(path)
        self.assertEqual(REPORT.check_kernel(self.spec), [])
        self.assertEqual(self.dependencies(), {self.statement})
        self.write("external/relay.v", "Require Export Infinite.conjectures.X0.\n")
        compile("external/relay.v", ("-Q", "external", "External"))
        self.write(self.other, "From External Require Import relay.\n"
                   "Definition foreign_statement : Prop := local_helper 0.\n"
                   "Lemma binding : foreign_statement <-> Infinite.conjectures.X0.local_helper 0.\n"
                   "Proof. exact (iff_refl _). Qed.\n")
        self.write("chromatic-theory/_CoqProject", self.other_project + "-Q ../infinite-graph-theory/theories Infinite\n")
        compile(self.other, ("-Q", "external", "External"))
        self.assertIn(self.other_statement, self.dependencies())


class SourceCacheTests(unittest.TestCase):
    """Warm caches must preserve fresh report/provenance checks and errors."""

    setUp = ReportTests.setUp
    write = ReportTests.write
    write_json = ReportTests.write_json
    command = ReportTests.command
    commit = ReportTests.commit
    write_manifests = ReportTests.write_manifests
    report = ReportTests.report
    failures = ReportTests.failures

    caches = ("_full_commit", "_historical_source", "_historical_blob",
              "_inventory_index", "_declarations")

    @contextlib.contextmanager
    def uncached(self):
        with contextlib.ExitStack() as stack:
            for name in self.caches:
                stack.enter_context(patch.object(REPORT, name, getattr(REPORT, name).__wrapped__))
            yield

    def test_report_bytes_and_duplicate_read_reduction(self):
        for name in self.caches:
            getattr(REPORT, name).cache_clear()
        with patch.object(REPORT, "_git_at", wraps=REPORT._git_at) as reads:
            cold = self.report()
            cold_calls = reads.call_count
            reads.reset_mock()
            warm = self.report()
            warm_calls = reads.call_count
            reads.reset_mock()
            with self.uncached():
                original = self.report()
            uncached_calls = reads.call_count
        self.assertEqual(self.failures(), [])
        self.assertEqual(cold, warm)
        self.assertEqual(warm, original)
        self.assertLess(warm_calls, cold_calls)
        self.assertLess(cold_calls, uncached_calls)
        self.assertEqual(json.dumps(warm, sort_keys=True), json.dumps(original, sort_keys=True))
        for renderer in (REPORT.render_markdown, REPORT.render_details):
            self.assertEqual(renderer(warm, self.spec), renderer(original, self.spec))
        warm["checks"].clear()
        self.assertEqual(self.report(), original)

    def test_live_edits_with_restored_mtime_remain_fresh(self):
        self.assertEqual(self.failures(), [])
        path = self.root / self.certificate
        old = path.stat()
        path.write_text(self.cert_source.replace(":= n = n.", ":= n = 0."))
        os.utime(path, ns=(old.st_atime_ns, old.st_mtime_ns))
        self.assertTrue(self.failures())
        self.write(self.certificate, self.cert_source)
        self.assertEqual(self.failures(), [])
        self.write(self.source, self.live.replace("canonical n", "canonical 0"))
        self.assertTrue(self.failures())

    def test_current_registry_and_manifest_remain_fresh(self):
        self.assertEqual(self.failures(), [])
        self.row["status"] = "changed"
        self.write_manifests("v2")
        self.assertTrue(self.failures())
        self.row["status"] = "open"
        self.write_manifests("v2")
        self.assertEqual(self.failures(), [])
        path = self.root / "meta/library_primitives/test-family.json"
        registry = json.loads(path.read_text())
        registry["primitive"]["source_definitions"] = []
        path.write_text(json.dumps(registry))
        self.assertTrue(self.failures())

    def test_parser_returns_fresh_containers_and_keys_by_text(self):
        expected = REPORT.declarations(self.original)
        result = REPORT.declarations(self.original)
        result[0]["name"] = "corrupted"
        result.clear()
        self.assertEqual(REPORT.declarations(self.original), expected)
        changed = self.original.replace("n = n", "n = 0")
        self.assertNotEqual(REPORT.declarations(changed), expected)
        with patch.object(REPORT.INV, "strip_comments", wraps=REPORT.INV.strip_comments) as parse:
            REPORT.declarations(self.original)
            REPORT.declarations(self.original)
            self.assertEqual(parse.call_count, 0)

    def test_moving_refs_and_different_commits(self):
        self.command("git", "tag", "moving")
        for ref in ("HEAD", "moving", self.baseline):
            self.assertEqual(REPORT.source_at(ref, self.source), self.original)
        changed = self.original.replace("n = n", "n = 0")
        self.write(self.source, changed)
        current = self.commit()
        self.command("git", "tag", "-f", "moving")
        for ref in ("HEAD", "moving", current):
            self.assertEqual(REPORT.source_at(ref, self.source), changed)
        self.assertEqual(REPORT.source_at(self.baseline, self.source), self.original)
        self.assertNotEqual(REPORT.blob_at(current, self.source),
                            REPORT.blob_at(self.baseline, self.source))

    def test_cross_root_missing_objects_do_not_hit_other_repository(self):
        REPORT.source_at(self.baseline, self.source)
        other = self.root / "other"
        other.mkdir()
        self.command("git", "-C", str(other), "init", "-q")
        with patch.object(REPORT, "ROOT", other):
            with self.assertRaises(subprocess.CalledProcessError):
                REPORT.source_at(self.baseline, self.source)

    def test_tree_expression_retains_original_git_semantics(self):
        tree = self.command("git", "rev-parse", self.baseline + "^{tree}")
        self.assertEqual(REPORT.source_at(tree, self.source), self.original)
        self.assertEqual(REPORT.blob_at(tree, self.source),
                         REPORT.git("rev-parse", tree + ":" + self.source).strip())
        self.assertEqual(REPORT.inventory_hash(tree, self.helper),
                         REPORT.inventory_hash(self.baseline, self.helper))

    def test_alternate_object_store_changes_retain_git_errors(self):
        other = self.root / "alternate"
        self.command("git", "clone", "--shared", "-q", str(self.root), str(other))
        with patch.object(REPORT, "ROOT", other):
            self.assertEqual(REPORT.source_at(self.baseline, self.source), self.original)
            (other / ".git/objects/info/alternates").write_text("/missing-object-store\n")
            with self.assertRaises(subprocess.CalledProcessError):
                REPORT.source_at(self.baseline, self.source)

    def test_git_indirection_retargeting_and_replacement_refs(self):
        other = self.root / "other"
        self.command("git", "clone", "-q", str(self.root), str(other))
        self.write(self.source, self.original.replace("n = n", "n = 0"))
        changed = self.commit()
        self.command("git", "-C", str(other), "fetch", "-q", str(self.root), changed)
        self.command("git", "-C", str(other), "replace", self.baseline, changed)
        alias = self.root / "alias"
        alias.mkdir()
        pointer = alias / ".git"
        pointer.write_text("gitdir: " + str(self.root / ".git") + "\n")
        with patch.object(REPORT, "ROOT", alias):
            self.assertEqual(REPORT.source_at(self.baseline, self.source), self.original)
            pointer.write_text("gitdir: " + str(other / ".git") + "\n")
            self.assertEqual(REPORT.source_at(self.baseline, self.source),
                             REPORT.git("show", f"{self.baseline}:{self.source}"))
            self.assertNotEqual(REPORT.source_at(self.baseline, self.source), self.original)

    def test_object_directory_override_and_failed_reads_are_not_cached(self):
        REPORT.source_at(self.baseline, self.source)
        empty = self.root / "empty-objects"
        empty.mkdir()
        with patch.dict(os.environ, {"GIT_OBJECT_DIRECTORY": str(empty)}):
            with self.assertRaises(subprocess.CalledProcessError):
                REPORT.source_at(self.baseline, self.source)
            with self.assertRaises(subprocess.CalledProcessError):
                REPORT.blob_at(self.baseline, self.source)
        missing = "new-ref"
        with self.assertRaises(subprocess.CalledProcessError):
            REPORT.source_at(missing, self.source)
        self.command("git", "branch", missing, self.baseline)
        self.assertEqual(REPORT.source_at(missing, self.source), self.original)
        with patch.object(REPORT, "_git_at", wraps=REPORT._git_at) as reads:
            for _ in range(2):
                with self.assertRaises(subprocess.CalledProcessError):
                    REPORT.source_at(self.baseline, "absent.v")
            self.assertEqual(reads.call_count, 2)

    def test_loose_and_packed_replacements_bypass_warm_caches(self):
        old_hash = REPORT.inventory_hash(self.baseline, self.helper)
        old_blob = REPORT.blob_at(self.baseline, self.source)
        REPORT.source_at(self.baseline, self.source)
        changed = self.original.replace("n = n", "n = 0")
        self.write(self.source, changed)
        self.write_json("meta/library_helper_inventory.json", {"helpers": [{
            "qualified_name": self.helper, "declaration_hash": "changed"}]})
        replacement = self.commit()
        self.command("git", "replace", self.baseline, replacement)
        for packed in (False, True):
            if packed:
                self.command("git", "pack-refs", "--all", "--prune")
                shutil.rmtree(self.root / ".git/refs/replace")
            self.assertEqual(REPORT.source_at(self.baseline, self.source), changed)
            self.assertEqual(REPORT.inventory_hash(self.baseline, self.helper), "changed")
            self.assertNotEqual(REPORT.blob_at(self.baseline, self.source), old_blob)
        self.command("git", "replace", "-d", self.baseline)
        self.assertEqual(REPORT.inventory_hash(self.baseline, self.helper), old_hash)
        self.assertEqual(REPORT.source_at(self.baseline, self.source), self.original)

    def test_inventory_first_match_and_original_error_order(self):
        path = "meta/library_helper_inventory.json"
        good = {"qualified_name": self.helper, "declaration_hash": "first"}
        cases = ([good, dict(good, declaration_hash="second")], [good, None],
                 [None, good], [{"qualified_name": self.helper}],
                 [{"qualified_name": "other"}, good])
        for helpers in cases:
            with self.subTest(helpers=helpers):
                self.write_json(path, {"helpers": helpers})
                pin = self.commit()
                try:
                    with self.uncached():
                        expected = REPORT.inventory_hash(pin, self.helper)
                except (TypeError, KeyError) as error:
                    for _ in range(2):
                        with self.assertRaises(type(error)):
                            REPORT.inventory_hash(pin, self.helper)
                else:
                    self.assertEqual(REPORT.inventory_hash(pin, self.helper), expected)
                    self.assertEqual(REPORT.inventory_hash(pin, self.helper), expected)
        self.write(path, "invalid json")
        pin = self.commit()
        for _ in range(2):
            with self.assertRaises(json.JSONDecodeError):
                REPORT.inventory_hash(pin, self.helper)


class ParametricStatementTests(unittest.TestCase):
    """An explicitly enrolled Section-parametric whole Prop with a same-Section companion."""

    write = ReportTests.write
    write_json = ReportTests.write_json
    command = ReportTests.command
    write_manifests = ReportTests.write_manifests
    report = ReportTests.report
    failures = ReportTests.failures
    rebaseline = ReportTests.rebaseline
    register = FrozenRoleTests.register
    commit = AdditionalStatementTests.commit
    assert_invalid = AdditionalStatementTests.assert_invalid

    NAT = "Corelib.Init.Datatypes.nat"
    VARIABLES = ["Variable P : nat -> Prop.", "Variable Q : nat -> Prop.", "Variable unused : nat."]
    SCAFFOLD = "Variable P : nat -> Prop.\nVariable Q : nat -> Prop.\nVariable unused : nat.\n"

    def setUp(self):
        ReportTests.setUp(self)
        self.middle_path = "base/theories/conjectures/X1.v"
        self.schema_path = "base/theories/conjectures/X2.v"
        self.schema = "GTBase.conjectures.X2.schema_claim"
        self.middle_text = ("From GTBase.conjectures Require Import X0.\n"
                            "Definition middle (n : nat) : Prop := local_helper n.\n")
        self.closed_text = "Definition closed : Prop := forall n, P n -> Q n.\n"
        self.claim_text = ("(** A Section-parametric whole conjecture. *)\n"
                           "Definition schema_claim : Prop := closed -> forall n, middle n /\\ P n.\n")
        self.schema_text = self.schema_source()
        self.write(self.middle_path, self.middle_text)
        self.write(self.schema_path, self.schema_text)
        project = self.root / "base/_CoqProject"
        project.write_text(project.read_text() + "theories/conjectures/X1.v\ntheories/conjectures/X2.v\n")
        self.binding = "(@GTBase.conjectures.X2.closed P Q)"
        self.frozen_claim = ("Definition schema_claim : Prop := " + self.binding
                             + " -> forall n, MiddleLegacy.middle n /\\ P n.\n")
        self.shape_claim = ("Definition schema_claim_live_shape : Prop := " + self.binding
                            + " -> forall n, middle n /\\ P n.\n")
        self.cert_base = self.cert_source
        self.cert_source = self.cert_base + self.certificate_tail()
        self.write(self.certificate, self.cert_source)
        self.spec["parametric_statements"] = [{
            "qualified": self.schema, "section": "Schema", "variables": list(self.VARIABLES),
            "parameters": [{"name": "P", "kernel_type": self.NAT + " -> Prop"},
                           {"name": "Q", "kernel_type": self.NAT + " -> Prop"}],
            "bindings": {"closed": ["P", "Q"]},
            "live_shape": self.module + ".schema_claim_live_shape"}]
        self.spec["frozen"].extend([
            {"kind": "chain", "qualified": "GTBase.conjectures.X1.middle",
             "path": self.middle_path, "name": "middle", "frozen_path": self.certificate,
             "frozen": "MiddleLegacy.middle", "certificate": self.module + ".middle_compat",
             "substitutions": {"local_helper": "Legacy.local_helper"}},
            {"kind": "statement", "qualified": self.schema, "path": self.schema_path,
             "name": "schema_claim", "frozen_path": self.certificate,
             "frozen": "SchemaLegacy.schema_claim", "certificate": self.module + ".schema_compat",
             "non_corpus": True,
             "substitutions": {"middle": "MiddleLegacy.middle", "closed": self.binding}},
        ])
        self.spec["cross_module_consumers"] = [
            {"path": self.middle_path, "name": "local_helper", "note": "intermediary"},
            {"path": self.schema_path, "name": "middle", "note": "whole Prop"},
        ]
        self.register("middle_compat")
        self.register("schema_compat")
        self.rebaseline()

    def schema_source(self, scaffold=None, claim=None, closed=None, before="", inside="", after=""):
        return ("From GTBase.conjectures Require Import X1.\n" + before + "Section Schema.\n"
                + (self.SCAFFOLD if scaffold is None else scaffold)
                + (self.closed_text if closed is None else closed) + inside
                + (self.claim_text if claim is None else claim) + "End Schema.\n" + after)

    def certificate_tail(self, frozen=None, shape=None, legacy_scaffold=None, shape_scaffold=None,
                         compat=None, between=""):
        frozen = self.frozen_claim if frozen is None else frozen
        shape = self.shape_claim if shape is None else shape
        legacy_scaffold = self.SCAFFOLD if legacy_scaffold is None else legacy_scaffold
        shape_scaffold = self.SCAFFOLD if shape_scaffold is None else shape_scaffold
        compat = (compat if compat is not None else
                  "Lemma schema_compat (P Q : nat -> Prop) :\n"
                  "  SchemaLegacy.schema_claim P Q <-> GTBase.conjectures.X2.schema_claim P Q.\n"
                  "Proof. split; intro h; exact h. Qed.\n")
        return ("From GTBase.conjectures Require Import X1 X2.\n"
                "Module MiddleLegacy.\n"
                "Definition middle (n : nat) : Prop := Legacy.local_helper n.\n"
                "End MiddleLegacy.\n"
                "Module SchemaLegacy.\nSection Schema.\n" + legacy_scaffold + frozen
                + "End Schema.\nEnd SchemaLegacy.\n" + between
                + "Section Schema.\n" + shape_scaffold + shape + "End Schema.\n"
                + "Lemma middle_compat (n : nat) : MiddleLegacy.middle n <-> middle n.\n"
                "Proof. split; trivial. Qed.\n" + compat)

    def set_certificate(self, **parts):
        self.cert_source = self.cert_base + self.certificate_tail(**parts)
        self.write(self.certificate, self.cert_source)

    def entry(self):
        return self.spec["parametric_statements"][0]

    def statement_object(self):
        return next(o for o in self.spec["frozen"] if o.get("qualified") == self.schema)

    def at_both_pins(self, source, match):
        for baseline in (False, True):
            with self.subTest(source=source, baseline=baseline):
                self.write(self.schema_path, source)
                if baseline:
                    self.rebaseline()
                    self.write(self.schema_path, self.schema_text)
                self.assert_invalid(match)
                self.write(self.schema_path, self.schema_text)
                self.rebaseline()

    def compile_fixture(self, extra=()):
        for source in ("common", "conjectures/X0", "conjectures/X1", "conjectures/X2", *extra,
                       "migration/test_family"):
            proc = subprocess.run(["coqc", "-Q", "theories", "GTBase", "theories/" + source + ".v"],
                                  cwd=self.root / "base", env=REPORT.ROCQ.environment(),
                                  text=True, capture_output=True)
            self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)

    # Positive cases and non-weakening.

    def test_parametric_whole_prop_with_binding_passes(self):
        self.assertEqual(self.failures(), [])
        report = self.report()
        row = next(s for s in report["statements"] if s["qualified"] == self.schema)
        self.assertEqual([p["name"] for p in row["parameters"]], ["P", "Q"])
        self.assertEqual(row["bindings"], {"closed": ["P", "Q"]})
        self.assertIn("Section-parametric", REPORT.render_markdown(report, {**self.spec, "report_name": "x"}))
        rows, _ = REPORT.manifest_rows(self.spec["baseline_commit"])
        found, path = REPORT.statement_dependencies(self.spec["baseline_commit"], {self.helper}, rows,
                                                   additional_statements={self.schema})
        self.assertEqual(found, {self.statement, self.schema})
        self.assertNotIn("GTBase.conjectures.X2.closed", path)

    def test_unbound_parametric_prop_passes(self):
        claim = ("(** An unbound Section-parametric conjecture. *)\n"
                 "Definition schema_claim : Prop := forall n, middle n /\\ P n.\n")
        self.schema_text = self.schema_source(claim=claim)
        self.write(self.schema_path, self.schema_text)
        self.set_certificate(
            frozen="Definition schema_claim : Prop := forall n, MiddleLegacy.middle n /\\ P n.\n",
            shape="Definition schema_claim_live_shape : Prop := forall n, middle n /\\ P n.\n",
            compat="Lemma schema_compat (P : nat -> Prop) :\n"
                   "  SchemaLegacy.schema_claim P <-> GTBase.conjectures.X2.schema_claim P.\n"
                   "Proof. split; intro h; exact h. Qed.\n")
        self.entry()["parameters"] = self.entry()["parameters"][:1]
        self.entry()["bindings"] = {}
        del self.statement_object()["substitutions"]["closed"]
        self.rebaseline()
        self.assertEqual(self.failures(), [])

    def test_masked_scope_strings_and_other_scopes_outside_the_section_pass(self):
        self.schema_text = self.schema_source(
            before='Redirect "Section Schema" Check nat.\nModule Other.\nSection Schema.\nEnd Schema.\nEnd Other.\n',
            scaffold="Variable P : nat -> Prop.\n(* End Schema. *)\nVariable Q : nat -> Prop.\nVariable unused : nat.\n",
            after='Redirect "End Schema" Check nat.\n')
        self.write(self.schema_path, self.schema_text)
        self.rebaseline()
        self.assertEqual(self.failures(), [])
        # Two commands on one line are not a wrapped scope (same rule as the
        # nullary scanner): the Section opener is a real top-level scope.
        self.schema_text = self.schema_source().replace("Section Schema.\n", "Check nat. Section Schema.\n", 1)
        self.write(self.schema_path, self.schema_text)
        self.rebaseline()
        self.assertEqual(self.failures(), [])

    def test_nullary_enrollment_still_rejects_the_section_prop(self):
        del self.spec["parametric_statements"]
        self.spec["additional_statements"] = [self.schema]
        self.assert_invalid("outside Module/Section scopes")

    def test_section_prop_is_never_enrolled_by_its_type(self):
        del self.spec["parametric_statements"]
        self.assertIn("affected statement coverage matches baseline dependencies", self.failures())

    # Schema, parameters, bindings and substitutions.

    def test_parametric_schema_is_strict(self):
        original = copy.deepcopy(self.entry())
        cases = [
            None, {}, "x",
            {**original, "extra": 1},
            {key: value for key, value in original.items() if key != "bindings"},
            {**original, "qualified": "bare"},
            {**original, "section": "bad-label"},
            {**original, "parameters": []},
            {**original, "parameters": original["parameters"] + [original["parameters"][0]]},
            {**original, "variables": ["Variables P Q : nat -> Prop."]},
            {**original, "bindings": {"closed": "P"}},
            {**original, "live_shape": self.module + ".schema_claim_shape"},
            {**original, "live_shape": "GTBase.elsewhere.schema_claim_live_shape"},
        ]
        for kernel_type in ("_ -> Prop", "nat -> Prop", "P -> Prop", "forall x : " + self.NAT + ", Prop",
                            self.NAT + " -> Prop%type", ""):
            cases.append({**original, "parameters": [{"name": "P", "kernel_type": kernel_type},
                                                     original["parameters"][1]]})
        for value in cases:
            with self.subTest(value=value):
                self.spec["parametric_statements"] = [value]
                self.assert_invalid("parametric|live_shape|kernel_type")
        self.spec["parametric_statements"] = [original, copy.deepcopy(original)]
        self.assert_invalid("unique qualified")
        self.spec["parametric_statements"] = {"x": original}
        self.assert_invalid("must be a list")
        self.spec["parametric_statements"] = [original]
        self.spec["additional_statements"] = [self.schema]
        # The unchanged nullary validator rejects this Section Prop first; the
        # separate list's own disjointness rule is checked directly as well.
        self.assert_invalid("outside Module/Section scopes")
        with self.assertRaisesRegex(ValueError, "disjoint"):
            REPORT.parametric_statement_entries(self.spec)

    def test_omitted_extra_or_reordered_parameters_are_rejected(self):
        p, q = self.entry()["parameters"]
        unused = {"name": "unused", "kernel_type": self.NAT}
        for parameters in ([p], [q, p], [p, q, unused], [q]):
            with self.subTest(parameters=parameters):
                self.entry()["parameters"] = parameters
                self.assert_invalid("parameters must be exactly")
        self.entry()["parameters"] = [p, q]

    def test_variables_must_be_the_complete_reviewed_scaffold(self):
        for variables in (self.VARIABLES[:2], [self.VARIABLES[1], self.VARIABLES[0], self.VARIABLES[2]],
                          ["Variable P : Corelib.Init.Datatypes.nat -> Prop."] + self.VARIABLES[1:]):
            with self.subTest(variables=variables):
                self.entry()["variables"] = variables
                self.assert_invalid("scaffold differs")
        self.entry()["variables"] = list(self.VARIABLES)

    def test_bindings_are_exact_ordered_and_generated(self):
        for bindings, match in (({"closed": ["Q", "P"]}, "Section order"),
                                ({"closed": ["P", "R"]}, "Section order"),
                                ({"closed": ["P", "P", "Q"]}, "Section order"),
                                ({}, "bindings must name exactly"),
                                ({"closed": ["P", "Q"], "middle": []}, "bindings must name exactly"),
                                ({"closed": ["P"]}, "parameters must be exactly|generated")):
            with self.subTest(bindings=bindings):
                self.entry()["bindings"] = bindings
                self.assert_invalid(match)
        self.entry()["bindings"] = {"closed": ["P", "Q"]}
        substitutions = self.statement_object()["substitutions"]
        for value in ("(@GTBase.conjectures.X2.closed P (fun _ => True))", "(@GTBase.conjectures.X1.middle)",
                      "(@GTBase.conjectures.X2.closed Q P)", "GTBase.conjectures.X2.closed P Q", None):
            with self.subTest(value=value):
                if value is None:
                    del substitutions["closed"]
                else:
                    substitutions["closed"] = value
                self.assert_invalid("must be the generated")
                substitutions["closed"] = self.binding

    def test_substitutions_cannot_capture_parameters_or_bypass_bindings(self):
        substitutions = self.statement_object()["substitutions"]
        for key, value, match in (("P", "(fun _ => True)", "cannot replace Section variable"),
                                  ("unused", "0", "cannot replace Section variable"),
                                  ("middle", "(fun n => P n)", "cannot mention Section variables")):
            with self.subTest(key=key, value=value):
                saved = dict(substitutions)
                substitutions[key] = value
                self.assert_invalid(match)
                substitutions.clear()
                substitutions.update(saved)

    # Scopes, Section commands and dependent scaffolds.

    def test_scope_shapes_are_rejected_at_both_pins(self):
        body = self.SCAFFOLD + self.closed_text + self.claim_text
        header = "From GTBase.conjectures Require Import X1.\n"
        cases = {
            header + "Module M.\nSection Schema.\n" + body + "End Schema.\nEnd M.\n": "directly in top-level Section",
            header + "Module F (X : Sig).\nSection Schema.\n" + body + "End Schema.\nEnd F.\n": "directly in top-level Section",
            header + "Module Type T.\nSection Schema.\n" + body + "End Schema.\nEnd T.\n": "directly in top-level Section",
            header + "Section Outer.\nSection Schema.\n" + body + "End Schema.\nEnd Outer.\n": "directly in top-level Section",
            header + self.SCAFFOLD.replace("Variable", "Parameter") + self.claim_text.replace("closed -> ", ""): "directly in top-level Section",
            header + "Time Section Schema.\n" + body + "End Schema.\n": "wrapped scope",
            header + "Timeout 5 Section Schema.\n" + body + "End Schema.\n": "wrapped scope",
            header + 'Redirect "f" Section Schema.\n' + body + "End Schema.\n": "wrapped scope",
            header + 'Load "fragment".\nSection Schema.\n' + body + "End Schema.\n": "source-splicing Load",
            header + "Section Schema.\nEnd Schema.\nSection Schema.\n" + body + "End Schema.\n": "exactly one top-level scope",
            header + "Module Schema.\nEnd Schema.\nSection Schema.\n" + body + "End Schema.\n": "exactly one top-level scope",
            header + "Section Schema.\n" + body + "End Schema.\nSection Schema.\nEnd Schema.\n": "exactly one top-level scope",
            header + "Section Schema.\n" + body: "unclosed",
            header + "Section Other.\n" + body + "End Other.\n": "directly in top-level Section Schema",
        }
        for source, match in cases.items():
            self.at_both_pins(source, match)

    def test_section_command_whitelist_is_not_bypassed(self):
        for command in ('Redirect "End Schema" Check nat.\n', "Hypothesis h : forall n, P n.\n",
                        "Variables (R S : nat -> Prop).\n", "Let k := 0.\n", "Context (R : nat).\n",
                        "Local Definition k := 0.\n", "#[local] Definition k := 0.\n",
                        "Local Notation k := 0.\n", "Implicit Types n : nat.\n",
                        "Fixpoint k (n : nat) : nat := n.\n", 'Redirect "f" Variable R : nat.\n',
                        "Lemma k : True.\nProof. exact I. Qed.\n"):
            self.at_both_pins(self.schema_source(inside=command), "unsupported Section command")

    def test_dependent_scaffolds_are_rejected(self):
        # The reviewed variables match the source at both pins, so only the
        # dependency rule can reject: Rocq would discharge T through P's type.
        cases = (("Variable T : Type.\nVariable P : T -> Prop.\nVariable Q : nat -> Prop.\nVariable unused : nat.\n",
                  ["Variable T : Type.", "Variable P : T -> Prop.", *self.VARIABLES[1:]]),
                 ("Variable P : nat -> Prop.\nVariable Q : nat -> Prop.\nDefinition U := nat.\nVariable unused : U.\n",
                  [*self.VARIABLES[:2], "Variable unused : U."]))
        for scaffold, variables in cases:
            for parameters in (self.entry()["parameters"],
                               [{"name": "T", "kernel_type": "Type"}, *self.entry()["parameters"]]):
                with self.subTest(scaffold=scaffold, parameters=parameters):
                    saved = copy.deepcopy(self.entry())
                    self.entry().update(variables=variables, parameters=parameters)
                    self.write(self.schema_path, self.schema_source(scaffold=scaffold))
                    self.rebaseline()
                    self.assert_invalid("dependent Section variable")
                    self.spec["parametric_statements"] = [saved]
                    self.write(self.schema_path, self.schema_text)
                    self.rebaseline()

    # Lost hypotheses, frozen copy and witness placement, history.

    def test_lost_hypotheses_are_rejected_everywhere(self):
        self.write(self.schema_path, self.schema_text.replace("closed -> ", ""))
        self.assert_invalid("bindings must name exactly")
        self.write(self.schema_path, self.schema_text)
        self.set_certificate(frozen=self.frozen_claim.replace(self.binding + " -> ", ""))
        self.assertTrue(any("frozen copy SchemaLegacy.schema_claim matches" in f for f in self.failures()))
        self.set_certificate(shape=self.shape_claim.replace(self.binding + " -> ", ""))
        self.assertIn(self.schema + ": live-shape witness matches the original modulo generated bindings",
                      self.failures())

    def test_frozen_copy_and_witness_placement(self):
        frozen_label = self.schema + ": frozen copy SchemaLegacy.schema_claim lies in its Section scaffold"
        shape_label = self.schema + ": live-shape witness schema_claim_live_shape lies in its top-level Section scaffold"
        legacy = ("Module SchemaLegacy.\nSection Schema.\n" + self.SCAFFOLD + self.frozen_claim
                  + "End Schema.\nEnd SchemaLegacy.\n")
        top = "Section Schema.\n" + self.SCAFFOLD + self.shape_claim + "End Schema.\n"
        cases = [
            (dict(legacy_scaffold=self.SCAFFOLD.replace("Variable unused : nat.\n", "")), frozen_label),
            (dict(legacy_scaffold="Variable Q : nat -> Prop.\nVariable P : nat -> Prop.\nVariable unused : nat.\n"), frozen_label),
            (dict(legacy_scaffold=self.SCAFFOLD + "Definition extra : nat := 0.\n"), frozen_label),
            (dict(shape_scaffold=self.SCAFFOLD.replace("nat -> Prop", "Datatypes.nat -> Prop")), shape_label),
            (dict(between="Section Schema.\nEnd Schema.\n"), shape_label),
            (dict(shape="Lemma schema_claim_live_shape : Prop.\nProof. exact True. Qed.\n"), shape_label),
        ]
        for parts, label in cases:
            with self.subTest(parts=parts):
                self.set_certificate(**parts)
                self.assertIn(label, self.failures())
        for text, label in (
                (self.cert_base + self.certificate_tail().replace(legacy, legacy + "Module Again.\nEnd Again.\n")
                 .replace("Module SchemaLegacy.\nSection Schema.\n", "Module SchemaLegacy.\nSection Schema.\nEnd Schema.\nSection Schema.\n", 1), frozen_label),
                (self.cert_base + self.certificate_tail().replace(legacy, legacy.replace("Section Schema.\n", "")
                 .replace("End Schema.\n", "")), frozen_label),
                (self.cert_base + self.certificate_tail().replace(legacy, legacy.replace("Module SchemaLegacy.\n", "Module SchemaLegacy (X : Sig).\n")), frozen_label),
                (self.cert_base + self.certificate_tail().replace(top, "Module Shape.\n" + top + "End Shape.\n"), shape_label)):
            with self.subTest(text=text[-400:]):
                self.write(self.certificate, text)
                self.assertIn(label, self.failures())
        self.set_certificate()

    def test_binding_target_must_be_unchanged(self):
        self.write(self.schema_path, self.schema_source(closed="Definition closed : Prop := forall n, Q n -> P n.\n"))
        self.assert_invalid("binding target closed differs")

    def test_history_guards(self):
        baseline = self.spec["baseline_commit"]
        self.spec["baseline_commit"] = baseline[:12]
        self.assert_invalid("immutable full baseline")
        tree = self.command("git", "rev-parse", baseline + "^{tree}")
        orphan = self.command("git", "commit-tree", tree, "-m", "orphan")
        self.spec["baseline_commit"] = orphan
        self.assert_invalid("ancestor of HEAD")
        self.spec["baseline_commit"] = baseline
        self.command("git", "replace", baseline, orphan)
        self.assert_invalid("replacement refs")
        self.command("git", "replace", "-d", baseline)
        grafts = self.root / ".git/info/grafts"
        grafts.parent.mkdir(exist_ok=True)
        grafts.write_text("")
        self.assert_invalid("grafts")
        grafts.unlink()
        self.assertEqual(self.failures(), [])

    def test_corpus_name_or_non_regular_source_cannot_be_enrolled(self):
        manifest = "meta/" + REPORT.REG.CORPORA["v2"]["manifest"]
        ordinary = json.loads((self.root / manifest).read_text())
        self.write_json(manifest, {"rows": [self.row, {**self.row, "formal_name": "schema_claim"}]})
        self.assert_invalid("outside both corpus manifests")
        self.write_json(manifest, ordinary)
        target = self.root / self.schema_path
        duplicate = self.root / "schema-copy.v"
        duplicate.write_text(self.schema_text)
        target.unlink()
        target.symlink_to(duplicate)
        self.assert_invalid("missing or aliased")
        self.rebaseline()
        target.unlink()
        target.write_text(self.schema_text)
        self.assert_invalid("expected regular source blob")

    # Companion reach through resolved provider dependencies (r2 section 2).

    def relay(self, at_baseline, at_current, imported="X3"):
        relay_path = "base/theories/conjectures/X3.v"
        relay_text = ("From GTBase.conjectures Require Export X1.\n"
                      "Definition relay (n : nat) : Prop := {}.\n")
        project = self.root / "base/_CoqProject"
        if "X3.v" not in project.read_text():
            project.write_text(project.read_text() + "theories/conjectures/X3.v\n")
        closed = "Definition closed : Prop := forall n, P n -> relay n -> Q n.\n"
        source = self.schema_source(closed=closed).replace("Require Import X1.", "Require Import " + imported + ".")
        self.write(self.schema_path, source)
        self.write(relay_path, relay_text.format("middle n" if at_baseline else "n = n"))
        self.schema_text = source
        self.rebaseline()
        self.write(relay_path, relay_text.format("middle n" if at_current else "n = n"))
        self.spec["cross_module_consumers"].append({"path": relay_path, "name": "middle", "note": "relay"})

    def test_companion_reaching_sources_cross_module_is_rejected(self):
        for at_baseline, at_current in ((True, True), (False, True), (True, False)):
            with self.subTest(at_baseline=at_baseline, at_current=at_current):
                self.relay(at_baseline, at_current)
                label = self.schema + ": binding targets do not reach migrated sources at any pin"
                self.assertIn(label, self.failures())
                with patch.object(REPORT.ROCQ, "environment", side_effect=AssertionError("metadata rejected")):
                    errors = REPORT.check_kernel(self.spec)
                self.assertTrue(any("would be live chains" in error for error in errors), errors)

    def test_companion_reach_follows_re_exports(self):
        closed = "Definition closed : Prop := forall n, P n -> middle n -> Q n.\n"
        project = self.root / "base/_CoqProject"
        project.write_text(project.read_text() + "theories/conjectures/X3.v\n")
        self.write("base/theories/conjectures/X3.v", "From GTBase.conjectures Require Export X1.\n")
        self.schema_text = self.schema_source(closed=closed).replace("Require Import X1.", "Require Import X3.")
        self.write(self.schema_path, self.schema_text)
        self.rebaseline()
        self.assertIn(self.schema + ": binding targets do not reach migrated sources at any pin", self.failures())

    # Kernel probes.

    @unittest.skipUnless(KERNEL, "use --kernel for tiny compiled probes")
    def test_kernel_accepts_parametric_endpoint_and_implicit_certificate_binders(self):
        self.compile_fixture()
        self.assertEqual(REPORT.check_kernel(self.spec), [])
        self.set_certificate(compat="Lemma schema_compat {P Q : nat -> Prop} :\n"
                                    "  SchemaLegacy.schema_claim P Q <-> GTBase.conjectures.X2.schema_claim P Q.\n"
                                    "Proof. split; intro h; exact h. Qed.\n")
        self.compile_fixture()
        self.assertEqual(REPORT.check_kernel(self.spec), [])

    @unittest.skipUnless(KERNEL, "use --kernel for tiny compiled probes")
    def test_kernel_rejects_wrong_endpoint_bindings_and_shapes(self):
        live = "GTBase.conjectures.X2.schema_claim"
        compats = {
            "global form": "Lemma schema_compat :\n  (forall P Q, SchemaLegacy.schema_claim P Q) <-> (forall P Q, " + live + " P Q).\n"
                           "Proof. split; intros h P Q; apply h. Qed.\n",
            "guarded": "Lemma schema_compat (P Q : nat -> Prop) : False ->\n  (SchemaLegacy.schema_claim P Q <-> " + live + " P Q).\n"
                       "Proof. intros []. Qed.\n",
            "witness": "Lemma schema_compat :\n  SchemaLegacy.schema_claim (fun _ => True) (fun _ => True) <-> " + live + " (fun _ => True) (fun _ => True).\n"
                       "Proof. split; intro h; exact h. Qed.\n",
            "swapped binders": "Lemma schema_compat (Q P : nat -> Prop) :\n  SchemaLegacy.schema_claim P Q <-> " + live + " P Q.\n"
                               "Proof. split; intro h; exact h. Qed.\n",
            "section hypothesis": "Section Guard.\nHypothesis guard : True.\nLemma schema_compat (P Q : nat -> Prop) :\n"
                                  "  SchemaLegacy.schema_claim P Q <-> " + live + " P Q.\n"
                                  "Proof using guard. split; intro h; exact h. Qed.\nEnd Guard.\n",
        }
        for name, compat in compats.items():
            with self.subTest(name=name):
                self.set_certificate(compat=compat)
                self.compile_fixture()
                self.assertTrue(REPORT.check_kernel(self.spec))
        self.set_certificate()
        self.compile_fixture()
        self.entry()["parameters"][1]["kernel_type"] = self.NAT + " -> Corelib.Init.Datatypes.bool"
        self.assertTrue(REPORT.check_kernel(self.spec))

    @unittest.skipUnless(KERNEL, "use --kernel for tiny compiled probes")
    def test_kernel_conversion_rejects_captured_or_opaque_live_shapes(self):
        # Text checks pass, but a certificate-local definition captures the
        # witness's bare `middle` with a non-convertible meaning; only the
        # kernel conversion of the live endpoint with its witness sees that.
        tail = self.certificate_tail(between="Definition middle (n : nat) : Prop := n = n /\\ True.\n")
        tail = tail.replace("Lemma middle_compat (n : nat) : MiddleLegacy.middle n <-> middle n.",
                            "Lemma middle_compat (n : nat) : MiddleLegacy.middle n <-> GTBase.conjectures.X1.middle n.")
        self.cert_source = self.cert_base + tail
        self.write(self.certificate, self.cert_source)
        self.assertEqual(self.failures(), [])
        self.compile_fixture()
        self.assertTrue(REPORT.check_kernel(self.spec))
        # A convertible capture is semantically harmless and is accepted.
        self.set_certificate(between="Local Notation middle := MiddleLegacy.middle.\n")
        self.compile_fixture()
        self.assertEqual(REPORT.check_kernel(self.spec), [])
        # An opaque witness cannot be unfolded, so the conversion fails.
        self.set_certificate(shape="Lemma schema_claim_live_shape : Prop.\nProof. exact ("
                                   + self.binding + " -> forall n, middle n /\\ P n). Qed.\n")
        self.compile_fixture()
        self.assertTrue(REPORT.check_kernel(self.spec))
        self.set_certificate(frozen="Definition schema_claim {x : nat} : Prop := " + self.binding
                                    + " -> forall n, MiddleLegacy.middle n /\\ P n.\n",
                             compat="Lemma schema_compat (P Q : nat -> Prop) :\n"
                                    "  @SchemaLegacy.schema_claim P Q 0 <-> GTBase.conjectures.X2.schema_claim P Q.\n"
                                    "Proof. split; intro h; exact h. Qed.\n")
        self.compile_fixture()
        self.assertTrue(REPORT.check_kernel(self.spec))

    # Historical parametric snapshots (T2a) and stale scans (T3).

    def add_snapshot(self, old_claim=None, old_scaffold=None, old_closed=None):
        """Commit an older X2, then the current one; enroll the older Original."""
        old_claim = old_claim or ("(** A Section-parametric whole conjecture. *)\n"
                                  "Definition schema_claim : Prop := closed -> forall n, P n /\\ middle n.\n")
        current = self.schema_text
        self.write(self.schema_path, self.schema_source(scaffold=old_scaffold, claim=old_claim, closed=old_closed))
        self.rebaseline()
        old = self.spec["baseline_commit"]
        self.write(self.schema_path, current)
        self.rebaseline()
        self.cert_source = (self.cert_source + "Module SchemaOriginal.\nSection Schema.\n" + self.SCAFFOLD
                            + "Definition schema_claim : Prop := " + self.binding
                            + " -> forall n, P n /\\ MiddleLegacy.middle n.\n"
                            + "End Schema.\nEnd SchemaOriginal.\n"
                            + "Lemma schema_original_compat (P Q : nat -> Prop) :\n"
                            "  SchemaOriginal.schema_claim P Q <-> GTBase.conjectures.X2.schema_claim P Q.\n"
                            "Proof. split; intros h c n; destruct (h c n); split; assumption. Qed.\n")
        self.write(self.certificate, self.cert_source)
        self.register("schema_original_compat")
        self.spec["frozen"].append({
            "kind": "original-statement", "qualified": self.schema, "path": self.schema_path,
            "name": "schema_claim", "commit": old, "frozen_path": self.certificate,
            "frozen": "SchemaOriginal.schema_claim", "certificate": self.module + ".schema_original_compat",
            "non_corpus": True,
            "substitutions": {"middle": "MiddleLegacy.middle", "closed": self.binding}})
        return old
    def test_parametric_snapshot_at_an_older_commit_passes(self):
        self.add_snapshot()
        self.assertEqual(self.failures(), [])

    def test_identical_snapshot_can_share_the_frozen_copy(self):
        old = self.add_snapshot(old_claim=self.claim_text)
        self.spec["frozen"][-1].update(frozen="SchemaLegacy.schema_claim",
                                       certificate=self.module + ".schema_compat")
        self.assertEqual(self.failures(), [])
        self.assertTrue(old)

    def test_parametric_snapshot_guards(self):
        old = self.add_snapshot()
        snapshot = self.spec["frozen"][-1]
        tree = self.command("git", "rev-parse", old + "^{tree}")
        for commit, match in ((self.spec["baseline_commit"], "distinct immutable"),
                              (old[:12], "distinct immutable"),
                              (self.command("git", "commit-tree", tree, "-m", "side"), "ancestor of the baseline")):
            with self.subTest(commit=commit):
                snapshot["commit"] = commit
                self.assert_invalid(match)
        snapshot["commit"] = old
        snapshot["kind"] = "original-chain"
        self.assert_invalid("whole statement roles")
        snapshot["kind"] = "original-statement"
        self.spec["frozen"].append(copy.deepcopy(snapshot))
        self.assert_invalid("distinct immutable")

    def test_snapshot_scaffold_bindings_and_parameters_must_hold_at_its_commit(self):
        cases = (
            (dict(old_scaffold=self.SCAFFOLD.replace("Q : nat -> Prop", "Q : nat -> bool")), "scaffold differs"),
            (dict(old_closed="Definition closed : Prop := forall n, Q n -> P n.\n"), "binding target closed differs"),
            (dict(old_claim="(** Old. *)\nDefinition schema_claim : Prop := forall n, middle n /\\ Q n.\n"),
             "bindings must name exactly"),
        )
        for parts, match in cases:
            with self.subTest(parts=parts):
                self.setUp()
                self.add_snapshot(**parts)
                self.assert_invalid(match)

    def test_stale_scan_sees_parametric_endpoints(self):
        old_cert = "base/theories/migration/old_family.v"
        self.write(old_cert, "From GTBase.conjectures Require Import X2.\nModule OldLegacy.\n"
                   "Definition old_glued : Prop := schema_claim (fun _ => True) (fun _ => True).\n"
                   "End OldLegacy.\n")
        label = (old_cert + "#OldLegacy.old_glued resolves through live ['schema_claim']")
        self.assertIn(label, self.failures())
        self.spec["known_stale_snapshots"] = {old_cert + "#OldLegacy.old_glued": "replaced by schema_compat"}
        self.assertEqual(self.failures(), [])
        del self.spec["known_stale_snapshots"]
        self.write(old_cert, "From GTBase.migration Require Import test_family.\nModule OldLegacy.\n"
                   "Definition old_glued : Prop := SchemaLegacy.schema_claim (fun _ => True) (fun _ => True).\n"
                   "End OldLegacy.\n")
        self.assertEqual(self.failures(), [])


    @unittest.skipUnless(KERNEL, "use --kernel for tiny compiled probes")
    def test_kernel_checks_parametric_snapshots(self):
        self.add_snapshot()
        self.compile_fixture()
        self.assertEqual(REPORT.check_kernel(self.spec), [])
        self.cert_source = self.cert_source.replace(
            "Lemma schema_original_compat (P Q : nat -> Prop) :\n",
            "Lemma schema_original_compat (P Q : nat -> Prop) : False ->\n").replace(
            "Proof. split; intros h c n; destruct (h c n); split; assumption. Qed.\n",
            "Proof. intros []. Qed.\n")
        self.write(self.certificate, self.cert_source)
        self.compile_fixture()
        self.assertTrue(REPORT.check_kernel(self.spec))


if __name__ == "__main__":
    unittest.main(verbosity=2)

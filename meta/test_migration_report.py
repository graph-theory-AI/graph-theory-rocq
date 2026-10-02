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


if __name__ == "__main__":
    unittest.main(verbosity=2)

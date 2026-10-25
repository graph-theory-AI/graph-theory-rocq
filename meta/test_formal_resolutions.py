#!/usr/bin/env python3
"""Mutation canaries for the resolution registry, including real Rocq checks."""
from __future__ import annotations

import contextlib
import copy
import hashlib
import io
import json
import os
from pathlib import Path
import tempfile
import unittest

import formal_resolutions as R


class ResolutionCanaries(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="resolution-canary-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        (self.root / "meta").mkdir()
        (self.root / "fixture/theories").mkdir(parents=True)
        self.statement = self.root / "fixture/theories/statement.v"
        self.proof = self.root / "fixture/theories/proof.v"
        self.statement.write_text("Definition claim : Prop := 2 = 2.\n")
        self.proof.write_text("Require Import Fixture.statement.\n"
                              "Theorem resolved : claim. Proof. reflexivity. Qed.\n")
        (self.root / "fixture/_CoqProject").write_text(
            "-Q theories Fixture\ntheories/statement.v\ntheories/proof.v\n")
        self.row = {
            "row_id": "fixture:1", "record_key": "fixture__01", "repo": "fixture",
            "source_hash": hashlib.sha256(b"synthetic source snapshot").hexdigest(),
            "source_text": "Two equals two.",
            "source_locator": "synthetic source | Rocq: fixture/theories/statement.v#claim",
            "formal_name": "claim", "status": "open",
        }
        self.entry = {
            **{field: self.row[field] for field in (
                "row_id", "record_key", "source_hash", "source_text", "source_locator")},
            "corpus": "v2", "package": "fixture",
            "statement": "Fixture.statement.claim",
            "statement_file": "fixture/theories/statement.v",
            "statement_sha256": R.declaration_hash(self.statement.read_text()),
            "theorem": "Fixture.proof.resolved", "theorem_file": "fixture/theories/proof.v",
            "direction": "prove",
            "correspondence": {"explanation": "Synthetic equality canary.",
                               "implemented_by": "fixture author", "reviewed_by": "fixture reviewer",
                               "reviewed_at": "2026-09-05"},
        }
        self.write_metadata()

    def write_metadata(self):
        (self.root / "meta/v2_corpus_manifest.json").write_text(json.dumps({"rows": [self.row]}))
        (self.root / "meta/formal_resolutions.json").write_text(
            json.dumps({"schema_version": 1, "resolutions": [self.entry]}))

    def test_positive_resolution_compiles_and_preserves_open_status(self):
        before = (self.root / "meta/v2_corpus_manifest.json").read_bytes()
        result = R.verify_resolutions(self.root)
        self.assertEqual(len(result), 1)
        self.assertEqual(result[0].exact_type_key,
                         ("Fixture.statement.claim", "Fixture.proof.resolved", "prove"))
        self.assertEqual(result[0].assumptions.count("Closed under the global context"), 2)
        self.assertEqual(before, (self.root / "meta/v2_corpus_manifest.json").read_bytes())

    def test_negative_resolution_compiles(self):
        self.statement.write_text("Definition claim : Prop := False.\n")
        self.entry["statement_sha256"] = R.declaration_hash(self.statement.read_text())
        self.entry["direction"] = "disprove"
        self.proof.write_text("Require Import Fixture.statement.\n"
                              "Theorem resolved : ~ claim. Proof. intro H; exact H. Qed.\n")
        self.write_metadata()
        self.assertEqual(R.verify_resolutions(self.root)[0].direction, "disprove")

    def test_clean_local_dependency_build_and_only_requested_package_targets(self):
        (self.root / "support/theories").mkdir(parents=True)
        (self.root / "support/_CoqProject").write_text("-Q theories Support\ntheories/base.v\n")
        (self.root / "support/theories/base.v").write_text(
            "Theorem base_fact : 2 = 2. Proof. reflexivity. Qed.\n")
        (self.root / "fixture/_CoqProject").write_text(
            "-Q theories Fixture\n-Q ../support/theories Support\n"
            "theories/statement.v\ntheories/proof.v\ntheories/unrelated.v\n")
        (self.root / "fixture/theories/unrelated.v").write_text(
            "Theorem unrelated : False. Proof. exact I. Qed.\n")
        self.proof.write_text("Require Import Fixture.statement Support.base.\n"
                              "Theorem resolved : claim. Proof. exact base_fact. Qed.\n")
        self.assertEqual(len(R.verify_resolutions(self.root)), 1)
        self.assertTrue((self.root / "support/theories/base.vo").is_file())
        self.assertFalse((self.root / "fixture/theories/unrelated.vo").exists())

    def test_verification_preserves_prebuilt_dependents_with_project_flags(self):
        (self.root / "support/theories").mkdir(parents=True)
        (self.root / "support/_CoqProject").write_text("-Q theories Support\ntheories/base.v\n")
        (self.root / "support/theories/base.v").write_text(
            "Theorem base_fact : 2 = 2. Proof. reflexivity. Qed.\n")
        # rocq makefile groups -Q before -R, unlike their order in this project.
        (self.root / "fixture/_CoqProject").write_text(
            "-R theories Fixture\n-Q ../support/theories Support\n"
            "-arg -w -arg -notation-overridden,-ambiguous-paths\n"
            "theories/statement.v\ntheories/proof.v\ntheories/dependent.v\n")
        # MathComp plus a universe-bearing declaration exposes the inconsistent
        # objects produced when verification omits the package's compiler options.
        claim = "Definition claim : Prop := forall T : Type, T = T.\n"
        self.statement.write_text("From mathcomp Require Import all_boot.\n" + claim)
        self.entry["statement_sha256"] = R.declaration_hash(claim)
        self.write_metadata()
        self.proof.write_text("Require Import Fixture.statement Support.base.\n"
                              "Theorem resolved : claim. Proof. intros T; reflexivity. Qed.\n")
        dependent = self.root / "fixture/theories/dependent.v"
        dependent.write_text("Require Import Fixture.statement Fixture.proof.\n"
                             "Theorem derived : claim. Proof. exact resolved. Qed.\n")
        env = R.ROCQ.environment()
        for package in ("support", "fixture"):
            directory = self.root / package
            R.run(["rocq", "makefile", "-f", "_CoqProject", "-o", "Makefile.coq"], directory, env)
            R.run(["make", "-f", "Makefile.coq"], directory, env)
        products = [source.with_suffix(".vo") for source in (self.statement, self.proof)]
        digests = [hashlib.sha256(product.read_bytes()).hexdigest() for product in products]
        dependent_mtime = dependent.with_suffix(".vo").stat().st_mtime_ns

        self.assertEqual(len(R.verify_resolutions(self.root, build=False)), 1)

        # Verification must not invalidate dependents already built by the caller.
        probe = self.root / "DependentProbe.v"
        probe.write_text("Require Import Fixture.dependent.\nCheck derived.\n")
        flags, _files = R.project(self.root, "fixture")
        R.run(["rocq", "compile", *flags, str(probe)], self.root / "fixture", env)
        self.assertEqual(dependent.with_suffix(".vo").stat().st_mtime_ns, dependent_mtime)
        self.assertEqual([hashlib.sha256(product.read_bytes()).hexdigest() for product in products],
                         digests)

    def test_wrong_type_closed_theorem_is_rejected(self):
        self.proof.write_text("Require Import Fixture.statement.\n"
                              "Theorem resolved : True. Proof. exact I. Qed.\n")
        with self.assertRaisesRegex(R.ResolutionError, "failed"):
            R.verify_resolutions(self.root)

    def test_wrong_polarity_is_rejected(self):
        self.entry["direction"] = "disprove"
        self.write_metadata()
        with self.assertRaisesRegex(R.ResolutionError, "failed"):
            R.verify_resolutions(self.root)

    def test_transitive_axiom_is_rejected(self):
        (self.root / "fixture/theories/dependency.v").write_text(
            "Require Import Fixture.statement.\nAxiom hidden_axiom : claim.\n")
        (self.root / "fixture/_CoqProject").write_text(
            "-Q theories Fixture\ntheories/statement.v\ntheories/dependency.v\ntheories/proof.v\n")
        self.proof.write_text("Require Import Fixture.statement Fixture.dependency.\n"
                              "Theorem resolved : claim. Proof. exact hidden_axiom. Qed.\n")
        with self.assertRaisesRegex(R.ResolutionError, "assumptions are not closed"):
            R.verify_resolutions(self.root)

    def test_stale_compiled_proof_cannot_hide_changed_source(self):
        R.verify_resolutions(self.root)
        original_stat = self.proof.stat()
        self.proof.write_text("Require Import Fixture.statement.\n"
                              "Theorem resolved : claim. Proof. exact I. Qed.\n")
        os.utime(self.proof, ns=(original_stat.st_atime_ns, original_stat.st_mtime_ns))
        with self.assertRaisesRegex(R.ResolutionError, "failed"):
            R.verify_resolutions(self.root, build=False)

    def test_admission_is_rejected(self):
        self.proof.write_text("Require Import Fixture.statement.\nTheorem resolved : claim. Admitted.\n")
        with self.assertRaisesRegex(R.ResolutionError, "forbidden admission"):
            R.verify_resolutions(self.root)

    def test_source_and_identity_mutations_are_rejected(self):
        mutations = {
            "source hash": ("source_hash", "0" * 64),
            "source prose": ("source_text", "A different proposition."),
            "source locator": ("source_locator", "another source"),
            "row id": ("row_id", "fixture:2"),
            "statement name": ("statement", "Fixture.statement.other"),
            "module spoof": ("theorem", "Other.proof.resolved"),
            "command injection": ("theorem", "Fixture.proof.resolved). Axiom H : False"),
            "path traversal": ("theorem_file", "../proof.v"),
            "missing project source": ("theorem_file", "fixture/theories/unlisted.v"),
        }
        (self.root / "fixture/theories/unlisted.v").write_text(self.proof.read_text())
        for label, (field, value) in mutations.items():
            with self.subTest(label=label):
                mutated = copy.deepcopy(self.entry)
                mutated[field] = value
                with self.assertRaises(R.ResolutionError):
                    R.validate_entry(self.root, mutated)

    def test_statement_change_requires_new_correspondence(self):
        self.statement.write_text("Definition claim : Prop := True.\n")
        with self.assertRaisesRegex(R.ResolutionError, "statement declaration changed"):
            R.validate_entry(self.root, self.entry)

    def test_cannot_substitute_another_same_named_statement(self):
        other = self.root / "fixture/theories/other.v"
        other.write_text("Definition claim : Prop := True.\n")
        with (self.root / "fixture/_CoqProject").open("a") as project:
            project.write("theories/other.v\n")
        self.entry.update(statement="Fixture.other.claim", statement_file="fixture/theories/other.v",
                          statement_sha256=R.declaration_hash(other.read_text()))
        with self.assertRaisesRegex(R.ResolutionError, "corpus statement location"):
            R.validate_entry(self.root, self.entry)

    def test_transcript_drops_warning_blocks_and_fails_on_unknown_messages(self):
        tmp = "/tmp/rocq-resolution-abc123"
        warning = (f'File "{tmp}/ResolutionCheck.v", line 1, characters 0-39:\n'
                   'Warning: Notation "_ + _" was already used in scope nat_scope.\n'
                   "[notation-overridden,parsing,default]\n")
        long_warning = (f'File "{tmp}/ResolutionCheck.v", line 2, characters 0-10:\n'
                        "Warning:\nA message\non three lines.\n[deprecated-since-9.2,deprecated,default]\n")
        checks = "claim : Prop\n     : Prop\nClosed under the global context\n"
        self.assertEqual(R.transcript(warning + long_warning + checks + warning, tmp), checks)
        self.assertEqual(R.transcript(checks, tmp), checks)
        for bad in (f'File "{tmp}/ResolutionCheck.v", line 1, characters 0-5:\nSomething else.\n' + checks,
                    "Warning: a warning without its location.\n" + checks,
                    warning.replace("[notation-overridden,parsing,default]\n", "") + checks):
            with self.subTest(bad=bad):
                with self.assertRaisesRegex(R.ResolutionError, "unrecognised compiler message"):
                    R.transcript(bad, tmp)

    def test_report_transcript_is_reproducible_when_the_probe_warns(self):
        # Importing the statement module re-declares "_ + _" in nat_scope, so the probe warns.
        notation = 'Notation "x + y" := (Nat.add x y) (at level 50, left associativity) : nat_scope.\n'
        claim = "Definition claim : Prop := 2 = 2.\n"
        self.statement.write_text(notation + claim)
        self.entry["statement_sha256"] = R.declaration_hash(claim)
        self.write_metadata()
        result = R.verify_resolutions(self.root)
        self.assertEqual(result[0].assumptions.count("Closed under the global context"), 2)
        self.assertNotIn("Warning:", result[0].assumptions)
        self.assertNotIn("rocq-resolution-", result[0].assumptions)
        # Not vacuous: the same probe, compiled directly, does warn.
        probe = self.root / "WarningProbe.v"
        probe.write_text("Require Import Fixture.statement Fixture.proof.\nPrint Assumptions Fixture.proof.resolved.\n")
        flags, _files = R.project(self.root, "fixture")
        output = R.run(["rocq", "compile", *flags, str(probe)], self.root / "fixture", R.ROCQ.environment())
        self.assertIn("Warning:", output)
        self.assertIn(str(probe), output)

    def test_entry_fields_are_exact(self):
        mutated = copy.deepcopy(self.entry)
        mutated["node_id"] = 1
        with self.assertRaisesRegex(R.ResolutionError, "fields not used by v2 entries"):
            R.validate_entry(self.root, mutated)
        del mutated["node_id"], mutated["source_hash"]
        with self.assertRaisesRegex(R.ResolutionError, "missing fields"):
            R.validate_entry(self.root, mutated)

    def test_duplicate_entries_are_rejected(self):
        (self.root / "meta/formal_resolutions.json").write_text(
            json.dumps({"schema_version": 1, "resolutions": [self.entry, self.entry]}))
        with self.assertRaisesRegex(R.ResolutionError, "duplicate record_key"):
            R.registry_entries(self.root)

    def test_same_author_reviewer_is_rejected(self):
        self.entry["correspondence"]["reviewed_by"] = self.entry["correspondence"]["implemented_by"]
        with self.assertRaisesRegex(R.ResolutionError, "reviewer must differ"):
            R.validate_entry(self.root, self.entry)

    def test_registered_proof_does_not_exempt_a_second_exact_proof(self):
        with self.proof.open("a") as proof:
            proof.write("Theorem unregistered : claim. Proof. reflexivity. Qed.\n")
        checked = R.verify_resolutions(self.root)
        keys = {item.exact_type_key for item in checked}
        statement = self.entry["statement"]
        registered_cases = R.CONTRACTS.forbidden_exact_types(
            "open", statement, "Fixture.proof.resolved", keys)
        self.assertEqual(registered_cases, [("unconditional-refutation", f"~ {statement}")])
        other_cases = R.CONTRACTS.forbidden_exact_types(
            "open", statement, "Fixture.proof.unregistered", keys)
        probe = self.root / "ForbiddenProbe.v"
        body = "Require Import Fixture.statement Fixture.proof.\n"
        body += "".join(f"Fail Check (Fixture.proof.unregistered : {typ}).\n"
                        for _kind, typ in other_cases)
        probe.write_text(body)
        with self.assertRaisesRegex(R.ResolutionError, "The command has not failed"):
            R.run(["rocq", "compile", "-Q", "theories", "Fixture", str(probe)],
                  self.root / "fixture", R.ROCQ.environment())


class OpgResolutions(unittest.TestCase):
    """OPG rows: key opg:<slug>, pinned row identity, the unique top-level statement file, selection."""

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="resolution-opg-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        (self.root / "meta").mkdir()
        (self.root / "fixture/theories").mkdir(parents=True)
        self.statement = self.root / "fixture/theories/statement.v"
        self.statement.write_text("Definition claim : Prop := 2 = 2.\n")
        (self.root / "fixture/theories/proof.v").write_text(
            "Require Import Fixture.statement.\nTheorem resolved : claim. Proof. reflexivity. Qed.\n")
        self.project = ["theories/statement.v", "theories/proof.v"]
        self.write_project()
        self.row = {
            "slug": "fixture_problem", "node_id": 4242,
            "canonical_url": "http://www.openproblemgarden.org/op/fixture_problem",
            "source_commit_repo": "1" * 40, "source_commit_problems_json": "2" * 40,
            "source_text": "Conjecture Two equals two.", "selected_proposition": "primary OPG statement",
            "repo": "fixture", "formal_name": "claim", "status": "open",
        }
        self.entry = {
            "record_key": "opg:fixture_problem", "corpus": "opg",
            **{field: self.row[field] for field in R.SOURCE_IDENTITY["opg"]},
            "package": "fixture", "statement": "Fixture.statement.claim",
            "statement_file": "fixture/theories/statement.v",
            "statement_sha256": R.declaration_hash(self.statement.read_text()),
            "theorem": "Fixture.proof.resolved", "theorem_file": "fixture/theories/proof.v",
            "direction": "prove",
            "correspondence": {"explanation": "Synthetic OPG canary.",
                               "implemented_by": "fixture author", "reviewed_by": "fixture reviewer",
                               "reviewed_at": "2026-10-25"},
        }
        self.rows = [self.row]
        self.entries = [self.entry]
        self.write_metadata()

    def write_project(self):
        (self.root / "fixture/_CoqProject").write_text(
            "-Q theories Fixture\n" + "".join(f"{source}\n" for source in self.project))

    def write_metadata(self):
        (self.root / "meta/opg_corpus_manifest.json").write_text(json.dumps({"rows": self.rows}))
        (self.root / "meta/formal_resolutions.json").write_text(
            json.dumps({"schema_version": 1, "resolutions": self.entries}))

    def add_source(self, name, text, listed=True):
        (self.root / "fixture/theories" / name).write_text(text)
        if listed:
            self.project.append(f"theories/{name}")
            self.write_project()

    def rejected(self, pattern, entry=None):
        with self.assertRaisesRegex(R.ResolutionError, pattern):
            R.validate_entry(self.root, self.entry if entry is None else entry)

    def cli(self, *args):
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = R.main(["--root", str(self.root), *args])
        return code, out.getvalue() + err.getvalue()

    def test_positive_opg_resolution_compiles_and_preserves_the_manifest(self):
        before = (self.root / "meta/opg_corpus_manifest.json").read_bytes()
        result = R.verify_resolutions(self.root)
        self.assertEqual([item.record_key for item in result], ["opg:fixture_problem"])
        self.assertEqual(result[0].exact_type_key,
                         ("Fixture.statement.claim", "Fixture.proof.resolved", "prove"))
        self.assertEqual(before, (self.root / "meta/opg_corpus_manifest.json").read_bytes())

    def test_source_identity_mutations_are_rejected(self):
        for field in R.SOURCE_IDENTITY["opg"]:
            with self.subTest(field=field):
                mutated = copy.deepcopy(self.entry)
                mutated[field] = 4243 if field == "node_id" else self.entry[field] + "x"
                self.rejected(f"{field} differs from the pinned source row", mutated)

    def test_key_and_row_identity_are_rejected_when_wrong(self):
        cases = {
            "fixture_problem": "opg:<slug>", "opg:Fixture_problem": "opg:<slug>",
            "opg:fixture_problem ": "opg:<slug>", "opg:other_problem": "exactly once",
        }
        for key, pattern in cases.items():
            with self.subTest(key=key):
                self.rejected(pattern, {**self.entry, "record_key": key})
        self.rejected("ownership", {**self.entry, "package": "other"})
        self.rejected("formal_name", {**self.entry, "statement": "Fixture.statement.other"})
        self.rows = [self.row, dict(self.row)]
        self.write_metadata()
        self.rejected("exactly once")

    def test_entry_fields_are_exact(self):
        self.rejected("fields not used by opg entries", {**self.entry, "source_hash": "0" * 64})
        self.rejected("fields not used by opg entries", {**self.entry, "row_id": "opg:fixture_problem"})
        mutated = copy.deepcopy(self.entry)
        del mutated["node_id"]
        self.rejected("missing fields", mutated)
        self.rejected("corpus must be v2 or opg", {**self.entry, "corpus": ["opg"]})

    def test_row_without_formal_name_is_rejected(self):
        self.row["formal_name"] = ""
        self.write_metadata()
        self.rejected("needs the source row's formal_name")

    def test_frozen_module_copies_comments_and_unlisted_files_do_not_count(self):
        self.add_source("migration.v", "Module Legacy.\nDefinition claim : Prop := 2 = 2.\nEnd Legacy.\n"
                                       "Module Alias := Legacy.\n")
        self.add_source("notes.v", "(* Definition claim : Prop := True. *)\n"
                                   "Definition note : string := \"\nDefinition claim\".\n")
        self.add_source("unlisted.v", "Definition claim : Prop := True.\n", listed=False)
        R.validate_entry(self.root, self.entry)
        self.rejected("corpus statement location",
                      {**self.entry, "statement_file": "fixture/theories/migration.v"})

    def test_a_second_top_level_definition_is_ambiguous(self):
        for name, text in (("copy.v", "Definition claim : Prop := True.\n"),
                           ("section.v", "Section S.\nDefinition claim : Prop := True.\nEnd S.\n"),
                           ("local.v", "Local Definition claim : Prop := True.\n")):
            with self.subTest(name=name):
                self.setUp()
                self.add_source(name, text)
                self.rejected("needs exactly one top-level definition")

    def test_unsupported_scope_structure_fails_closed(self):
        self.add_source("broken.v", "Definition claim : Prop := True.\nEnd Nowhere.\n")
        self.rejected("unsupported Module/Section structure")

    def test_selection_by_record_and_package(self):
        broken = {**copy.deepcopy(self.entry), "record_key": "opg:missing_problem", "package": "other"}
        self.entries = [self.entry, broken]
        self.write_metadata()
        cases = [
            ((), 1, "source row must occur exactly once: OPG slug missing_problem"),
            (("--record", "opg:fixture_problem"), 0, "1 entries; proofs not checked; selected entries only"),
            (("--record", "opg:missing_problem"), 1, "source row must occur exactly once"),
            (("--record", "opg:fixture_problem", "--record", "opg:missing_problem"), 1, "exactly once"),
            (("--record", "opg:unknown_problem"), 1, "unknown record_key: opg:unknown_problem"),
            (("--package", "fixture"), 0, "1 entries; proofs not checked; selected entries only"),
            (("--package", "other"), 1, "exactly once"),
            (("--package", "nowhere"), 1, "matches no registry entry"),
            (("--package", "fixture", "--record", "opg:missing_problem"), 1, "matches no registry entry"),
        ]
        for args, code, text in cases:
            with self.subTest(args=args):
                got, output = self.cli("--metadata-only", *args)
                self.assertEqual(got, code, output)
                self.assertIn(text, output)

    def test_record_selection_compiles_and_reports_only_the_selected_entry(self):
        broken = {**copy.deepcopy(self.entry), "record_key": "opg:missing_problem", "package": "other"}
        self.entries = [self.entry, broken]
        self.write_metadata()
        report = self.root / "report.txt"
        code, output = self.cli("--record", "opg:fixture_problem", "--report", str(report))
        self.assertEqual(code, 0, output)
        self.assertIn("OK opg:fixture_problem: prove Fixture.statement.claim", output)
        self.assertIn("formal resolutions OK (1 exact, assumption-free proofs; selected entries only)", output)
        text = report.read_text()
        self.assertTrue(text.startswith("opg:fixture_problem\n"))
        self.assertNotIn("opg:missing_problem", text)
        self.assertEqual(text.count("Closed under the global context"), 2)


if __name__ == "__main__":
    unittest.main(verbosity=2)

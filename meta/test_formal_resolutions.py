#!/usr/bin/env python3
"""Mutation canaries for the resolution registry, including real Rocq checks."""
from __future__ import annotations

import copy
import hashlib
import json
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
        self.proof.write_text("Require Import Fixture.statement.\n"
                              "Theorem resolved : claim. Proof. exact I. Qed.\n")
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


if __name__ == "__main__":
    unittest.main(verbosity=2)

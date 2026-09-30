#!/usr/bin/env python3
"""Mutation canaries for the dependency-graph edge gate (meta/check_edges.py).

Three layers, in the style of meta/test_statement_docs.py (a throwaway tree in a temp
dir, so nothing depends on the real corpus or on a concurrent regeneration):

  1. the probe GENERATOR — the `.v` text produced for an implies / equiv / specializes /
     conditional edge, and the fact that swapping `from` and `to` produces a different
     claimed type (which is what makes the swap canary of layer 3 bite);
  2. the output PARSER — a coqc run is accepted only when it exits 0, prints no
     `Axioms:` block and prints exactly one "Closed under the global context" per edge;
  3. an END-TO-END run of `--assumptions` against a tiny synthetic package (four Rocq
     files, no mathcomp, so the coqc runs are ~0.3s each): the honest graph passes,
     while a swapped edge, an axiom-tainted proof and a conditional edge whose
     external hypothesis is dropped each fail.

Plus the registry checker's fixtures: missing reviewer, reviewer == prover, a refuted
entry without a reason, and a state that contradicts the graph each fail; a consistent
ledger passes; a missing ledger is a warning, an error under --strict.

Run: python3 meta/test_check_edges.py
"""

from __future__ import annotations

import contextlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

META = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, META)
import check_edges as GATE               # noqa: E402
import gate_contracts as CONTRACTS       # noqa: E402
import rocq_toolchain as ROCQ            # noqa: E402

CLOSED = GATE.CLOSED

# ── the synthetic package ───────────────────────────────────────────────────────────────
# Distinct, mutually NON-convertible Props, so a swapped claim really is a type error
# (with `Prop := True` everywhere the swap would typecheck and the canary would lie).

X0_V = """Definition a_statement : Prop := 0 = 0.
Definition b_statement : Prop := 1 = 1.
Definition c_statement : Prop := 2 = 2.
Definition d_statement : Prop := 3 = 3.
Definition e_statement : Prop := 5 = 5.
Definition f_statement : Prop := 6 = 6.
"""

IMPL_V = """From Fake.conjectures Require Import X0.

Definition ext_fact : Prop := 4 = 4.

(*@EDGE from=a_statement to=b_statement kind=implies status=verified proof=a_implies_b *)
Theorem a_implies_b : a_statement -> b_statement.
Proof. unfold a_statement, b_statement. intros _. reflexivity. Qed.

Theorem b_equiv_a : b_statement <-> a_statement.
Proof. unfold a_statement, b_statement. split; intros _; reflexivity. Qed.

Theorem c_implies_d : ext_fact -> c_statement -> d_statement.
Proof. unfold ext_fact, c_statement, d_statement. intros _ _. reflexivity. Qed.

Axiom bogus_fact : 6 = 6.

Theorem e_implies_f : e_statement -> f_statement.
Proof. unfold e_statement, f_statement. intros _. exact bogus_fact. Qed.
"""


def edge(frm, to, kind, proof, status="verified", external=None, stem="implications_X0"):
    record = {"from": frm, "to": to, "kind": kind, "status": status, "proof": proof,
              "cite": "fixture", "sources": [f"fakepkg/{stem}.v"]}
    if external is not None:
        record["external"] = external
    return record


GOOD_EDGES = [
    edge("a_statement", "b_statement", "implies", "a_implies_b"),
    edge("b_statement", "a_statement", "equiv", "b_equiv_a"),
    edge("c_statement", "d_statement", "implies", "c_implies_d",
         status="conditional", external=["ext_fact"]),
]


class ProbeGenerator(unittest.TestCase):
    """Layer 1: what the gate claims, in Rocq syntax."""

    defmod = {"a_statement": "X0", "b_statement": "X0", "c_statement": "X0",
              "d_statement": "X0", "ext_fact": "implications_X0"}

    def test_implies_claims_from_arrow_to(self):
        self.assertEqual(GATE.expected_type(GOOD_EDGES[0]), "a_statement -> b_statement")

    def test_specializes_claims_an_arrow_too(self):
        spec = edge("a_statement", "b_statement", "specializes", "a_implies_b")
        self.assertEqual(GATE.expected_type(spec), "a_statement -> b_statement")

    def test_equiv_claims_an_iff(self):
        self.assertEqual(GATE.expected_type(GOOD_EDGES[1]), "b_statement <-> a_statement")

    def test_conditional_prefixes_the_externals_in_order(self):
        cond = edge("c_statement", "d_statement", "implies", "c_implies_d",
                    status="conditional", external=["ext_one", "ext_two"])
        self.assertEqual(GATE.expected_type(cond),
                         "ext_one -> ext_two -> c_statement -> d_statement")

    def test_conditional_equiv_parenthesises_the_iff(self):
        cond = edge("c_statement", "d_statement", "equiv", "c_equiv_d",
                    status="conditional", external=["ext_one"])
        self.assertEqual(GATE.expected_type(cond), "ext_one -> (c_statement <-> d_statement)")

    def test_missing_external_field_is_not_an_error(self):
        bare = dict(GOOD_EDGES[0])
        bare.pop("external", None)
        self.assertEqual(GATE.externals(bare), [])
        self.assertEqual(GATE.externals({"external": None}), [])

    def test_swapping_endpoints_changes_the_claim(self):
        swapped = edge("b_statement", "a_statement", "implies", "a_implies_b")
        self.assertNotEqual(GATE.expected_type(swapped), GATE.expected_type(GOOD_EDGES[0]))

    def test_probe_imports_endpoint_modules_and_qualifies_names(self):
        text = GATE.probe_text("Fake", GOOD_EDGES, self.defmod)
        self.assertIn("From Fake.conjectures Require Import X0 implications_X0.", text)
        self.assertIn("Check (Fake.conjectures.implications_X0.a_implies_b : "
                      "Fake.conjectures.X0.a_statement -> Fake.conjectures.X0.b_statement).",
                      text)
        self.assertIn("Check (Fake.conjectures.implications_X0.b_equiv_a : "
                      "Fake.conjectures.X0.b_statement <-> Fake.conjectures.X0.a_statement).",
                      text)
        self.assertIn("Check (Fake.conjectures.implications_X0.c_implies_d : "
                      "Fake.conjectures.implications_X0.ext_fact -> "
                      "Fake.conjectures.X0.c_statement -> Fake.conjectures.X0.d_statement).",
                      text)
        self.assertEqual(text.count("Print Assumptions "), len(GOOD_EDGES))

    def test_probe_can_also_be_written_with_bare_names(self):
        text = GATE.probe_text("Fake", GOOD_EDGES, self.defmod, qualified=False)
        self.assertIn("Check (a_implies_b : a_statement -> b_statement).", text)
        self.assertIn("Print Assumptions a_implies_b.", text)

    def test_registry_key_shape(self):
        self.assertEqual(GATE.edge_key(GOOD_EDGES[0]), "a_statement->b_statement:implies")

    def test_refutes_edges_are_out_of_scope(self):
        graph = {"edges": [edge("a_statement", "b_statement", "refutes", "", status="verified"),
                           GOOD_EDGES[0]]}
        self.assertEqual([GATE.edge_key(e) for e in GATE.proved_edges(graph)],
                         ["a_statement->b_statement:implies"])

    def test_candidate_edges_are_out_of_scope(self):
        graph = {"edges": [edge("a_statement", "b_statement", "implies", "", status="candidate")]}
        self.assertEqual(GATE.proved_edges(graph), [])


class OutputParser(unittest.TestCase):
    """Layer 2: what counts as a clean Print Assumptions run."""

    def test_clean_run_passes(self):
        out = f"a_implies_b\n{CLOSED}\nb_equiv_a\n{CLOSED}\n"
        problems, closed = GATE.parse_probe_output(out, 0, 2)
        self.assertEqual((problems, closed), ([], 2))

    def test_axioms_block_fails(self):
        out = f"a_implies_b\n{CLOSED}\nb_equiv_a\nAxioms:\nbogus_fact : 6 = 6\n"
        problems, closed = GATE.parse_probe_output(out, 0, 2)
        self.assertTrue(any("Axioms:" in p for p in problems), problems)
        self.assertEqual(closed, 1)

    def test_short_closed_count_fails(self):
        problems, _ = GATE.parse_probe_output(f"{CLOSED}\n", 0, 2)
        self.assertTrue(any("1 of 2" in p for p in problems), problems)

    def test_long_closed_count_fails(self):
        problems, _ = GATE.parse_probe_output(f"{CLOSED}\n{CLOSED}\n{CLOSED}\n", 0, 2)
        self.assertTrue(any("3 of 2" in p for p in problems), problems)

    def test_nonzero_exit_fails_even_with_the_right_count(self):
        problems, _ = GATE.parse_probe_output(f"{CLOSED}\n{CLOSED}\n", 1, 2)
        self.assertTrue(any("exited 1" in p for p in problems), problems)

    def test_notation_warnings_are_filtered_out_of_a_report(self):
        noisy = ('File "./theories/conjectures/_assum_edges.v", line 1, characters 0-147:\n'
                 'Warning: Notation "_ + _" was already used in scope nat_scope.\n'
                 '[notation-overridden,parsing,default]\n'
                 'Error:\nThe term "x" has type "A" while it is expected to have type "B".\n')
        self.assertEqual(GATE.interesting_lines(noisy),
                         ["Error:",
                          'The term "x" has type "A" while it is expected to have type "B".'])


class RegistryLedger(unittest.TestCase):
    """The edge_waves.json cross-check."""

    def graph(self):
        return {"edges": [
            GOOD_EDGES[0], GOOD_EDGES[2],
            edge("e_statement", "f_statement", "implies", "", status="candidate"),
            edge("a_statement", "d_statement", "implies", "", status="refuted-direction"),
        ]}

    def registry(self, **overrides):
        entries = {
            "a_statement->b_statement:implies": {
                "gc": "e001", "tier": "T0", "wave": "W1", "host": "fakepkg",
                "state": "verified", "proof": "a_implies_b", "external": [],
                "reason": "", "proved_by": "agent-A", "reviewed_by": "agent-B",
                "reviewed_at": "2026-09-24", "note": ""},
            "c_statement->d_statement:implies": {
                "gc": "e002", "tier": "T1", "wave": "W1", "host": "fakepkg",
                "state": "conditional", "proof": "c_implies_d", "external": ["ext_fact"],
                "reason": "", "proved_by": "agent-B", "reviewed_by": "agent-A",
                "reviewed_at": "2026-09-24", "note": ""},
            "e_statement->f_statement:implies": {
                "gc": "e003", "tier": "T2", "wave": "W2", "host": "fakepkg",
                "state": "blocked", "proof": None, "external": [],
                "reason": "needs the Kempe-chain lemma", "proved_by": None,
                "reviewed_by": "", "reviewed_at": None, "note": "BLOCKED: waiting on X99"},
            "a_statement->d_statement:implies": {
                "gc": "e004", "tier": "T4", "wave": "W2", "host": "fakepkg",
                "state": "refuted-direction", "proof": None, "external": [],
                "reason": "independent: neither implies the other", "proved_by": None,
                "reviewed_by": "", "reviewed_at": None, "note": ""},
        }
        for key, patch in overrides.items():
            entries[key.replace("__", "->")].update(patch)
        return {"_README": "fixture", "edges": entries}

    def run_registry(self, registry, strict=False):
        buffer = io.StringIO()
        code = GATE.check_registry(self.graph(), registry, strict=strict, out=buffer)
        return code, buffer.getvalue()

    def test_consistent_ledger_passes(self):
        code, output = self.run_registry(self.registry())
        self.assertEqual(code, 0, output)
        self.assertIn("2/2 proved edges carry a reviewer", output)
        self.assertIn("1 blocked, 1 conditional, 1 refuted-direction, 1 verified", output)

    def test_blocked_matches_a_candidate_graph_edge(self):
        code, output = self.run_registry(self.registry(
            **{"e_statement__f_statement:implies": {"note": ""}}))
        self.assertEqual(code, 0, output)

    def test_missing_reviewer_fails(self):
        code, output = self.run_registry(self.registry(
            **{"a_statement__b_statement:implies": {"reviewed_by": ""}}))
        self.assertEqual(code, 1)
        self.assertIn("without reviewed_by", output)

    def test_reviewer_equal_to_prover_fails(self):
        code, output = self.run_registry(self.registry(
            **{"a_statement__b_statement:implies": {"reviewed_by": "agent-A"}}))
        self.assertEqual(code, 1)
        self.assertIn("reviewed_by == proved_by", output)

    def test_reviewer_equal_to_prover_modulo_whitespace_fails(self):
        code, output = self.run_registry(self.registry(
            **{"a_statement__b_statement:implies": {"reviewed_by": " agent-A "}}))
        self.assertEqual(code, 1)
        self.assertIn("reviewed_by == proved_by", output)

    def test_refuted_without_reason_fails(self):
        code, output = self.run_registry(self.registry(
            **{"a_statement__d_statement:implies": {"reason": ""}}))
        self.assertEqual(code, 1)
        self.assertIn("state refuted-direction without a reason", output)

    def test_blocked_without_reason_fails(self):
        code, output = self.run_registry(self.registry(
            **{"e_statement__f_statement:implies": {"reason": "  "}}))
        self.assertEqual(code, 1)
        self.assertIn("state blocked without a reason", output)

    def test_state_contradicting_the_graph_fails(self):
        code, output = self.run_registry(self.registry(
            **{"c_statement__d_statement:implies": {"state": "verified"}}))
        self.assertEqual(code, 1)
        self.assertIn("!= graph status 'conditional'", output)

    def test_out_of_vocabulary_state_fails(self):
        code, output = self.run_registry(self.registry(
            **{"c_statement__d_statement:implies": {"state": "mostly-fine"}}))
        self.assertEqual(code, 1)
        self.assertIn("out-of-vocabulary state", output)

    def test_proved_edge_absent_from_the_registry_fails(self):
        registry = self.registry()
        del registry["edges"]["c_statement->d_statement:implies"]
        code, output = self.run_registry(registry)
        self.assertEqual(code, 1)
        self.assertIn("absent from the registry", output)

    def test_registry_entry_without_a_graph_edge_is_only_a_note(self):
        registry = self.registry()
        registry["edges"]["x_statement->y_statement:implies"] = {
            "state": "candidate", "reason": "", "proved_by": None, "reviewed_by": ""}
        code, output = self.run_registry(registry)
        self.assertEqual(code, 0, output)
        self.assertIn("no edge in the dependency graph", output)

    def test_missing_file_is_a_warning_and_an_error_under_strict(self):
        code, output = self.run_registry(None)
        self.assertEqual(code, 0, output)
        self.assertIn("WARNING", output)
        code, output = self.run_registry(None, strict=True)
        self.assertEqual(code, 1)
        self.assertIn("--strict", output)


@unittest.skipIf(shutil.which("coqc") is None, "coqc not on PATH")
class EndToEnd(unittest.TestCase):
    """Layer 3: the whole gate, against a synthetic package compiled on the spot."""

    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory(prefix="check-edges-canary-")
        cls.root = Path(cls.temporary.name)
        pkg = cls.root / "fakepkg"
        (pkg / "theories" / "conjectures").mkdir(parents=True)
        (pkg / "_CoqProject").write_text(
            "-R theories Fake\n"
            "theories/conjectures/X0.v\ntheories/conjectures/implications_X0.v\n")
        (pkg / "theories/conjectures/X0.v").write_text(X0_V)
        (pkg / "theories/conjectures/implications_X0.v").write_text(IMPL_V)
        env = ROCQ.environment()
        for stem in ("X0", "implications_X0"):
            run = subprocess.run(["coqc", "-R", "theories", "Fake",
                                  f"theories/conjectures/{stem}.v"],
                                 cwd=pkg, env=env, capture_output=True, text=True)
            if run.returncode != 0:
                raise unittest.SkipTest(f"fixture package does not compile: "
                                        f"{run.stdout + run.stderr}")

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def assumptions(self, edges, keep=False):
        buffer = io.StringIO()
        code = GATE.check_assumptions({"edges": edges}, root=str(self.root), keep=keep,
                                      out=buffer)
        return code, buffer.getvalue()

    def test_honest_graph_passes(self):
        code, output = self.assumptions(GOOD_EDGES)
        self.assertEqual(code, 0, output)
        self.assertIn("[PASS] fakepkg", output)
        self.assertIn("3 edge(s) (1 conditional, 2 verified), 3 closed", output)
        self.assertIn("ACCEPTED: 3/3", output)

    def test_swapped_endpoints_fail(self):
        swapped = [edge("b_statement", "a_statement", "implies", "a_implies_b")]
        code, output = self.assumptions(swapped)
        self.assertEqual(code, 1)
        self.assertIn("does not typecheck", output)
        # the diagnostic probe reports what the constant really proves
        self.assertIn("a_statement -> b_statement", output)

    def test_axiom_tainted_proof_fails(self):
        tainted = [edge("e_statement", "f_statement", "implies", "e_implies_f")]
        code, output = self.assumptions(tainted)
        self.assertEqual(code, 1)
        self.assertIn("`Axioms:` block", output)

    def test_conditional_edge_without_its_external_fails(self):
        dropped = [edge("c_statement", "d_statement", "implies", "c_implies_d",
                        status="conditional", external=[])]
        code, output = self.assumptions(dropped)
        self.assertEqual(code, 1)
        self.assertIn("does not typecheck", output)

    def test_verified_edge_that_is_really_conditional_fails(self):
        mislabelled = [edge("c_statement", "d_statement", "implies", "c_implies_d")]
        code, output = self.assumptions(mislabelled)
        self.assertEqual(code, 1)
        self.assertIn("does not typecheck", output)

    def test_wrong_kind_fails(self):
        mislabelled = [edge("a_statement", "b_statement", "equiv", "a_implies_b")]
        code, output = self.assumptions(mislabelled)
        self.assertEqual(code, 1)

    def test_edge_without_a_proof_fails(self):
        code, output = self.assumptions([edge("a_statement", "b_statement", "implies", "")])
        self.assertEqual(code, 1)
        self.assertIn("name no proof", output)

    def test_edge_without_sources_fails(self):
        orphan = edge("a_statement", "b_statement", "implies", "a_implies_b")
        orphan["sources"] = []
        code, output = self.assumptions([orphan])
        self.assertEqual(code, 1)
        self.assertIn("cannot locate the hosting package", output)

    def test_unknown_package_fails(self):
        elsewhere = edge("a_statement", "b_statement", "implies", "a_implies_b")
        elsewhere["sources"] = ["nosuchpkg/implications_X0.v"]
        code, output = self.assumptions([elsewhere])
        self.assertEqual(code, 1)
        self.assertIn("unusable package layout", output)

    def test_probe_is_removed_and_kept_on_demand(self):
        probe = self.root / "fakepkg/theories/conjectures" / f"{GATE.PROBE_STEM}.v"
        code, _ = self.assumptions(GOOD_EDGES)
        self.assertEqual(code, 0)
        self.assertFalse(probe.exists())
        self.assertEqual(list((self.root / "fakepkg/theories/conjectures")
                              .glob(f"{GATE.PROBE_STEM}*")), [])
        code, output = self.assumptions(GOOD_EDGES, keep=True)
        self.assertEqual(code, 0)
        self.assertTrue(probe.exists(), output)
        for stale in (self.root / "fakepkg/theories/conjectures").glob(f"{GATE.PROBE_STEM}*"):
            stale.unlink()

    def test_definition_index_finds_endpoint_modules(self):
        index, duplicates = GATE.definition_index(str(self.root), "fakepkg")
        self.assertEqual(index["a_statement"], "X0")
        self.assertEqual(index["ext_fact"], "implications_X0")
        self.assertEqual(duplicates, {})

    def test_include_flags_come_from_the_coqproject(self):
        cqp = GATE.read_cqp(str(self.root), "fakepkg")
        self.assertEqual(CONTRACTS.incl_flags_from_cqp(cqp), ["-R", "theories", "Fake"])
        self.assertEqual(CONTRACTS.namespace_from_cqp(cqp), "Fake")

    def test_cli_main_runs_both_checks(self):
        graph = self.root / "graph.json"
        graph.write_text(json.dumps({"edges": GOOD_EDGES}))
        buffer = io.StringIO()
        with contextlib.redirect_stdout(buffer):
            code = GATE.main(["--graph", str(graph), "--root", str(self.root),
                              "--registry-file", str(self.root / "nope.json")])
            strict = GATE.main(["--graph", str(graph), "--root", str(self.root),
                               "--registry-file", str(self.root / "nope.json"), "--strict"])
        self.assertEqual(code, 0, buffer.getvalue())
        self.assertEqual(strict, 1, buffer.getvalue())
        self.assertIn("ACCEPTED: 3/3", buffer.getvalue())


if __name__ == "__main__":
    unittest.main(verbosity=2)

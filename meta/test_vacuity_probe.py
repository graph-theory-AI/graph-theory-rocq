#!/usr/bin/env python3
"""vacuity_probe.py fails closed when a probe could not search; no Rocq needed.

Every coqc call goes through vacuity_probe.sh(), which these tests replace by a fake that answers
from the scratch file it is given (no fake executable: /tmp is noexec in the containers).  A run
killed by a signal (a negative return code, or 137 under a wrapper), a probe setup that does not
compile (a parse error, a module that does not load), hint imports that do not load and a
small-model file that fails outside its Fail commands must each make the statement INCOMPLETE and
the exit code nonzero, in every probe layer and in --validate, and so must a name the index does not
hold (NOT-FOUND); the designed timeout (124), an ordinary failure and an ordinary success keep
their old verdicts."""
from __future__ import annotations

import contextlib
import io
from pathlib import Path
import unittest
from unittest.mock import patch

import vacuity_probe as VP


AREA, STEM, NS = "chromatic-theory", "X35", "Chromatic"
NAME = "fixture_statement"
HINTED = "sparse_graph_low_chromatic_cut_statement"   # has meta/probe_hints/<name>.v
BINDERS = "forall n : nat, 0 < n"                      # gets a small-model run
PREFLIGHT_MARK = "Goal True. Proof. __probe. Qed."


def entry(body: str = "True") -> tuple[str, str, str, str]:
    return (AREA, STEM, NS, body)


def fake_sh(answer, seen=None):
    """sh() replacement: `answer(file_name, text)` gives the return code of one coqc run, or a
    (return code, log) pair; the default logs mirror sh() (a timeout logs "<timeout>")."""
    def run(args, timeout):
        path = Path(args[-1])
        text = path.read_text()
        if seen is not None:
            seen.append(text)
        got = answer(path.name, text)
        rc, log = got if isinstance(got, tuple) else (got, None)
        if log is None:
            log = ("<killed>" if VP.killed(rc) else "<timeout>" if rc == 124
                   else "" if rc == 0 else "Error: fake failure")
        return rc, log
    return run


def setup_ok(answer):
    """The probe preflight and the hint imports compile; every other run is `answer`'s."""
    return lambda name, text: 0 if (name == "hint_setup.v" or PREFLIGHT_MARK in text) else answer(name, text)


def probe(idx, answer, name=NAME, seen=None):
    with patch.object(VP, "sh", fake_sh(answer, seen)):
        return VP.probe_statement(name, idx, VP.DEFAULT_TIMEOUT)


def report(rows):
    out = io.StringIO()
    with contextlib.redirect_stdout(out):
        rc = VP.report(rows)
    return rc, out.getvalue()


class ProbeCouldNotSearch(unittest.TestCase):
    def assert_incomplete(self, row, reason_text):
        self.assertEqual(row["status"], "INCOMPLETE")
        self.assertFalse(row["flag"])
        self.assertIn(reason_text, row["reason"])
        code, out = report([row])
        self.assertEqual(code, 1)
        self.assertIn("INCOMPLETE", out)
        self.assertIn("1 probed · 0 FLAGGED · 1 INCOMPLETE", out)

    def test_sigkill_on_the_auto_tripwire(self):
        self.assert_incomplete(probe({NAME: entry()}, setup_ok(lambda name, text: -9)), "rc -9")

    def test_137_under_a_wrapper(self):
        self.assert_incomplete(probe({NAME: entry()}, setup_ok(lambda name, text: 137)), "rc 137")

    def test_killed_preflight(self):
        self.assert_incomplete(probe({NAME: entry()}, lambda name, text: -9), "rc -9")

    def test_parse_failure_in_the_setup(self):
        # The ladder does not parse (ssreflect out of scope): every probe would fail before searching.
        syntax = (1, "Error: Syntax error: [ltac_expr] expected after '|' (in [ltac_expr]).")
        self.assert_incomplete(probe({NAME: entry()}, lambda name, text: syntax), "probe setup does not compile")

    def test_killed_hint_is_not_stale_fix_ok(self):
        # Snippets fail normally; only the witness hint's run is killed.
        row = probe({HINTED: entry()}, setup_ok(lambda name, text: 1 if name == "probe.v" else -9), HINTED)
        self.assert_incomplete(row, "hint")

    def test_hint_imports_that_do_not_load(self):
        answer = lambda name, text: 1 if name == "hint_setup.v" else (0 if PREFLIGHT_MARK in text else 1)
        self.assert_incomplete(probe({HINTED: entry()}, answer, HINTED), "the imports of the hint")

    def test_killed_instantiation_run(self):
        # Only the small-model run (its scratch file holds the __probe_inst_ definitions) is killed.
        row = probe({NAME: entry(BINDERS)}, setup_ok(lambda name, text: -9 if "__probe_inst_" in text else 1))
        self.assert_incomplete(row, "rc -9")

    def test_small_model_file_failing_outside_fail(self):
        row = probe({NAME: entry(BINDERS)}, setup_ok(lambda name, text: 1))
        self.assert_incomplete(row, "outside its Fail commands")

    def test_unknown_name_is_not_found_and_fails(self):
        # A misspelled or renamed statement in --names / a wave row: no coqc run at all.
        row = probe({NAME: entry()}, lambda name, text: 0, "no_such_statement")
        self.assertEqual((row["status"], row["flag"]), ("NOT-FOUND", False))
        code, out = report([row])
        self.assertEqual(code, 1)
        self.assertIn("1 probed · 0 FLAGGED · 1 NOT-FOUND (not in the index)", out)


class UnchangedVerdicts(unittest.TestCase):
    def test_healthy_statement_is_ok(self):
        # Probes fail, every small-model Fail fails as expected (rc 0): the old "ok".
        row = probe({NAME: entry(BINDERS)}, setup_ok(lambda name, text: 0 if "__probe_inst_" in text else 1))
        self.assertEqual(row["status"], "ok")
        code, out = report([row])
        self.assertEqual(code, 0)
        self.assertIn("1 probed · 0 FLAGGED\n", out)
        self.assertNotIn("INCOMPLETE", out)

    def test_timeout_keeps_its_meaning(self):
        row = probe({NAME: entry(BINDERS)}, setup_ok(lambda name, text: 124))
        self.assertEqual(row["status"], "ok")
        self.assertEqual(report([row])[0], 0)

    def test_ordinary_failure_is_ok(self):
        row = probe({HINTED: entry()}, setup_ok(lambda name, text: 1), HINTED)
        self.assertEqual((row["status"], row["hint"]), ("ok", "stale-FIX-OK"))
        self.assertEqual(report([row])[0], 0)

    def test_success_still_flags(self):
        row = probe({NAME: entry()}, setup_ok(lambda name, text: 0 if "Lemma __pt" in text else 1))
        self.assertEqual(row["status"], "FLAGGED")
        self.assertTrue(row["auto_true"])
        self.assertEqual(report([row])[0], 1)

    def test_settling_specialization_still_flags(self):
        settled = (1, "Error: The command has not failed!")
        row = probe({NAME: entry(BINDERS)},
                    setup_ok(lambda name, text: settled if "__probe_inst_" in text else 1))
        self.assertEqual(row["status"], "FLAGGED")
        self.assertTrue(row["instantiation"])


class SnippetShape(unittest.TestCase):
    def test_header_imports_ssreflect_before_the_module(self):
        seen: list[str] = []
        probe({NAME: entry()}, setup_ok(lambda name, text: 1), seen=seen)
        self.assertTrue(seen)
        for text in seen:
            self.assertTrue(text.startswith(f"From mathcomp Require Import all_boot.\n"
                                            f"From {NS}.conjectures Require Import {STEM}.\n"), text[:120])

    def test_hint_setup_is_the_leading_import_block(self):
        text = ("(* a hint *)\nFrom GTBase Require Import\n  base common.\nSet Implicit Arguments.\n"
                "Local Open Scope nat_scope.\nLemma foo : True.\nProof. done. Qed.\n")
        self.assertEqual(VP.hint_setup(text), "From GTBase Require Import\n  base common.\n"
                                              "Set Implicit Arguments.\nLocal Open Scope nat_scope.")


class ValidateFailsClosed(unittest.TestCase):
    """--validate on a fake tree: healthy answers pass; a killed or unloadable row fails."""

    IDX = {name: entry() for name in VP.HISTORICAL_FIXES + VP.CONTROL_GOOD}

    @staticmethod
    def healthy(name, text):
        # Setups compile, the two recall fixtures compile, hints and probes do not.
        if name == "hint_setup.v" or PREFLIGHT_MARK in text:
            return 0
        return 0 if ("__probe_selftest_vacuous_statement" in text
                     or "__probe_inst_fixture_statement" in text) else 1

    def validate(self, answer):
        out = io.StringIO()
        with patch.object(VP, "sh", fake_sh(answer)), contextlib.redirect_stdout(out):
            code = VP.validate(self.IDX, VP.DEFAULT_TIMEOUT, 1)
        return code, out.getvalue()

    def test_healthy_fake_tree_passes(self):
        code, out = self.validate(self.healthy)
        self.assertEqual(code, 0, out)
        self.assertIn("rows without a verdict (no search ran):     0", out)

    def test_killed_control_row_fails(self):
        victim = VP.CONTROL_GOOD[0]
        code, out = self.validate(lambda name, text: -9 if victim in text else self.healthy(name, text))
        self.assertEqual(code, 1, out)
        self.assertIn("rows without a verdict (no search ran):     1", out)

    def test_control_whose_module_does_not_load_fails(self):
        # The preflight of one control row does not compile (an unbuilt library).
        victim = VP.CONTROL_GOOD[0]
        code, out = self.validate(
            lambda name, text: 1 if (victim in text and PREFLIGHT_MARK in text) else self.healthy(name, text))
        self.assertEqual(code, 1, out)
        self.assertIn("probe setup does not compile", out)

    def test_killed_recall_fixture_fails(self):
        code, out = self.validate(
            lambda name, text: -9 if "__probe_selftest_vacuous_statement" in text else self.healthy(name, text))
        self.assertEqual(code, 1, out)
        self.assertIn("!! RECALL: coqc ended abnormally", out)

    def test_control_missing_from_the_index_fails(self):
        idx = {name: row for name, row in self.IDX.items() if name != VP.CONTROL_GOOD[0]}
        out = io.StringIO()
        with patch.object(VP, "sh", fake_sh(self.healthy)), contextlib.redirect_stdout(out):
            code = VP.validate(idx, VP.DEFAULT_TIMEOUT, 1)
        self.assertEqual(code, 1, out.getvalue())
        self.assertIn("rows without a verdict (no search ran):     1", out.getvalue())


if __name__ == "__main__":
    unittest.main(verbosity=2)

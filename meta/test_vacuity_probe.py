#!/usr/bin/env python3
"""vacuity_probe.py fails closed on a killed coqc run; no Rocq needed.

Every coqc call goes through vacuity_probe.sh(), which these tests replace by a fake that answers
from the scratch file it is given (no fake executable: /tmp is noexec in the containers).  A run
killed by a signal (a negative return code, or 137 under a wrapper) must make the statement
INCOMPLETE and the exit code nonzero, in each of the three probe layers and in --validate; the
designed timeout (124), an ordinary failure and an ordinary success keep their old verdicts."""
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


def entry(body: str = "True") -> tuple[str, str, str, str]:
    return (AREA, STEM, NS, body)


def fake_sh(answer):
    """sh() replacement: `answer(file_name, text)` gives the return code of one coqc run."""
    def run(args, timeout):
        path = Path(args[-1])
        rc = answer(path.name, path.read_text())
        return rc, ("<killed>" if VP.killed(rc) else "")
    return run


def probe(idx, answer, name=NAME):
    with patch.object(VP, "sh", fake_sh(answer)):
        return VP.probe_statement(name, idx, VP.DEFAULT_TIMEOUT)


def report(rows):
    out = io.StringIO()
    with contextlib.redirect_stdout(out):
        rc = VP.report(rows)
    return rc, out.getvalue()


class KilledRunIsIncomplete(unittest.TestCase):
    def assert_incomplete(self, row, rc_text):
        self.assertEqual(row["status"], "INCOMPLETE")
        self.assertFalse(row["flag"])
        self.assertIn(rc_text, row["reason"])
        code, out = report([row])
        self.assertEqual(code, 1)
        self.assertIn("INCOMPLETE", out)
        self.assertIn("1 probed · 0 FLAGGED · 1 INCOMPLETE", out)

    def test_sigkill_on_the_auto_tripwire(self):
        self.assert_incomplete(probe({NAME: entry()}, lambda name, text: -9), "rc -9")

    def test_137_under_a_wrapper(self):
        self.assert_incomplete(probe({NAME: entry()}, lambda name, text: 137), "rc 137")

    def test_killed_hint_is_not_stale_fix_ok(self):
        # Snippets fail normally; only the witness hint's run is killed.
        row = probe({HINTED: entry()}, lambda name, text: 1 if name == "probe.v" else -9, HINTED)
        self.assert_incomplete(row, "hint")

    def test_killed_instantiation_run(self):
        # Only the small-model run (its scratch file holds the __probe_inst_ definitions) is killed.
        row = probe({NAME: entry("forall n : nat, 0 < n")},
                    lambda name, text: -9 if "__probe_inst_" in text else 1)
        self.assert_incomplete(row, "rc -9")


class UnchangedVerdicts(unittest.TestCase):
    def test_timeout_keeps_its_meaning(self):
        row = probe({NAME: entry("forall n : nat, 0 < n")}, lambda name, text: 124)
        self.assertEqual(row["status"], "ok")
        code, out = report([row])
        self.assertEqual(code, 0)
        self.assertIn("1 probed · 0 FLAGGED\n", out)
        self.assertNotIn("INCOMPLETE", out)

    def test_ordinary_failure_is_ok(self):
        row = probe({HINTED: entry()}, lambda name, text: 1, HINTED)
        self.assertEqual((row["status"], row["hint"]), ("ok", "stale-FIX-OK"))
        self.assertEqual(report([row])[0], 0)

    def test_success_still_flags(self):
        row = probe({NAME: entry()}, lambda name, text: 0 if "Lemma __pt" in text else 1)
        self.assertEqual(row["status"], "FLAGGED")
        self.assertTrue(row["auto_true"])
        self.assertEqual(report([row])[0], 1)


class ValidateFailsClosed(unittest.TestCase):
    """--validate on a fake tree: healthy answers pass, a killed control row fails."""

    IDX = {name: entry() for name in VP.HISTORICAL_FIXES + VP.CONTROL_GOOD}

    @staticmethod
    def healthy(name, text):
        # The two recall fixtures compile; hints and probes do not (stale-FIX-OK, ok).
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
        self.assertIn("incomplete probes (killed coqc runs):       0", out)

    def test_killed_control_row_fails(self):
        victim = VP.CONTROL_GOOD[0]
        code, out = self.validate(lambda name, text: -9 if victim in text else self.healthy(name, text))
        self.assertEqual(code, 1, out)
        self.assertIn("incomplete probes (killed coqc runs):       1", out)

    def test_killed_recall_fixture_fails(self):
        code, out = self.validate(
            lambda name, text: -9 if "__probe_selftest_vacuous_statement" in text else self.healthy(name, text))
        self.assertEqual(code, 1, out)
        self.assertIn("!! RECALL: coqc ended abnormally", out)


if __name__ == "__main__":
    unittest.main(verbosity=2)

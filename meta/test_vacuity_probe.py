#!/usr/bin/env python3
"""vacuity_probe.py fails closed when a probe could not search; no Rocq needed.

Every coqc call goes through vacuity_probe.sh(), which these tests replace by a fake that answers
from the scratch file it is given (no fake executable: /tmp is noexec in the containers).  A run
killed by a signal (a negative return code, or 137 under a wrapper), a probe setup that does not
compile (a parse error, a module that does not load), hint imports that do not load and a
small-model file that fails outside its Fail commands must each make the statement INCOMPLETE and
the exit code nonzero, in every probe layer and in --validate, and so must a name the index does not
hold (NOT-FOUND); the designed timeout (124), an ordinary failure and an ordinary success keep
their old verdicts.  The gate-tooling item (2026-10-27) adds: the preflight's two Locate checks (a
name that does not resolve to the probed module's definition in the auto layers' or the small
model's context is INCOMPLETE; a long name wrapped after "Constant" still resolves), PARAMETRIC (a
target whose type is a product, not Prop), AMBIGUOUS (a --names name two files define), file-
qualified --files / --wave targets, --target for any Definition, first_error's continuation lines,
and an empty request exiting non-zero.  Temporary trees are only READ (nothing is executed there)."""
from __future__ import annotations

import contextlib
import io
import json
from pathlib import Path
import re
import sys
import tempfile
import unittest
from unittest.mock import patch

import vacuity_probe as VP


AREA, STEM, NS = "chromatic-theory", "X35", "Chromatic"
NAME = "fixture_statement"
HINTED = "sparse_graph_low_chromatic_cut_statement"   # has meta/probe_hints/<name>.v
BINDERS = "forall n : nat, 0 < n"                      # gets a small-model run
PREFLIGHT_MARK = "Goal True. Proof. __probe. Qed."
CLASSIFY_MARK = "forall __vp_x : _, _"                  # only the PARAMETRIC classification run


def locate_log(text: str, first: str | None = None, second: str | None = None, wrap: bool = False) -> str:
    """A coqc log for the preflight snippet `text`: its two Locate commands answered (by default with
    the probed module's own constant, <ns>.conjectures.<stem>.<name> read from the snippet's header),
    around the printed mark."""
    name = re.search(r"Locate (\S+)\.", text).group(1)
    ns, stem = re.search(r"From (\S+)\.conjectures Require Import (\S+)\.", text).groups()
    own = f"{ns}.conjectures.{stem}.{name}"
    sep = "\n" if wrap else " "
    return (f"Constant{sep}{first or own}\n{VP.RESOLUTION_MARK} = 0\n     : nat\n"
            f"Constant{sep}{second or own}\n")


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
    """The probe preflight (with its two Locate answers) and the hint imports compile; every other
    run is `answer`'s."""
    def run(name, text):
        if PREFLIGHT_MARK in text:
            return 0, locate_log(text)
        return 0 if name == "hint_setup.v" else answer(name, text)
    return run


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
        answer = lambda name, text: (1 if name == "hint_setup.v"
                                     else (0, locate_log(text)) if PREFLIGHT_MARK in text else 1)
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
        # Setups compile (the preflight's names resolve), the two recall fixtures compile, hints and
        # probes do not.
        if PREFLIGHT_MARK in text:
            return 0, locate_log(text)
        if name == "hint_setup.v":
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


def fake_tree(files: dict[str, str], waves: dict | None = None):
    """A temporary repository tree to READ: {relative path: text}; patches VP.ROOT and VP.META."""
    td = tempfile.TemporaryDirectory()
    root = Path(td.name).resolve()
    for rel, text in files.items():
        (root / rel).parent.mkdir(parents=True, exist_ok=True)
        (root / rel).write_text(text)
    (root / "meta").mkdir(exist_ok=True)
    (root / "meta" / "v2_statement_waves.json").write_text(json.dumps({"waves": waves or {}}))
    stack = contextlib.ExitStack()
    stack.callback(td.cleanup)
    stack.enter_context(patch.object(VP, "ROOT", root))
    stack.enter_context(patch.object(VP, "META", root / "meta"))
    return stack


CONJ = "chromatic-theory/theories/conjectures"


class Resolution(unittest.TestCase):
    """The preflight's two Locate checks: both must name the probed module's own definition."""

    def run_with(self, first=None, second=None, wrap=False, log=None):
        def answer(name, text):
            if PREFLIGHT_MARK in text:
                return 0, (log if log is not None else locate_log(text, first, second, wrap))
            return 1
        return probe({NAME: entry()}, answer)

    def test_wrong_module_in_the_auto_context(self):
        row = self.run_with(first=f"{NS}.conjectures.Other.{NAME}")
        self.assertEqual(row["status"], "INCOMPLETE")
        self.assertIn(f"auto layers: {NS}.conjectures.Other.{NAME}", row["reason"])
        self.assertEqual(report([row])[0], 1)

    def test_wrong_module_in_the_small_model_context(self):
        row = self.run_with(second=f"GTBase.finite_graph.{NAME}")
        self.assertEqual(row["status"], "INCOMPLETE")
        self.assertIn(f"small model: GTBase.finite_graph.{NAME}", row["reason"])

    def test_no_constant_printed(self):
        row = self.run_with(log="")
        self.assertEqual(row["status"], "INCOMPLETE")
        self.assertIn("<none>", row["reason"])

    def test_wrapped_long_name_resolves(self):
        # Positive control: Rocq breaks the line after "Constant" for a long qualified name.
        row = self.run_with(wrap=True)
        self.assertEqual(row["status"], "ok")
        want = f"{NS}.conjectures.{STEM}.{NAME}"
        self.assertEqual(row["resolved"], (want, want))
        code, out = report([row])
        self.assertEqual(code, 0)
        self.assertIn(f"RESOLVED {NAME} -> {want} | {want}", out)

    def test_both_locates_are_in_the_preflight(self):
        seen: list[str] = []
        probe({NAME: entry()}, setup_ok(lambda name, text: 1), seen=seen)
        pre = next(text for text in seen if PREFLIGHT_MARK in text)
        self.assertEqual(pre.count(f"Locate {NAME}."), 2)
        # The first Locate precedes the finite_graph import (the auto layers' context), the second follows it.
        self.assertLess(pre.index(f"Locate {NAME}."), pre.index("Require Import finite_graph"))
        self.assertGreater(pre.rindex(f"Locate {NAME}."), pre.index("Require Import finite_graph"))


class Parametric(unittest.TestCase):
    TYPE_ERROR = (1, 'Error:\nThe term "fixture_statement" has type "(nat -> Prop) -> Prop"\n'
                     'while it is expected to have type "Prop".')

    def classify(self, classification_rc, seen=None):
        def answer(name, text):
            if CLASSIFY_MARK in text:
                return classification_rc
            return self.TYPE_ERROR if PREFLIGHT_MARK in text else 1
        return probe({NAME: entry()}, answer, seen=seen)

    def test_product_type_is_parametric_and_fails(self):
        row = self.classify(0)
        self.assertEqual(row["status"], "PARAMETRIC")
        self.assertIn("--target", row["reason"])
        code, out = report([row])
        self.assertEqual(code, 1)
        self.assertIn("1 probed · 0 FLAGGED · 1 PARAMETRIC", out)

    def test_classification_that_fails_is_incomplete(self):
        row = self.classify(1)
        self.assertEqual(row["status"], "INCOMPLETE")
        # first_error keeps the continuation of a bare "Error:".
        self.assertIn('has type "(nat -> Prop) -> Prop"', row["reason"])

    def test_killed_classification_is_incomplete(self):
        row = self.classify(-9)
        self.assertEqual(row["status"], "INCOMPLETE")
        self.assertIn("rc -9", row["reason"])

    def test_healthy_row_never_classifies(self):
        seen: list[str] = []
        row = probe({NAME: entry()}, setup_ok(lambda name, text: 1), seen=seen)
        self.assertEqual(row["status"], "ok")
        self.assertFalse(any(CLASSIFY_MARK in text for text in seen))

    def test_instance_candidates_are_listed(self):
        files = {f"{CONJ}/A.v": "Definition p_statement (q : nat -> Prop) : Prop := forall n, q n.\n",
                 f"{CONJ}/B.v": ("Definition p_concrete : Prop :=\n  p_statement (fun n => n = n).\n"
                                 "(* Definition p_old : Prop := p_statement (fun _ => True). *)\n"
                                 "Definition p_statement_extra : Prop := True.\n")}
        with fake_tree(files):
            self.assertEqual(VP.instance_candidates("p_statement"), ["chromatic-theory/B:p_concrete"])


class FirstError(unittest.TestCase):
    def test_bare_error_keeps_its_continuation(self):
        log = 'File "./probe.v", line 3:\nError:\nThe term "x" has type "nat"\nwhile it is expected.\n\nmore'
        self.assertEqual(VP.first_error(log), 'Error: The term "x" has type "nat" while it is expected.')

    def test_one_line_error_unchanged(self):
        self.assertEqual(VP.first_error("Error: Syntax error.\nFile x"), "Error: Syntax error.")

    def test_no_error_line_gives_the_last_line(self):
        self.assertEqual(VP.first_error("a\n<timeout>\n"), "<timeout>")


class Targets(unittest.TestCase):
    FILES = {f"{CONJ}/A.v": ("Definition x_statement : Prop := True.\n"
                             "Definition y_statement : Prop := False.\n"
                             "(* Definition z_statement : Prop := True. *)\n"
                             "Definition helper_def : Prop := True.\n"),
             f"{CONJ}/B.v": "Definition x_statement : Prop := False.\n"}

    def test_duplicated_name_is_not_indexed(self):
        with fake_tree(self.FILES):
            idx = VP.build_index()
        self.assertNotIn("x_statement", idx)
        self.assertEqual(idx.dups["x_statement"], ["chromatic-theory/A", "chromatic-theory/B"])
        self.assertEqual(idx["y_statement"][:2], ("chromatic-theory", "A"))

    def test_ambiguous_name_fails_without_a_coqc_run(self):
        idx = VP.Index({NAME: entry()})
        idx.dups["x_statement"] = ["chromatic-theory/A", "chromatic-theory/B"]
        row = probe(idx, lambda name, text: self.fail("no coqc run for an AMBIGUOUS name"), "x_statement")
        self.assertEqual(row["status"], "AMBIGUOUS")
        code, out = report([row])
        self.assertEqual(code, 1)
        self.assertIn("1 AMBIGUOUS", out)

    def test_files_are_probed_against_their_own_module(self):
        with fake_tree(self.FILES):
            targets = VP.targets_from_files([f"{CONJ}/B.v"])
        self.assertEqual([(name, entry[:3]) for name, entry in targets],
                         [("x_statement", ("chromatic-theory", "B", "Chromatic"))])
        seen: list[str] = []
        with patch.object(VP, "sh", fake_sh(setup_ok(lambda name, text: 1), seen)):
            rows = VP.probe_targets(targets, VP.Index(), VP.DEFAULT_TIMEOUT, 1)
        self.assertEqual(rows[0]["status"], "ok")
        self.assertTrue(all("From Chromatic.conjectures Require Import B.\n" in text for text in seen))

    def test_commented_definition_is_not_collected(self):
        with fake_tree(self.FILES):
            names = [name for name, _ in VP.targets_from_files([f"{CONJ}/A.v"])]
        self.assertEqual(names, ["x_statement", "y_statement"])

    def test_file_outside_a_conjecture_directory_exits(self):
        with fake_tree({"chromatic-theory/theories/foundations/F.v": "Definition f_statement : Prop := True.\n"}):
            with self.assertRaises(SystemExit):
                VP.targets_from_files(["chromatic-theory/theories/foundations/F.v"])

    def test_wave_uses_its_defines_file(self):
        waves = {"XT": {"repo": "chromatic-theory", "defines_file": "B.v",
                        "rows": {"r1": {"formal_name": "x_statement"}, "r2": {"formal_name": "y_statement"}}}}
        with fake_tree(self.FILES, waves):
            targets = VP.targets_from_wave("XT")
            with self.assertRaises(SystemExit):
                VP.targets_from_wave("NO_SUCH_WAVE")
        self.assertEqual(targets[0][0], "x_statement")
        self.assertEqual(targets[0][1][:2], ("chromatic-theory", "B"))
        self.assertEqual(targets[1], ("y_statement", None))   # not in B.v: the index decides

    def test_target_any_definition_and_not_found(self):
        with fake_tree(self.FILES):
            targets = VP.targets_from_specs(["chromatic-theory/A:helper_def", "chromatic-theory/A:missing",
                                             "chromatic-theory/NOFILE:helper_def"])
        self.assertEqual(targets[0], ("helper_def", ("chromatic-theory", "A", "Chromatic", " True.")))
        self.assertEqual((targets[1][1]["status"], targets[2][1]["status"]), ("NOT-FOUND", "NOT-FOUND"))
        self.assertEqual(VP.probe_target(targets[1], VP.Index(), VP.DEFAULT_TIMEOUT), targets[1][1])

    def test_empty_request_exits_nonzero(self):
        with patch.object(VP, "build_index", lambda: VP.Index()), \
             patch.object(sys, "argv", ["vacuity_probe.py", "--names", ","]):
            with self.assertRaises(SystemExit) as ctx:
                VP.main()
        self.assertNotIn(ctx.exception.code, (0, None))


if __name__ == "__main__":
    unittest.main(verbosity=2)

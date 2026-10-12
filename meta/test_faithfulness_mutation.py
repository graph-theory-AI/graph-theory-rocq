#!/usr/bin/env python3
"""Tests for the resource guards of meta/faithfulness_mutation.py: a check that ran out of memory, disk or
time, or was killed by a signal, is never counted as a killed mutant.  The checks here are small fake
commands; no Rocq build runs."""

from __future__ import annotations

import dataclasses
import inspect
import os
import signal
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import faithfulness_mutation as FM  # noqa: E402

SIGNATURE = "[FAIL] milestone closure compiles"


class GuardTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.dir = Path(self.tmp.name)

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def check(self, body: str, timeout: int = 60) -> FM.CheckResult:
        script = self.dir / "fake_check.py"
        script.write_text(textwrap.dedent(body))
        return FM.run_guarded([sys.executable, str(script)], self.dir, dict(os.environ), timeout)

    def test_control_killed(self) -> None:
        result = self.check(f"import sys\nprint({SIGNATURE!r})\nsys.exit(1)\n")
        self.assertEqual(FM.mutant_verdict(result, SIGNATURE, 60), (True, f"baseline accepted; killed by {SIGNATURE}"))

    def test_control_survived_and_wrong_reason(self) -> None:
        self.assertEqual(FM.mutant_verdict(self.check("print('ok')\n"), SIGNATURE, 60)[1],
                         "SURVIVED: check_milestone accepted the mutant")
        killed, detail = FM.mutant_verdict(self.check("import sys\nprint('other')\nsys.exit(1)\n"), SIGNATURE, 60)
        self.assertFalse(killed)
        self.assertTrue(detail.startswith("rejected for the wrong reason"))

    def test_killed_marker_is_not_a_kill(self) -> None:
        result = self.check(f"import sys\nprint({SIGNATURE!r})\nprint('Killed')\nsys.exit(1)\n")
        self.assertEqual(FM.mutant_verdict(result, SIGNATURE, 60), (False, "resource: markers ['Killed']"))

    def test_signal_after_the_signature_is_not_a_kill(self) -> None:
        # The case the old rule counted as KILLED: the signature is printed, then the check dies by SIGKILL.
        result = self.check(f"import os, signal, sys\nprint({SIGNATURE!r}, flush=True)\nos.kill(os.getpid(), signal.SIGKILL)\n")
        self.assertEqual(result.returncode, -signal.SIGKILL)
        self.assertEqual(FM.mutant_verdict(result, SIGNATURE, 60), (False, f"resource: signal {int(signal.SIGKILL)}"))

    def test_timeout_is_a_failure_not_an_exception(self) -> None:
        result = self.check(f"import time\nprint({SIGNATURE!r}, flush=True)\ntime.sleep(60)\n", timeout=1)
        self.assertIsNone(result.returncode)
        self.assertEqual(FM.mutant_verdict(result, SIGNATURE, 1), (False, "timed out after 1s"))

    def test_oom_kill_delta_is_a_failure(self) -> None:
        with mock.patch.object(FM, "cgroup_oom_kills", side_effect=[0, 1]):
            result = self.check(f"import sys\nprint({SIGNATURE!r})\nsys.exit(1)\n")
        self.assertEqual(FM.mutant_verdict(result, SIGNATURE, 60), (False, "resource: oom_kill 1"))

    def test_group_not_empty_is_a_failure(self) -> None:
        result = dataclasses.replace(self.check(f"import sys\nprint({SIGNATURE!r})\nsys.exit(1)\n"), group_empty=False)
        self.assertEqual(FM.mutant_verdict(result, SIGNATURE, 60), (False, "resource: the process group is not empty after the kill"))

    def test_detached_leftover_child_is_killed(self) -> None:
        body = (f"import subprocess, sys\nsubprocess.Popen(['sleep', '300'], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)\n"
                f"print({SIGNATURE!r})\nsys.exit(1)\n")
        result = self.check(body)
        self.assertTrue(result.group_empty)
        self.assertEqual(FM.mutant_verdict(result, SIGNATURE, 60)[0], True)

    def test_leftover_child_holding_the_pipes_times_out(self) -> None:
        result = self.check(f"import subprocess, sys\nsubprocess.Popen(['sleep', '300'])\nprint({SIGNATURE!r})\nsys.exit(1)\n", timeout=2)
        self.assertIsNone(result.returncode)
        self.assertTrue(result.group_empty)
        self.assertEqual(FM.mutant_verdict(result, SIGNATURE, 2), (False, "timed out after 2s"))

    def test_baseline_guard(self) -> None:
        result = self.check("import sys\nprint('Cannot allocate memory')\nsys.exit(1)\n")
        self.assertEqual(FM.baseline_verdict(result, 60), "resource: markers ['Cannot allocate memory']")


class ParmutImportTests(unittest.TestCase):
    """The names the batch runner's parmut prototype imports from this module keep today's call shape."""

    def test_names(self) -> None:
        self.assertIsInstance(FM.ROOT, Path)
        self.assertTrue(FM.MUTANTS and all(isinstance(m, FM.Mutant) for m in FM.MUTANTS))
        fields = {f.name for f in dataclasses.fields(FM.Mutant)}
        self.assertLessEqual({"name", "phase", "package", "replacements", "detector", "expected_signature", "note"}, fields)
        self.assertEqual(list(inspect.signature(FM.copy_workspace).parameters), ["mutant", "dst"])
        self.assertEqual(list(inspect.signature(FM.apply_mutation).parameters), ["workspace", "mutant"])
        self.assertIsInstance(FM.ROCQ.environment(), dict)


if __name__ == "__main__":
    unittest.main()

#!/usr/bin/env python3
"""The graph-conjectures clone is used only at the pinned commit; no Rocq needed.

Fixture clones are throwaway git repositories; the pinned commit is patched to the fixture's
HEAD, so these tests never need the real corpus."""
from __future__ import annotations

import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import corpus_registry as REG


FIXTURE_GIT_ENV = {**{k: v for k, v in os.environ.items() if not k.startswith("GIT_")},
                   "GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": os.devnull}


def git(path, *args):
    """Fixture git, isolated from the user's and the system's git configuration (signing, hooks)."""
    return subprocess.run(
        ["git", "-c", "user.email=t@t", "-c", "user.name=t", "-c", "commit.gpgsign=false",
         "-C", str(path), *args],
        check=True, capture_output=True, text=True, env=FIXTURE_GIT_ENV).stdout.strip()


def make_clone(path: Path) -> str:
    """A minimal graph-conjectures-like clone; returns its HEAD."""
    (path / "data").mkdir(parents=True)
    (path / "data/problems.json").write_text("[]\n")
    git(path, "init", "-q", "-b", "main")
    git(path, "add", "data/problems.json")
    git(path, "commit", "-q", "-m", "pinned")
    return git(path, "rev-parse", "HEAD")


class PinnedDiscovery(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="gc-pin-")
        self.addCleanup(temporary.cleanup)
        self.tmp = Path(temporary.name).resolve()
        self.clone = self.tmp / "graph-conjectures"
        self.pin = make_clone(self.clone)
        # no candidate outside the fixture: the monorepo root and HOME point into it, and the
        # monorepo's sibling <mono>/../graph-conjectures does not exist (it is not self.clone)
        self.mono = self.tmp / "work" / "mono"
        self.mono.mkdir(parents=True)
        self.home = self.tmp / "home"
        self.home.mkdir()
        for patcher in (patch.object(REG, "GRAPH_CONJECTURES_COMMIT", self.pin),
                        patch.object(REG, "MONO", str(self.mono)),
                        patch.dict(os.environ, {"HOME": str(self.home)}, clear=False)):
            patcher.start()
            self.addCleanup(patcher.stop)
        os.environ.pop("GRAPH_CONJECTURES", None)

    def use(self, path):
        os.environ["GRAPH_CONJECTURES"] = str(path)

    def test_a_pinned_clean_clone_is_returned(self):
        self.use(self.clone)
        self.assertEqual(REG.graph_conjectures_dir(), str(self.clone))

    def test_a_unset_variable_finds_the_verified_nested_clone(self):
        nested = self.mono / "graph-conjectures"
        os.rename(self.clone, nested)
        self.assertEqual(REG.graph_conjectures_dir(), str(nested))

    def test_b_wrong_head_is_an_error(self):
        (self.clone / "data/other.json").write_text("{}\n")
        git(self.clone, "add", "data/other.json")
        git(self.clone, "commit", "-q", "-m", "elsewhere")
        git(self.clone, "checkout", "-q", "--detach", "HEAD")
        with patch.object(REG, "GRAPH_CONJECTURES_COMMIT", "0" * 40):
            self.use(self.clone)
            with self.assertRaises(REG.GraphConjecturesPinError):
                REG.graph_conjectures_dir()

    def test_c_changed_tracked_data_is_an_error(self):
        (self.clone / "data/problems.json").write_text("[1]\n")
        self.use(self.clone)
        with self.assertRaisesRegex(REG.GraphConjecturesPinError, "changed or untracked"):
            REG.graph_conjectures_dir()

    def test_d_no_candidate_is_still_systemexit(self):
        with self.assertRaises(SystemExit):
            REG.graph_conjectures_dir()

    def test_e_the_ci_fallback_does_not_swallow_a_wrong_clone(self):
        # build_v2_manifest: try: GC = REG.graph_conjectures_dir() except SystemExit: <replay>
        (self.clone / "data/problems.json").write_text("[1]\n")
        self.use(self.clone)
        with self.assertRaises(REG.GraphConjecturesPinError):
            try:
                REG.graph_conjectures_dir()
            except SystemExit:
                self.fail("a wrong clone was read as an absent one")

    def test_f_a_data_dir_inside_another_repository_is_an_error(self):
        inner = self.clone / "copied"
        (inner / "data").mkdir(parents=True)
        (inner / "data/problems.json").write_text("[]\n")
        self.use(inner)
        with self.assertRaisesRegex(REG.GraphConjecturesPinError, "top level"):
            REG.graph_conjectures_dir()

    def test_g_a_descendant_of_the_pin_is_an_error(self):
        # intended: reproduction means exactly the pinned commit, not a later one
        (self.clone / "data/later.json").write_text("{}\n")
        git(self.clone, "add", "data/later.json")
        git(self.clone, "commit", "-q", "-m", "later")
        self.use(self.clone)
        with self.assertRaisesRegex(REG.GraphConjecturesPinError, "not at the pinned commit"):
            REG.graph_conjectures_dir()

    def test_h_an_untracked_file_under_data_is_an_error(self):
        # intended: the data must be exactly the pinned tree
        (self.clone / "data/sub").mkdir()
        (self.clone / "data/sub/extra.json").write_text("{}\n")
        self.use(self.clone)
        with self.assertRaisesRegex(REG.GraphConjecturesPinError, "changed or untracked"):
            REG.graph_conjectures_dir()

    def test_i_the_variable_is_authoritative(self):
        # a valid nested clone exists, but the variable names a directory without data/
        os.rename(self.clone, self.mono / "graph-conjectures")
        empty = self.tmp / "empty"
        empty.mkdir()
        self.use(empty)
        with self.assertRaisesRegex(REG.GraphConjecturesPinError, "no data/"):
            REG.graph_conjectures_dir()

    def test_k_repository_selecting_variables_are_ignored(self):
        # GIT_DIR naming another repository must not decide which repository is checked
        other = self.tmp / "other"
        make_clone(other)
        self.use(self.clone)
        with patch.dict(os.environ, {"GIT_DIR": str(other / ".git"), "GIT_WORK_TREE": str(other)}):
            self.assertEqual(REG.graph_conjectures_dir(), str(self.clone))

    def test_j_data_outside_any_git_checkout_is_an_error(self):
        plain = self.tmp / "plain"
        (plain / "data").mkdir(parents=True)
        self.use(plain)
        with patch.dict(os.environ, {"GIT_CEILING_DIRECTORIES": str(self.tmp)}):
            with self.assertRaisesRegex(REG.GraphConjecturesPinError, "top level"):
                REG.graph_conjectures_dir()


if __name__ == "__main__":
    unittest.main(verbosity=2)

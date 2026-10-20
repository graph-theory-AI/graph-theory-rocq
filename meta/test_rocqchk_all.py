#!/usr/bin/env python3
"""Tests for meta/rocqchk_all.py: the plan, the per-shard verdict (G5), the coverage guards (G1-G4, G6-G8), the scheduler, Shard.poll's
rc mapping and dependency_edges on real .Makefile.coq.d lines.  Synthetic rocqchk outputs use the real 9.1.1 format (an SR-32c
fixture's rocqchk.out: `[intern <path> ...`, `Checking library:` / `Admitting library:`, the CONTEXT SUMMARY block with two-space blank
lines and 4-space axiom entries).  a1 (Marcol F-2): every coverage NEG asserts the EXACT set of tripped guards, and each tamper is
distinct.

a3 (arthur, RC R-10, 2026-10-20): the receipt's source (O-1): SourceIdentity (S1-S10, on temporary git repositories), MainSource
(M1) and ReceiptFixture (F1-F5: main() end to end on a one-module fixture tree with a fake rocqchk).  a1 / a2 (RC G-1, 2026-10-14)
ran at G-1's first execution (48 tests OK).
"""
from __future__ import annotations

import json
import os
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path
from unittest import mock

import rocqchk_all as R

NS = {"GTBase", "Digraph", "Hamilton", "Hom"}
ROOT = "/t/"
PREF = (ROOT + "base/", ROOT + "digraph-theory/")
EXT = ["Corelib.Init.Logic", "Stdlib.Logic.Classical_Prop"]
EXT_VO = {"Corelib.Init.Logic": "/o/lib/coq/theories/Init/Logic.vo",
          "Stdlib.Logic.Classical_Prop": "/o/lib/coq/user-contrib/Stdlib/Logic/Classical_Prop.vo"}
P_VO = {"GTBase.a": ROOT + "base/theories/a.vo", "Digraph.b": ROOT + "digraph-theory/theories/b.vo",
        "Digraph.c": ROOT + "digraph-theory/theories/c.vo"}
NAMES = sorted(P_VO)


def summary(axioms=("Stdlib.Logic.Classical_Prop.classic",), drop=None, raw_axioms=None):
    lines = ["CONTEXT SUMMARY", "===============", "  ", "* Theory: Set is predicative", "  ",
             "* Theory: Rewrite rules are not allowed", "  "]
    if raw_axioms is not None:
        lines += ["* Axioms:"] + list(raw_axioms) + ["  "]
    else:
        lines += (["* Axioms:"] + ["    " + a for a in axioms] + ["  "]) if axioms else ["* Axioms: <none>", "  "]
    lines += ["* Constants/Inductives relying on type-in-type: <none>", "  ",
              "* Constants/Inductives relying on unsafe (co)fixpoints: <none>", "  ",
              "* Inductives whose positivity is assumed: <none>", "  "]
    return "\n".join(l for l in lines if l != drop) + "\n"


def output(checked, admitted, intern_as=None, drop_intern=(), **kw):
    """intern lines for every checked / admitted name (at its own path, or at intern_as[name]), then the library lines, then the
    summary"""
    vo = {**P_VO, **EXT_VO, **(intern_as or {})}
    body = [f"[intern {vo[n]} ... done]" for n in checked + admitted if n not in drop_intern]
    body += [f"Checking library: {n}" for n in checked] + [f"Admitting library: {n}" for n in admitted]
    return "\n".join(body) + "\n" + summary(**kw)


def good():
    """shard 0 = E recursive; shard 1 = the joint load (lists Digraph.c, the root; loads everything); shard 2 = GTBase.a, Digraph.b"""
    outs = {0: output(EXT, []), 1: output(["Digraph.c"], ["GTBase.a", "Digraph.b"] + EXT), 2: output(["GTBase.a", "Digraph.b"], EXT)}
    lists = {0: list(EXT), 1: ["Digraph.c"], 2: ["GTBase.a", "Digraph.b"]}
    return outs, lists


def tripped(outs, lists, externals=EXT):
    return {b.split(":")[0] for b in R.coverage_violations(outs, lists, NAMES, externals, set(P_VO.values()), PREF)}


class ShardVerdict(unittest.TestCase):
    def v(self, rc, out, planned=("Digraph.c",)):
        return R.shard_verdict(rc, out, list(planned), NS)[0]

    def test_pass_with_external_axiom(self):
        self.assertEqual(self.v(0, output(["Digraph.c"], EXT)), "PASS")

    def test_pass_without_axioms(self):
        self.assertEqual(self.v(0, output(["Digraph.c"], EXT, axioms=())), "PASS")

    def test_project_axiom_fails(self):
        v, _, proj, _ = R.shard_verdict(0, output(["Digraph.c"], EXT, axioms=("Digraph.c.ax",)), ["Digraph.c"], NS)
        self.assertEqual((v, proj), ("FAIL", ["Digraph.c.ax"]))

    def test_namespaces_without_public_layer_count(self):
        for ax in ("Hamilton.x.ax", "Hom.y.ax"):
            with self.subTest(ax=ax):
                self.assertEqual(self.v(0, output(["Digraph.c"], EXT, axioms=(ax,))), "FAIL")

    def test_limit_and_kill_are_incomplete(self):
        for rc in (124, 137):
            self.assertEqual(self.v(rc, ""), "INCOMPLETE")

    def test_other_rc_fails(self):
        self.assertEqual(self.v(1, output(["Digraph.c"], EXT)), "FAIL")

    def test_checked_names_must_be_the_planned_list(self):          # a1, Marcol N-1
        self.assertEqual(self.v(0, output(["Digraph.c"], EXT), planned=("Digraph.b",)), "FAIL")
        self.assertEqual(self.v(0, output(["Digraph.c"], EXT), planned=("Digraph.b", "Digraph.c")), "FAIL")

    def test_empty_plan_fails(self):
        self.assertEqual(self.v(0, output(["Digraph.c"], EXT), planned=()), "FAIL")

    def test_each_summary_line_is_required(self):
        for drop in ("* Theory: Set is predicative", "* Theory: Rewrite rules are not allowed",
                     "* Constants/Inductives relying on type-in-type: <none>",
                     "* Constants/Inductives relying on unsafe (co)fixpoints: <none>",
                     "* Inductives whose positivity is assumed: <none>", "* Axioms:", "CONTEXT SUMMARY"):
            with self.subTest(drop=drop):
                self.assertEqual(self.v(0, output(["Digraph.c"], EXT, drop=drop)), "FAIL")

    def test_two_summaries_fail(self):
        self.assertEqual(self.v(0, output(["Digraph.c"], EXT) + summary()), "FAIL")

    def test_malformed_axiom_entry_fails(self):                     # 5 spaces, as sr32b's `^    [^ ]`
        self.assertEqual(self.v(0, output(["Digraph.c"], EXT, raw_axioms=["     Stdlib.x"])), "FAIL")

    def test_axioms_header_with_empty_list_fails(self):
        self.assertEqual(self.v(0, output(["Digraph.c"], EXT, raw_axioms=[])), "FAIL")


class Coverage(unittest.TestCase):
    def test_good_run_trips_nothing(self):
        self.assertEqual(tripped(*good()), set())

    def test_externals_from_joint(self):
        self.assertEqual(R.externals_from_joint(good()[0][1], NAMES), sorted(EXT))

    def test_G1_module_missing_from_the_partition(self):
        outs, lists = good(); lists[2] = ["GTBase.a"]
        self.assertEqual(tripped(outs, lists), {"G1"})

    def test_G1_shard0_list_is_not_E(self):
        outs, lists = good(); lists[0] = EXT[:1]
        self.assertEqual(tripped(outs, lists), {"G1"})

    def test_G2_shard0_loads_a_project_file(self):
        # shard 0 interns GTBase.a's file in place of Classical_Prop's (counts intact, so G7 holds); the -norec shards' Classical_Prop
        # file is then not in shard 0's set, so G3 trips with it (inherent: shard 0's file set is fixed at |E|)
        outs, lists = good(); outs[0] = output(EXT, [], intern_as={"Stdlib.Logic.Classical_Prop": P_VO["GTBase.a"]})
        self.assertEqual(tripped(outs, lists), {"G2", "G3"})

    def test_G3_external_not_checked_by_shard0(self):
        outs, lists = good(); outs[2] = output(["GTBase.a", "Digraph.b"], EXT, intern_as={"Stdlib.Logic.Classical_Prop": "/o/Stray.vo"})
        self.assertEqual(tripped(outs, lists), {"G3"})

    def test_G4_stray_project_file(self):
        outs, lists = good(); outs[2] = output(["GTBase.a", "Digraph.b"], EXT, intern_as={"Digraph.b": ROOT + "digraph-theory/theories/zz.vo"})
        self.assertEqual(tripped(outs, lists), {"G4"})

    def test_G6_library_checked_twice(self):
        outs, lists = good(); outs[2] = output(["GTBase.a", "Digraph.b", "Digraph.c"], EXT)
        self.assertEqual(tripped(outs, lists), {"G6"})

    def test_G6_loaded_never_checked(self):
        # a -norec shard ADMITS a name nobody checks, at a file shard 0 did intern (G3 and G7 hold)
        outs, lists = good()
        outs[2] = output(["GTBase.a", "Digraph.b"], [EXT[0], "Stdlib.Ghost"], intern_as={"Stdlib.Ghost": EXT_VO[EXT[1]]})
        self.assertEqual(tripped(outs, lists), {"G6"})

    def test_G7_no_intern_lines(self):
        outs, lists = good(); outs[2] = output(["GTBase.a", "Digraph.b"], EXT, drop_intern=["GTBase.a", "Digraph.b"] + EXT)
        self.assertEqual(tripped(outs, lists), {"G7"})

    def test_G7_one_intern_line_missing(self):
        outs, lists = good(); outs[2] = output(["GTBase.a", "Digraph.b"], EXT, drop_intern=["Digraph.b"])
        self.assertEqual(tripped(outs, lists), {"G7"})

    def test_G7_recursive_shard_admits(self):
        # shard 0 admits Classical_Prop, which shard 2 checks instead: everything is checked once (G6 holds), only G7's rule trips
        outs, lists = good(); outs[0] = output(EXT[:1], EXT[1:]); outs[2] = output(["GTBase.a", "Digraph.b", EXT[1]], EXT[:1])
        self.assertEqual(tripped(outs, lists), {"G7"})

    def test_G8_joint_shard_misses_a_package_file(self):
        outs, lists = good(); outs[1] = output(["Digraph.c"], ["Digraph.b"] + EXT)
        self.assertEqual(tripped(outs, lists), {"G8"})


class Plan(unittest.TestCase):
    MODS = [{"name": n, "bytes": b} for n, b in (("D.a", 10), ("D.b", 5_000_000), ("D.c", 20), ("D.d", 30), ("D.e", 40))]
    EDGES = {("D.e", "D.a"), ("D.e", "D.b"), ("D.e", "D.c"), ("D.c", "D.d")}

    def plan(self, top=300):
        return R.make_plan(self.MODS, self.EDGES, top, 1_000_000, 19, (4, 5, 28, 10))

    def test_partition_roots_heavy_light(self):
        p = self.plan()
        self.assertEqual(p["roots"], ["D.e"])
        self.assertEqual(p["shards"][1], ["D.e"])
        self.assertEqual(p["shards"][2], ["D.b"])
        self.assertEqual(p["caps"][2], (28, "h"))
        self.assertEqual(R.plan_violations(p, [m["name"] for m in self.MODS]), [])

    def test_heavy_root_stays_in_shard1(self):                     # Marcol F-1: a heavy ROOT is in shard 1, not in lane h
        mods = [dict(m) for m in self.MODS]; mods[4]["bytes"] = 4_000_000
        p = R.make_plan(mods, self.EDGES, 300, 1_000_000, 19, (4, 5, 28, 10))
        self.assertEqual((p["shards"][1], [p["shards"][i] for i in p["shards"] if p["caps"][i][1] == "h"]), (["D.e"], [["D.b"]]))

    def test_big_closure_joins_shard1(self):
        self.assertIn("D.c", self.plan(top=1)["shards"][1])

    def test_root_moved_is_refused(self):
        p = self.plan(); p["shards"][1] = []; p["shards"][99] = ["D.e"]
        self.assertTrue(any(b.startswith("roots") for b in R.plan_violations(p, [m["name"] for m in self.MODS])))

    def test_missing_module_is_refused(self):
        p = self.plan(); p["shards"][2] = []
        self.assertTrue(any(b.startswith("G1") for b in R.plan_violations(p, [m["name"] for m in self.MODS])))


class Stub:
    """a scheduler item without rocqchk: it ends `dur` seconds after its launch with `code`"""
    def __init__(self, i, cap, lane="", dur=0.1, code=0):
        self.i, self.cap, self.lane, self.dur, self.code = i, cap, lane, dur, code

    def launch(self, starts):
        starts.append(self.i)
        self.t0 = time.monotonic()

    def poll(self, limit_s):
        if time.monotonic() - self.t0 < self.dur:
            return False
        self.rc = self.code
        return True


class Schedule(unittest.TestCase):
    """SR-32c's test-sr32c-schedule.sh 3346f1b1, in the same cases"""
    def run_items(self, budget, items):
        starts, log = [], []
        R.schedule(items, budget, 0.01, 999, (starts,), log.append, heartbeat_s=999)
        running = [int(l.split(" running ")[1].split()[0]) for l in log]
        return starts, log, running

    def check_ok(self, budget, caps):
        items = [Stub(i, c) for i, c in enumerate(caps)]
        starts, log, running = self.run_items(budget, items)
        self.assertLessEqual(max(running), budget)
        self.assertEqual(sorted(starts), list(range(len(caps))))
        self.assertEqual(sum(" end " in l for l in log), len(caps))

    def test_P1_waves(self):
        self.check_ok(10, [3, 7, 4, 4, 2, 6])

    def test_P2_all_fit(self):
        self.check_ok(48, [3, 7, 9, 9, 4, 4, 4, 4, 4])

    def test_P3_serial_by_budget(self):
        self.check_ok(9, [9, 9, 9])

    def test_P4_backfill(self):
        starts, _, _ = self.run_items(10, [Stub(0, 8, dur=0.2), Stub(1, 5), Stub(2, 2)])
        self.assertEqual(starts, [0, 2, 1])

    def test_P5_serial_lane(self):
        items = [Stub(0, 4), Stub(1, 22, "h"), Stub(2, 22, "h"), Stub(3, 22, "h"), Stub(4, 10), Stub(5, 10)]
        _, log, running = self.run_items(48, items)
        heavy, peak = 0, 0
        for l in log:
            if " lane h" in l and " start " in l:
                heavy += 1; peak = max(peak, heavy)
            if " end " in l and l.split(" end ")[1].split()[0] in ("1", "2", "3"):
                heavy -= 1
        self.assertEqual(peak, 1)
        self.assertLessEqual(max(running), 48)

    def test_N2_cap_over_budget(self):
        with self.assertRaises(R.Refused):
            self.run_items(10, [Stub(0, 3), Stub(1, 11)])

    def test_N4_repeated_index(self):
        with self.assertRaises(R.Refused):
            self.run_items(10, [Stub(0, 3), Stub(0, 4)])

    def test_N7_bad_lane(self):
        with self.assertRaises(R.Refused):
            self.run_items(10, [Stub(0, 3, "H")])

    def test_N6_early_end_is_counted(self):
        items = [Stub(0, 2, dur=0, code=3), Stub(1, 2, dur=0.2)]
        _, log, _ = self.run_items(10, items)
        self.assertEqual((items[0].rc, sum(" end 0 " in l and " rc 3" in l for l in log)), (3, 1))


class Poll(unittest.TestCase):
    """Shard.poll's rc mapping: a normal exit keeps its code, SIGKILL -> 137, the limit -> 124 (as `timeout`)"""
    def shard(self, argv, d):
        s = R.Shard(5, 1, "", ["X"], False, Path(d))
        (s.dir / "console.txt").write_text("")
        s.out = open(s.dir / "rocqchk.out", "wb")
        s.start = time.monotonic()
        s.proc = subprocess.Popen(argv, stdout=s.out, stderr=subprocess.STDOUT, start_new_session=True)
        return s

    def wait(self, s, limit_s):
        while not s.poll(limit_s):
            time.sleep(0.01)
        return s.rc, (Path(s.dir) / "rocqchk.rc").read_text().strip()

    def test_normal_exit(self):
        with tempfile.TemporaryDirectory() as d:
            self.assertEqual(self.wait(self.shard(["false"], d), 60), (1, "1"))

    def test_sigkill_is_137(self):
        with tempfile.TemporaryDirectory() as d:
            s = self.shard(["sleep", "30"], d); os.kill(s.proc.pid, signal.SIGKILL)
            self.assertEqual(self.wait(s, 60), (137, "137"))

    def test_limit_is_124(self):
        with tempfile.TemporaryDirectory() as d:
            s = self.shard(["sleep", "30"], d)
            self.assertEqual(self.wait(s, 0), (124, "124"))
            self.assertIsInstance(s.max_rss_kb, int)


class Edges(unittest.TestCase):
    """dependency_edges on lines of the real coqdep form (b3-prepared graph-theory-misc/.Makefile.coq.d): cross-package deps are
    `../base/theories/X.vo`, externals are absolute paths (skipped), and the .vos / .vok lines are ignored"""
    def test_real_lines(self):
        with tempfile.TemporaryDirectory() as t:
            root = Path(t)
            files = {"base/_CoqProject": "-R theories GTBase\ntheories/complexity.v\ntheories/base.v\n",
                     "graph-theory-misc/_CoqProject": "-R theories GTMisc\n-Q ../base/theories GTBase\n"
                                                      "theories/foundations/complexity.v\ntheories/foundations/cops.v\n",
                     "base/.Makefile.coq.d": "theories/complexity.vo theories/complexity.glob theories/complexity.v.beautified "
                                             "theories/complexity.required_vo: theories/complexity.v theories/base.vo\n",
                     "graph-theory-misc/.Makefile.coq.d":
                         "theories/foundations/complexity.vo theories/foundations/complexity.glob theories/foundations/complexity.v.beautified "
                         "theories/foundations/complexity.required_vo: theories/foundations/complexity.v ../base/theories/complexity.vo "
                         "/opt/opam/graph-theory-rocq/lib/rocq-runtime/rocqworker "
                         "/opt/opam/graph-theory-rocq/lib/coq/user-contrib/mathcomp/ssreflect/ssrbool.vo\n"
                         "theories/foundations/complexity.vos theories/foundations/complexity.vok theories/foundations/complexity.required_vos: "
                         "theories/foundations/complexity.v ../base/theories/complexity.vos /opt/opam/graph-theory-rocq/lib/rocq-runtime/rocqworker\n"
                         "theories/foundations/cops.vo theories/foundations/cops.glob theories/foundations/cops.v.beautified "
                         "theories/foundations/cops.required_vo: theories/foundations/cops.v ../base/theories/base.vo "
                         "/opt/opam/graph-theory-rocq/lib/rocq-runtime/rocqworker\n"}
            for p, text in files.items():
                (root / p).parent.mkdir(parents=True, exist_ok=True); (root / p).write_text(text)
            for vo in ("base/theories/complexity.vo", "base/theories/base.vo", "graph-theory-misc/theories/foundations/complexity.vo",
                       "graph-theory-misc/theories/foundations/cops.vo"):
                (root / vo).parent.mkdir(parents=True, exist_ok=True); (root / vo).write_bytes(b"x")
            projs = R.projects(root)
            edges = R.dependency_edges(root, projs, R.package_modules(root, projs))
            self.assertEqual(edges, {("GTBase.complexity", "GTBase.base"), ("GTMisc.foundations.complexity", "GTBase.complexity"),
                                     ("GTMisc.foundations.cops", "GTBase.base")})


class Projects(unittest.TestCase):
    def tree(self, t, **pkgs):
        root = Path(t)
        for name, text in pkgs.items():
            (root / name).mkdir(); (root / name / "_CoqProject").write_text(text)
        return root

    def test_own_mapping(self):
        with tempfile.TemporaryDirectory() as t:
            root = self.tree(t, base="-R theories GTBase\ntheories/a.v\n", atlas="-R theories Atlas\n-Q ../base/theories GTBase\n")
            (root / "blueprint").mkdir()
            self.assertEqual(R.projects(root), {"atlas": "Atlas", "base": "GTBase"})

    def test_no_own_mapping_is_refused(self):
        with tempfile.TemporaryDirectory() as t:
            root = self.tree(t, base="-R theories GTBase\n", x="-Q ../base/theories GTBase\n")
            with self.assertRaises(R.Refused):
                R.projects(root)

    def test_hidden_directory_is_not_a_project(self):               # Lancelot 14:11Z
        with tempfile.TemporaryDirectory() as t:
            root = self.tree(t, base="-R theories GTBase\n")
            (root / ".agent-worktrees").mkdir(); (root / ".agent-worktrees" / "_CoqProject").write_text("-R theories Hidden\n")
            self.assertEqual(R.projects(root), {"base": "GTBase"})

    def test_shared_namespace_is_refused(self):
        with tempfile.TemporaryDirectory() as t:
            root = self.tree(t, base="-R theories GTBase\n", other="-R theories GTBase\n")
            with self.assertRaises(R.Refused):
                R.projects(root)

    def test_not_built_is_refused(self):
        with tempfile.TemporaryDirectory() as t:
            root = self.tree(t, base="-R theories GTBase\ntheories/a.v\n")
            with self.assertRaises(R.Refused):
                R.package_modules(root, R.projects(root))


# ---------------------------------------------------------------- a3 (O-1): the receipt's source
GIT_ENV = {"GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": os.devnull, "GIT_AUTHOR_NAME": "fixture", "GIT_AUTHOR_EMAIL": "f@x",
           "GIT_COMMITTER_NAME": "fixture", "GIT_COMMITTER_EMAIL": "f@x", "GIT_AUTHOR_DATE": "2026-01-01T00:00:00Z",
           "GIT_COMMITTER_DATE": "2026-01-01T00:00:00Z"}
C40, T40 = "1" * 40, "2" * 40                             # declared ids that no fixture repository has


def git(cwd, *args):
    """git in a fixture repository: a pinned identity, no system or global configuration, no inherited GIT_* variable"""
    env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
    env.update(GIT_ENV)
    return subprocess.run(["git", "-c", "init.defaultBranch=main", *args], cwd=cwd, env=env, capture_output=True, text=True,
                          check=True).stdout.strip()


def repo(path, files=None):
    """a repository at `path` with `files` (name -> text; default one x.txt) written and everything under `path` committed;
    -> (commit, tree)"""
    path.mkdir(parents=True, exist_ok=True)
    git(path, "init", "-q")
    for name, text in ({"x.txt": "x\n"} if files is None else files).items():
        (path / name).write_text(text)
    git(path, "add", "-A")
    git(path, "commit", "-q", "-m", "fixture")
    return git(path, "rev-parse", "HEAD"), git(path, "rev-parse", "HEAD^{tree}")


class GitTmp(unittest.TestCase):
    """a temporary directory that git discovery never leaves (GIT_CEILING_DIRECTORIES)"""
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.t = Path(self.tmp.name).resolve()
        self.env = mock.patch.dict(os.environ, {"GIT_CEILING_DIRECTORIES": str(self.t)})
        self.env.start()

    def tearDown(self):
        self.env.stop()
        self.tmp.cleanup()

    def nested(self):
        """the O-1 layout: an untracked ROOT inside an enclosing repository whose ids differ and which has a tracked change"""
        ec, et = repo(self.t / "enc")
        (self.t / "enc" / "x.txt").write_text("changed\n")
        root = self.t / "enc" / "tree"
        root.mkdir()
        return root, ec, et


class SourceIdentity(GitTmp):
    def test_S1_toplevel_clean_is_verified(self):
        c, t = repo(self.t / "r")
        self.assertEqual(R.source_identity(self.t / "r", c, t),
                         {"commit": c, "tree": t, "root_is_git_toplevel": True, "git_commit": c, "git_tree": t,
                          "tracked_changes": False, "verified": True, "accepted": True})

    def test_S2_nested_root_reads_no_enclosing_git(self):          # THE REGRESSION (G-1's receipt named 30351d53)
        root, ec, et = self.nested()
        (root / "a.txt").write_text("a\n")
        s = R.source_identity(root, C40, T40)
        self.assertEqual(s, {"commit": C40, "tree": T40, "root_is_git_toplevel": False, "git_commit": None, "git_tree": None,
                             "tracked_changes": None, "verified": False, "accepted": True})
        self.assertNotIn(ec, json.dumps(s))
        self.assertNotIn(et, json.dumps(s))

    def test_S3_no_repository(self):
        root = self.t / "plain"
        root.mkdir()
        s = R.source_identity(root, C40, T40)
        self.assertEqual((s["root_is_git_toplevel"], s["git_commit"], s["git_tree"], s["tracked_changes"], s["verified"],
                          s["accepted"]), (False, None, None, None, False, True))

    def test_S4_toplevel_at_another_commit_is_refused(self):
        c, t = repo(self.t / "r")
        with self.assertRaises(R.Refused):
            R.source_identity(self.t / "r", C40, t)

    def test_S4b_toplevel_with_another_tree_is_refused(self):
        c, t = repo(self.t / "r")
        with self.assertRaises(R.Refused):
            R.source_identity(self.t / "r", c, T40)

    def test_S5_tracked_change_is_recorded_untracked_file_is_not(self):
        c, t = repo(self.t / "r")
        (self.t / "r" / "built.vo").write_text("untracked\n")
        s = R.source_identity(self.t / "r", c, t)
        self.assertEqual((s["tracked_changes"], s["verified"], s["accepted"]), (False, True, True))
        (self.t / "r" / "x.txt").write_text("changed\n")
        s = R.source_identity(self.t / "r", c, t)
        self.assertEqual((s["tracked_changes"], s["verified"], s["accepted"]), (True, False, False))

    def test_S6_malformed_ids_are_refused(self):
        root = self.t / "plain"
        root.mkdir()
        good = "a" * 40
        for bad in ("", "HEAD", "a" * 39, "a" * 41, "A" * 40, "a" * 64, None):
            for args in ((bad, good), (good, bad)):
                with self.subTest(args=args), self.assertRaises(R.Refused):
                    R.source_identity(root, *args)

    def test_S7_unreadable_dot_git_is_refused(self):
        root = self.t / "broken"
        root.mkdir()
        (root / ".git").write_text("gitdir: /nonexistent/.git\n")
        with self.assertRaises(R.Refused):
            R.source_identity(root, C40, T40)

    def test_S8_repository_selecting_variables_are_ignored(self):
        repo(self.t / "other")
        root, _, _ = self.nested()
        c, t = repo(self.t / "top")
        other = {"GIT_DIR": str(self.t / "other" / ".git"), "GIT_WORK_TREE": str(self.t / "other")}
        for extra in (other, dict(other, GIT_WORK_TREE=str(root))):
            with self.subTest(work_tree=extra["GIT_WORK_TREE"]), mock.patch.dict(os.environ, extra):
                s = R.source_identity(root, C40, T40)
                self.assertEqual((s["root_is_git_toplevel"], s["git_commit"], s["accepted"]), (False, None, True))
                s = R.source_identity(self.t / "top", c, t)
                self.assertEqual((s["git_commit"], s["verified"], s["accepted"]), (c, True, True))

    def test_S9_linked_worktree_root_is_a_toplevel(self):
        c, t = repo(self.t / "main")
        git(self.t / "main", "worktree", "add", "-q", "--detach", str(self.t / "wt"), "HEAD")
        s = R.source_identity(self.t / "wt", c, t)
        self.assertEqual((s["root_is_git_toplevel"], s["git_commit"], s["git_tree"], s["verified"], s["accepted"]),
                         (True, c, t, True, True))

    def test_S10_consumer_rule(self):                              # Lancelot 32c19fee; Marcol O-3
        c, t = repo(self.t / "r")
        top = R.source_identity(self.t / "r", c, t)
        (self.t / "r" / "x.txt").write_text("changed\n")
        dirty = R.source_identity(self.t / "r", c, t)
        (self.t / "plain").mkdir()
        archive = R.source_identity(self.t / "plain", c, t)
        self.assertEqual([R.source_accepted(s) for s in (top, archive, dirty)], [True, True, False])
        shapes = {"a toplevel with null git fields": dict(archive, root_is_git_toplevel=True),
                  "verified false with git fields": dict(top, verified=False),
                  "verified without a toplevel": dict(archive, verified=True),
                  "verified at other git ids": dict(top, git_commit=C40),
                  "verified with an unknown tracked state": dict(top, tracked_changes=None),
                  "a malformed declared id": dict(archive, commit="HEAD"),
                  "no source at all": {}}
        for name, s in shapes.items():
            with self.subTest(name):
                self.assertFalse(R.source_accepted(s))


class MainSource(unittest.TestCase):
    def test_M1_ids_are_required_unless_plan_only(self):
        with tempfile.TemporaryDirectory() as d:
            out = Path(d) / "out"
            for mode in ([], ["--shard1-only"]):
                for ids in ([], ["--source-commit", "a" * 40], ["--source-tree", "b" * 40]):
                    with self.subTest(mode=mode, ids=ids):
                        self.assertEqual(R.main(["--out", str(out)] + mode + ids), 2)
                        self.assertFalse(out.exists())


FAKE_ROCQCHK = """#!/bin/sh
if [ "$1" = --version ]; then echo "The Rocq Proof Checker, fake (test_rocqchk_all ReceiptFixture)"; exit 0; fi
cat "$(dirname "$0")/shard1.out"
"""


class ReceiptFixture(GitTmp):
    """main() end to end: a one-module fixture tree (meta/ = the module under test + rocq_toolchain.py; base/ = GTBase.a) and a fake
    rocqchk selected by ROCQ_OPAM_SWITCH (rocq_toolchain.environment's own override); --shard1-only writes receipt.json"""
    def tree(self, root):
        (root / "meta").mkdir(parents=True)
        shutil.copy(R.__file__, root / "meta" / "rocqchk_all.py")
        shutil.copy(Path(R.__file__).with_name("rocq_toolchain.py"), root / "meta" / "rocq_toolchain.py")
        (root / "base" / "theories").mkdir(parents=True)
        (root / "base" / "_CoqProject").write_text("-R theories GTBase\ntheories/a.v\n")
        (root / "base" / ".Makefile.coq.d").write_text("")
        (root / "base" / "theories" / "a.vo").write_bytes(b"a stand-in .vo\n")
        sw = self.t / "switch" / "bin"
        sw.mkdir(parents=True)
        (sw / "rocqchk").write_text(FAKE_ROCQCHK)
        (sw / "rocqchk").chmod(0o755)
        vo = {"GTBase.a": str(root / "base" / "theories" / "a.vo"), "Corelib.Init.Logic": "/fake/Corelib/Init/Logic.vo"}
        (sw / "shard1.out").write_text(output(["GTBase.a"], ["Corelib.Init.Logic"], intern_as=vo, axioms=()))
        return root

    def run_tool(self, root, *args):
        out = self.t / "out"
        p = subprocess.run([sys.executable, "-B", str(root / "meta" / "rocqchk_all.py"), "--out", str(out), "--budget", "1",
                            "--caps", "1,1,1,1", "--min-cpus", "1", "--poll-s", "0.01", *args],
                           env=dict(os.environ, ROCQ_OPAM_SWITCH=str(self.t / "switch")), capture_output=True, text=True, timeout=120)
        return p, out

    def receipt(self, p, out):
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        text = (out / "receipt.json").read_text()
        receipt = json.loads(text)
        self.assertTrue(receipt["verdict"].startswith("ROCQCHK_ALL_SHARD1_ONLY_PASS"), receipt["verdict"])
        self.assertNotIn("head", receipt)
        self.assertNotIn("tracked_changes", receipt)
        return receipt["source"], text

    def test_F1_nested_root_receipt(self):                         # the O-1 layout, end to end
        root, ec, et = self.nested()
        self.tree(root)
        source, text =self.receipt(*self.run_tool(root, "--shard1-only", "--source-commit", C40, "--source-tree", T40))
        self.assertEqual(source, {"commit": C40, "tree": T40, "root_is_git_toplevel": False, "git_commit": None, "git_tree": None,
                                  "tracked_changes": None, "verified": False, "accepted": True})
        self.assertNotIn(ec, text)
        self.assertNotIn(et, text)

    def test_F2_toplevel_root_is_verified(self):
        root = self.tree(self.t / "top")
        c, t = repo(root, {})
        source, _ = self.receipt(*self.run_tool(root, "--shard1-only", "--source-commit", c, "--source-tree", t))
        self.assertEqual(source, {"commit": c, "tree": t, "root_is_git_toplevel": True, "git_commit": c, "git_tree": t,
                                  "tracked_changes": False, "verified": True, "accepted": True})

    def test_F3_toplevel_at_other_ids_is_refused(self):
        root = self.tree(self.t / "top")
        c, t = repo(root, {})
        p, out = self.run_tool(root, "--shard1-only", "--source-commit", C40, "--source-tree", t)
        self.assertEqual(p.returncode, 2, p.stdout + p.stderr)
        self.assertIn("REFUSED", p.stdout)
        self.assertFalse(out.exists())

    def test_F4_ids_are_required_unless_plan_only(self):
        root, _, _ = self.nested()
        self.tree(root)
        p, out = self.run_tool(root, "--shard1-only")
        self.assertEqual((p.returncode, out.exists()), (2, False), p.stdout + p.stderr)
        p, out = self.run_tool(root, "--plan-only")
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        self.assertIn("PLAN_ONLY", p.stdout)
        self.assertFalse((out / "receipt.json").exists())

    def test_F5_toplevel_with_tracked_change_is_not_accepted(self):
        root = self.tree(self.t / "top")
        c, t = repo(root, {})
        (root / "base" / "_CoqProject").write_text("-R theories GTBase\ntheories/a.v\n\n")    # a tracked change, the same plan
        source, _ = self.receipt(*self.run_tool(root, "--shard1-only", "--source-commit", c, "--source-tree", t))
        self.assertEqual((source["tracked_changes"], source["verified"], source["accepted"]), (True, False, False))


if __name__ == "__main__":
    unittest.main()

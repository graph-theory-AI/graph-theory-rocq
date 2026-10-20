#!/usr/bin/env python3
"""Tests for meta/rocqchk_all.py: the plan, the per-shard verdict (G5), the coverage guards (G1-G4, G6-G8), the scheduler, Shard.poll's
rc mapping and dependency_edges on real .Makefile.coq.d lines.  Synthetic rocqchk outputs use the real 9.1.1 format (an SR-32c
fixture's rocqchk.out: `[intern <path> ...`, `Checking library:` / `Admitting library:`, the CONTEXT SUMMARY block with two-space blank
lines and 4-space axiom entries).  a1 (Marcol F-2): every coverage NEG asserts the EXACT set of tripped guards, and each tamper is
distinct.

DRAFT a1 (arthur, RC G-1, 2026-10-14): never executed.
"""
from __future__ import annotations

import os
import signal
import subprocess
import tempfile
import time
import unittest
from pathlib import Path

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


if __name__ == "__main__":
    unittest.main()

#!/usr/bin/env python3
"""Recursive rocqchk of every project module, sharded:  python3 meta/rocqchk_all.py --out DIR [options]

DRAFT a1 (arthur, RC G-1, 2026-10-14; Marcol's review RC-G1-draft-review-by-marcol 73690bc7 applied): never executed.  It ports
batch 2's reviewed SR-32c run (master-SR32c-r2-by-lancelot and addenda 1-4, run master-SR32c-run-1-by-lancelot: SR32C_ROCQCHK_PASS)
from digraph-theory alone to all 17 projects, as one repository command.

Objects:
  P   every `theories/*.v` row of the _CoqProject of every non-hidden top-level directory that has one (hidden directories are not
      projects: Lancelot 14:11Z), as logical names <NS>.<path>, NS read from the package's own `-R theories NS` (or `-Q`) line.
      Every .vo must exist.
  E   the external libraries: every library the joint-load shard loaded that is not in P.  DERIVED from the run.  What binds it to
      the run's coverage is G3 (every external a -norec shard interned was interned, so checked, by shard 0), G6 (checked == P + E,
      each once, every loaded library checked) and G8 (shard 1 loaded all of P, so E is P's whole external closure).  G1's "shard 0's
      list is E" and G7's "shard 0 interned |E|" now compare the run with itself (internal consistency only; Marcol R-2 / N-7).
Shards:
  1   the JOINT-LOAD shard, -norec: every ROOT module of P (no module of P depends on it, from the packages' .Makefile.coq.d) plus
      the modules whose closure exceeds --top files.  It loads all of P and E in ONE environment (G8).  It runs FIRST and ALONE; E is
      read from its output; the run stops if its rc != 0 or E is empty.  A union load rejects a universe inconsistency, also through
      admitted libraries (SR-32c addendum-2).  `--shard1-only` runs only this shard (the first measured step: its elapsed time and max
      RSS size the rest; Marcol F-1).
  0   E, RECURSIVE.  It runs after shard 1.  No `-admit` is ever passed: the -admit-only load form hit an anomaly (SR-32c a1 F-1).
  2.. the rest of P, -norec: each module whose .vo exceeds --heavy bytes (and is not in shard 1) is its own shard in the serial lane
      `h` (peaks are single-certificate transients, and .vo size does not predict them: SR-32c a3); the light modules in name order,
      cut into contiguous shards of about --light-mb own .vo megabytes.
Verdict, per shard (G5, SR-32b's criterion, sr32b-verdict.sh ec2f280c):
  rc 124 (the limit) or 137 (SIGKILL, e.g. an OOM) is INCOMPLETE, never a pass; any other non-zero rc is FAIL.  rc 0 needs exactly
  one CONTEXT SUMMARY with "Set is predicative", "Rewrite rules are not allowed", <none> for type-in-type, unsafe (co)fixpoints and
  assumed positivity, no listed axiom whose root is a project namespace, and (a1, Marcol N-1) the shard's "Checking library:" names
  == its planned list.  Under -norec the summary ALSO lists module-type / functor fields of ADMITTED libraries as axioms (SR-32c
  review question 4): a false FAIL is possible, a false PASS is not; such a FAIL is read by hand (D-5's procedure).
Then, only if every shard passed G5:
  G1  the -norec shards' lists partition P; shard 0's list is E.
  G2  shard 0 interned no project file.
  G3  every external file a -norec shard interned was interned (so checked) by shard 0.
  G4  every project file a -norec shard interned is the .vo of a module of P.
  G6  every library loaded anywhere is CHECKED exactly once, and the checked names are P plus E.
  G7  per shard, the unique `[intern` paths == the "Checking library" + "Admitting library" lines, and > 0; shard 0: == |E| and 0
      admitted (without it G2-G4 would be vacuous on an output without intern lines).
  G8  shard 1 interned exactly the .vo files of P.
Outputs (DIR must not exist and must lie OUTSIDE the repository): plan/ (modules.tsv, roots.txt, shard-<i>.txt, caps.txt,
externals.txt), shard-<i>/ (modules.txt, rocqchk.out, rocqchk.rc, console.txt with a HEARTBEAT every --heartbeat-s, axioms*.txt,
verdict.txt), schedule.log, verdict.txt (one ROCQCHK_ALL_<PASS|INCOMPLETE|FAIL> line, or ROCQCHK_ALL_SHARD1_ONLY_<...>) and
receipt.json.  Exit 0 PASS, 3 INCOMPLETE, 1 FAIL, 2 refused.
Resources: the caps are ADMISSION estimates (running caps <= --budget at every start, serial lanes, backfill: SR-32c's scheduler
a3), measured by SR-32c with the DEFAULT OCaml GC; nothing is enforced per process.  Run it in ONE container with memory >= --budget
GiB and >= --min-cpus CPUs (up to 3-4 shards run at once; Marcol R-4): when the cgroup's memory.max / cpu.max are readable and
below those, the tool refuses.  An overrun OOM-kills a shard, possibly a neighbour (rc 137 -> INCOMPLETE, never PASS).  The
Makefile target pins OCAMLRUNPARAM=s=1M,o=20, the gates' value; the receipt records the value in force.  The caps are expected to stay
conservative under it (the D-4.6 analysis measured lower COMPILE peaks with o=20); rocqchk under o=20 is unmeasured until its first run.
Rocq 9.2: the `[intern`, library-line and CONTEXT SUMMARY formats are verified on 9.1.1 output only, until a D-3 fixture on 9.2.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import signal
import subprocess
import sys
import time
from pathlib import Path

META = Path(__file__).resolve().parent
ROOT = META.parent
sys.path.insert(0, str(META))
import rocq_toolchain as ROCQ  # noqa: E402

OWN_MAPPING_RE = re.compile(r"^-[RQ]\s+theories\s+([A-Za-z][A-Za-z0-9_]*)\s*$")
INTERN_RE = re.compile(r"^\[intern (\S+)", re.M)
LIBRARY_RE = re.compile(r"^(Checking|Admitting) library: (\S+)", re.M)
INCOMPLETE_RC = {124: "the per-shard limit was reached", 137: "SIGKILL, e.g. an OOM"}


class Refused(Exception):
    pass


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


# ---------------------------------------------------------------- the objects (pure given the tree)
def projects(root: Path) -> dict[str, str]:
    """package directory -> its own logical namespace, for every top-level directory with a _CoqProject"""
    out = {}
    for d in sorted(p for p in root.iterdir() if p.is_dir() and not p.name.startswith(".") and (p / "_CoqProject").is_file()):
        own = [m.group(1) for m in map(OWN_MAPPING_RE.match, (d / "_CoqProject").read_text().splitlines()) if m]
        if len(own) != 1:
            raise Refused(f"{d.name}/_CoqProject: {len(own)} own `-R/-Q theories NS` lines, expected 1")
        out[d.name] = own[0]
    if len(set(out.values())) != len(out):
        raise Refused("two packages share a namespace")
    return out


def package_modules(root: Path, projs: dict[str, str]) -> list[dict]:
    """every theories/*.v row of every _CoqProject: {name, package, path (repo-relative .v), vo (absolute), bytes}"""
    mods = []
    for pkg, ns in projs.items():
        for line in (root / pkg / "_CoqProject").read_text().splitlines():
            line = line.strip()
            if line.startswith("theories/") and line.endswith(".v"):
                vo = root / pkg / (line[:-2] + ".vo")
                if not vo.is_file():
                    raise Refused(f"not built: {pkg}/{line[:-2]}.vo")
                name = ns + "." + line[len("theories/"):-2].replace("/", ".")
                mods.append({"name": name, "package": pkg, "path": f"{pkg}/{line}", "vo": str(vo), "bytes": vo.stat().st_size})
    names = [m["name"] for m in mods]
    if not mods or len(set(names)) != len(names):
        raise Refused("the module list is empty or repeats a name")
    return sorted(mods, key=lambda m: m["name"])


def dependency_edges(root: Path, projs: dict[str, str], mods: list[dict]) -> set[tuple[str, str]]:
    """(module, dependency) pairs between modules of P, from every package's .Makefile.coq.d (coqdep; absent -> refused)"""
    by_vo = {os.path.realpath(m["vo"]): m["name"] for m in mods}
    edges = set()
    for pkg in projs:
        dep = root / pkg / ".Makefile.coq.d"
        if not dep.is_file():
            raise Refused(f"{pkg}/.Makefile.coq.d is missing (build the package first)")
        for line in dep.read_text().splitlines():
            if ": " not in line:
                continue
            lhs, rhs = line.split(": ", 1)
            target = lhs.split()[0]
            if not (target.startswith("theories/") and target.endswith(".vo")):
                continue
            src = by_vo.get(os.path.realpath(root / pkg / target))
            for d in rhs.split():
                if d.endswith(".vo"):
                    dst = by_vo.get(os.path.realpath(root / pkg / d))
                    if src and dst and dst != src:
                        edges.add((src, dst))
    return edges


def closure_sizes(names: list[str], edges: set[tuple[str, str]]) -> dict[str, int]:
    """module -> the number of modules of P in its closure (itself included); closures are int bitmasks (3442 modules: ~1.5 MB)"""
    bit = {n: 1 << i for i, n in enumerate(names)}
    deps: dict[str, set[str]] = {n: set() for n in names}
    for a, b in edges:
        deps[a].add(b)
    memo: dict[str, int] = {}
    for start in names:                                   # iterative DFS: the digraph chains are deeper than the recursion limit
        stack = [(start, False)]
        while stack:
            n, done = stack.pop()
            if n in memo:
                continue
            if done:
                mask = bit[n]
                for d in deps[n]:
                    mask |= memo[d]
                memo[n] = mask
            else:
                stack.append((n, True))
                stack.extend((d, False) for d in deps[n] if d not in memo)
    return {n: bin(m).count("1") for n, m in memo.items()}


def make_plan(mods: list[dict], edges: set[tuple[str, str]], top: int, heavy: int, light_mb: int,
              caps: tuple[int, int, int, int]) -> dict:
    """PURE: shard 1 = roots + big-closure modules; heavy modules one per shard (lane h, largest first); light contiguous ranges"""
    names = [m["name"] for m in mods]
    size = {m["name"]: m["bytes"] for m in mods}
    depended = {b for _, b in edges}
    roots = sorted(n for n in names if n not in depended)
    clo = closure_sizes(names, edges)
    first = sorted(set(roots) | {n for n in names if clo[n] > top})
    heavy_mods = sorted((n for n in names if n not in first and size[n] > heavy), key=lambda n: (-size[n], n))
    light = [n for n in names if n not in first and n not in heavy_mods]
    k_light = max(1, -(-sum(size[n] for n in light) // (light_mb * 10 ** 6)))
    per = sum(size[n] for n in light) / k_light
    chunks: list[list[str]] = [[] for _ in range(k_light)]
    s, acc = 0, 0
    for n in light:
        if acc >= per * (s + 1) and s < k_light - 1:
            s += 1
        chunks[s].append(n)
        acc += size[n]
    shards = {1: first}
    for i, n in enumerate(heavy_mods):
        shards[2 + i] = [n]
    for j, chunk in enumerate(ch for ch in chunks if ch):
        shards[2 + len(heavy_mods) + j] = chunk
    c0, c1, ch, cl = caps
    capof = {0: (c0, ""), 1: (c1, "")}
    for i in shards:
        if i >= 2:
            capof[i] = (ch, "h") if i < 2 + len(heavy_mods) else (cl, "")
    return {"roots": roots, "shards": shards, "caps": capof}


def plan_violations(plan: dict, names: list[str]) -> list[str]:
    """PURE: G1 before START (a partition of P, no empty shard) and the roots check (every root in shard 1)"""
    bad = []
    listed = [n for i, ms in plan["shards"].items() if i >= 1 for n in ms]
    if sorted(listed) != sorted(names) or len(set(listed)) != len(listed):
        bad.append("G1: the shard plan is not a partition of the package modules")
    if any(not ms for ms in plan["shards"].values()):
        bad.append("G1: an empty shard")
    missing = sorted(set(plan["roots"]) - set(plan["shards"].get(1, [])))
    if not plan["roots"] or missing:
        bad.append(f"roots: shard 1 lacks {len(missing)} of the {len(plan['roots'])} root modules")
    return bad


# ---------------------------------------------------------------- one shard's verdict (G5, pure)
def summary_flags(out: str, project_ns: set[str]) -> tuple[list[str], list[str], list[str]]:
    """SR-32b's CONTEXT SUMMARY reading -> (problems, project axioms, external axioms)"""
    problems, proj, ext = [], [], []
    lines = out.splitlines()
    starts = [i for i, l in enumerate(lines) if l == "CONTEXT SUMMARY"]
    if len(starts) != 1:
        return [f"context-summary:{len(starts)}"], proj, ext
    tail = lines[starts[0] + 1:]
    want = {"* Theory: Set is predicative": "set-predicative", "* Theory: Rewrite rules are not allowed": "rewrite-rules-not-allowed",
            "* Constants/Inductives relying on type-in-type: <none>": "type-in-type-none",
            "* Constants/Inductives relying on unsafe (co)fixpoints: <none>": "unsafe-fixpoints-none",
            "* Inductives whose positivity is assumed: <none>": "positivity-none"}
    for text, label in want.items():
        if tail.count(text) != 1:
            problems.append(f"{label}:{tail.count(text)}")
    heads = [i for i, l in enumerate(tail) if l in ("* Axioms: <none>", "* Axioms:")]
    if len(heads) != 1:
        problems.append(f"axioms-header:{len(heads)}")
    elif tail[heads[0]] == "* Axioms:":
        for l in tail[heads[0] + 1:]:
            if not l.strip():
                break
            if not l.startswith("    ") or l.startswith("     "):
                problems.append("axioms-entry")
                continue
            name = l.split()[0]
            (proj if name.split(".", 1)[0] in project_ns else ext).append(name)
        if not proj and not ext:
            problems.append("axioms-empty-list")
    return problems, proj, ext


def shard_verdict(rc: int, out: str, planned: list[str], project_ns: set[str]) -> tuple[str, str, list[str], list[str]]:
    """-> (PASS|INCOMPLETE|FAIL, line, project axioms, external axioms).  a1 (Marcol N-1): the a0 count check compared the plan with
    itself; the shard's own "Checking library:" names must now equal its planned list (after the rc, as an incomplete output has
    fewer)"""
    if not planned:
        return "FAIL", f"rc {rc}: an empty planned list", [], []
    if rc in INCOMPLETE_RC:
        return "INCOMPLETE", f"rc {rc}: {INCOMPLETE_RC[rc]} (not a pass)", [], []
    if rc != 0:
        return "FAIL", f"rc {rc}: rocqchk failed", [], []
    checked = sorted(n for k, n in LIBRARY_RE.findall(out) if k == "Checking")
    if checked != sorted(planned):
        return "FAIL", f"rc 0: checked {len(checked)} libraries, not the {len(planned)} planned ones", [], []
    problems, proj, ext = summary_flags(out, project_ns)
    if problems:
        return "FAIL", "rc 0: CONTEXT SUMMARY check: " + " ".join(problems), proj, ext
    if proj:
        return "FAIL", f"rc 0: {len(proj)} axiom(s) in a project namespace: {' '.join(proj[:5])}", proj, ext
    return "PASS", f"modules {len(planned)}; axioms {len(proj) + len(ext)}, all outside the project namespaces", proj, ext


# ---------------------------------------------------------------- the coverage guards (pure over the shard outputs)
def interned(out: str) -> list[str]:
    return sorted(set(INTERN_RE.findall(out)))


def coverage_violations(outs: dict[int, str], lists: dict[int, list[str]], names: list[str], externals: list[str],
                        package_vo: set[str], project_prefixes: tuple[str, ...]) -> list[str]:
    """G1-G4 and G6-G8 over complete outputs (every shard passed G5).  Paths are compared as text, prefixes literally."""
    bad = []
    is_project = lambda p: p.startswith(project_prefixes)  # noqa: E731
    for i, out in sorted(outs.items()):                                                              # G7
        libs = LIBRARY_RE.findall(out)
        ni, nc, na = len(interned(out)), sum(k == "Checking" for k, _ in libs), sum(k == "Admitting" for k, _ in libs)
        if ni == 0 or ni != nc + na:
            bad.append(f"G7: shard {i}: {ni} unique intern paths != {nc} checking + {na} admitting")
        if i == 0 and (ni != len(externals) or na != 0):
            bad.append(f"G7: shard 0 (recursive): {ni} interned, {na} admitted, externals {len(externals)}")
    norec = [i for i in outs if i >= 1]
    if sorted(n for i in norec for n in lists[i]) != sorted(names):                                    # G1
        bad.append("G1: the -norec shards' module lists are not the package, once each")
    if sorted(lists[0]) != sorted(externals):
        bad.append("G1: shard 0's module list is not the externals list")
    rec = set(interned(outs[0]))
    if any(is_project(p) for p in rec):                                                               # G2
        bad.append(f"G2: shard 0 loaded {sum(is_project(p) for p in rec)} project file(s)")
    ext_loaded = {p for i in norec for p in interned(outs[i]) if not is_project(p)}
    if ext_loaded - rec:                                                                              # G3
        bad.append(f"G3: {len(ext_loaded - rec)} external file(s) loaded by a -norec shard, not by shard 0")
    proj_loaded = {p for i in norec for p in interned(outs[i]) if is_project(p)}
    if proj_loaded - package_vo:                                                                      # G4
        bad.append(f"G4: {len(proj_loaded - package_vo)} project file(s) loaded by a -norec shard are not package modules")
    joint = {p for p in interned(outs[1]) if is_project(p)}
    if joint != package_vo:                                                                           # G8
        bad.append(f"G8: shard 1 did not load exactly the whole package in one environment ({len(joint)} of {len(package_vo)})")
    checked = [n for i in sorted(outs) for k, n in LIBRARY_RE.findall(outs[i]) if k == "Checking"]  # G6
    loaded = {n for i in outs for _, n in LIBRARY_RE.findall(outs[i])}
    if len(checked) != len(set(checked)):
        bad.append(f"G6: {len(checked) - len(set(checked))} librar(ies) checked more than once")
    if set(checked) != loaded:
        bad.append("G6: a loaded library was never checked")
    if set(checked) != set(names) | set(externals):
        bad.append("G6: the checked libraries are not the package plus the externals")
    return bad


def externals_from_joint(out: str, names: list[str]) -> list[str]:
    """E = every library shard 1 loaded that is not a module of P (verified afterwards by G2, G3, G6, G7)"""
    return sorted({n for _, n in LIBRARY_RE.findall(out)} - set(names))


# ---------------------------------------------------------------- running (not pure)
def rocqchk_argv(root: Path, projs: dict[str, str], modules: list[str], recursive: bool) -> list[str]:
    argv = ["rocqchk", "-o"]
    for pkg, ns in projs.items():
        argv += ["-Q", str(root / pkg / "theories"), ns]
    for m in modules:
        argv += [m] if recursive else ["-norec", m]
    return argv


class Shard:
    def __init__(self, i: int, cap: int, lane: str, modules: list[str], recursive: bool, out: Path):
        self.i, self.cap, self.lane, self.modules, self.recursive, self.dir = i, cap, lane, modules, recursive, out
        self.proc = None
        self.start = 0.0

    def launch(self, root: Path, projs: dict[str, str], env: dict[str, str]) -> None:
        self.dir.mkdir(parents=True)
        (self.dir / "modules.txt").write_text("".join(m + "\n" for m in self.modules))
        argv = rocqchk_argv(root, projs, self.modules, self.recursive)
        (self.dir / "console.txt").write_text(f"shard {self.i} {'rec' if self.recursive else 'norec'}; modules {len(self.modules)}; "
                                              f"cap {self.cap} GiB{(' lane ' + self.lane) if self.lane else ''}\nSTART {utc()}\n")
        self.out = open(self.dir / "rocqchk.out", "wb")
        self.start = time.monotonic()
        self.proc = subprocess.Popen(argv, cwd=root, env=env, stdin=subprocess.DEVNULL, stdout=self.out,
                                     stderr=subprocess.STDOUT, start_new_session=True)

    def poll(self, limit_s: int) -> bool:
        """True when finished; records rocqchk.rc (124 on the limit) and the child's own peak RSS (wait4)"""
        pid, status, usage = os.wait4(self.proc.pid, os.WNOHANG)
        timed_out = False
        if pid == 0:
            if time.monotonic() - self.start <= limit_s:
                return False
            os.killpg(self.proc.pid, signal.SIGKILL)
            pid, status, usage = os.wait4(self.proc.pid, 0)
            timed_out = True
        self.out.close()
        rc = 124 if timed_out else (os.waitstatus_to_exitcode(status) if os.WIFEXITED(status) else 128 + os.WTERMSIG(status))
        self.rc, self.elapsed, self.max_rss_kb = rc, round(time.monotonic() - self.start), usage.ru_maxrss
        (self.dir / "rocqchk.rc").write_text(f"{rc}\n")
        with open(self.dir / "console.txt", "a") as f:
            f.write(f"END {utc()} rc={rc} elapsed {self.elapsed} s max_rss {self.max_rss_kb} kB\n")
        return True

    def heartbeat(self) -> None:
        """a1 (Marcol N-4; SR-32c inner's 10-min HEARTBEAT): progress of a running shard, to its console.txt"""
        with open(self.dir / "rocqchk.out", "rb") as f:
            text = f.read().decode(errors="replace")
        done = sum(1 for k, _ in LIBRARY_RE.findall(text) if k == "Checking")
        last = text.rstrip("\n").rsplit("\n", 1)[-1][:120]
        with open(self.dir / "console.txt", "a") as f:
            f.write(f"HEARTBEAT {utc()} elapsed {round(time.monotonic() - self.start)} s; checked {done} libraries; last: {last}\n")


def utc() -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


LANE_RE = re.compile(r"^[a-z]?$")


def schedule(shards: list, budget: int, poll_s: float, limit_s: int, launch_args: tuple, log, heartbeat_s: float = 600) -> None:
    """SR-32c a3's rules: plan order, backfill, serial lanes, running caps <= budget at every start; completion by each item's own
    poll (wait4 on the tool's own unreaped child; no wait -n).  Items need .i .cap .lane, launch(*launch_args), poll(limit_s) and
    may have heartbeat().  a1 (Marcol F-2; test-sr32c-schedule.sh N2-N4, N7): REFUSES a cap outside 1..budget, a repeated index and
    a lane name that is not one lowercase letter, before anything starts."""
    seen = set()
    for s in shards:
        if not (isinstance(s.cap, int) and 1 <= s.cap <= budget) or s.i in seen or not LANE_RE.match(s.lane):
            raise Refused(f"SCHED: item {s.i} (cap {s.cap}, lane {s.lane!r}): cap outside 1..{budget}, repeated index or bad lane")
        seen.add(s.i)
    queue, running, used, beat = list(shards), [], 0, time.monotonic()
    while queue or running:
        rest = []
        for s in queue:
            busy = s.lane and any(r.lane == s.lane for r in running)
            if used + s.cap <= budget and not busy:
                s.launch(*launch_args)
                running.append(s)
                used += s.cap
                log(f"SCHED {utc()} start {s.i} cap {s.cap} running {used}{(' lane ' + s.lane) if s.lane else ''}")
            else:
                rest.append(s)
        queue = rest
        if not running:
            raise Refused("SCHED: queued shards cannot start with nothing running")
        time.sleep(poll_s)
        for s in list(running):
            if s.poll(limit_s):
                running.remove(s)
                used -= s.cap
                log(f"SCHED {utc()} end {s.i} cap {s.cap} running {used} rc {s.rc}")
        if time.monotonic() - beat >= heartbeat_s:
            beat = time.monotonic()
            for s in running:
                if hasattr(s, "heartbeat"):
                    s.heartbeat()


def cgroup_limits() -> tuple[int | None, float | None]:
    """(memory.max bytes, CPUs from cpu.max) of the caller's cgroup v2, None when unlimited or unreadable"""
    mem = cpus = None
    try:
        raw = Path("/sys/fs/cgroup/memory.max").read_text().strip()
        mem = int(raw) if raw.isdigit() else None
    except OSError:
        pass
    try:
        quota, period = Path("/sys/fs/cgroup/cpu.max").read_text().split()[:2]
        cpus = int(quota) / int(period) if quota.isdigit() else None
    except (OSError, ValueError):
        pass
    return mem, cpus


def git_read(*args: str) -> str:
    """a1 (Marcol N-3): reads never refresh the index"""
    return subprocess.run(["git", "--no-optional-locks", *args], cwd=ROOT, capture_output=True, text=True).stdout


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--out", required=True, type=Path, help="a fresh directory OUTSIDE the repository")
    mode = ap.add_mutually_exclusive_group()
    mode.add_argument("--plan-only", action="store_true", help="write plan/ and stop; nothing is checked")
    mode.add_argument("--shard1-only", action="store_true", help="run the joint-load shard 1 alone and stop (a sizing measurement)")
    ap.add_argument("--top", type=int, default=300, help="closure size (files) that puts a module into shard 1 (SR-32c TOP_THR)")
    ap.add_argument("--heavy", type=int, default=1_000_000, help=".vo bytes above which a module is its own serial shard")
    ap.add_argument("--light-mb", type=int, default=19, help="own .vo megabytes per light shard")
    ap.add_argument("--caps", default="4,5,28,10", help="GiB admission estimates: shard 0, shard 1, heavy, light (SR-32c R1)")
    ap.add_argument("--budget", type=int, default=48, help="GiB: running caps never exceed it at a start")
    ap.add_argument("--min-cpus", type=int, default=4, help="refused below this many CPUs in the caller's cgroup (Marcol R-4)")
    ap.add_argument("--limit-s", type=int, default=10800, help="per-shard limit in seconds (SR-32c LIMIT_S)")
    ap.add_argument("--heartbeat-s", type=int, default=600, help="seconds between HEARTBEAT lines (SR-32c inner: 600)")
    ap.add_argument("--poll-s", type=float, default=5.0)
    a = ap.parse_args(argv)
    try:
        caps = tuple(int(x) for x in a.caps.split(","))
        if len(caps) != 4 or min(caps) < 1 or max(caps) > a.budget:
            raise Refused("--caps needs 4 positive GiB values, each <= --budget")
        out = a.out.resolve()
        if out.exists():
            raise Refused(f"{out} exists")
        if out.is_relative_to(ROOT):                      # a1 (Marcol N-5): never leave untracked run files in the repository
            raise Refused(f"{out} is inside the repository {ROOT}")
        mem, cpus = cgroup_limits()                       # a1 (Marcol R-4): only refuses, and only on a readable, smaller limit
        if mem is not None and mem < a.budget * 2 ** 30:
            raise Refused(f"the cgroup's memory.max {mem} B < --budget {a.budget} GiB")
        if cpus is not None and cpus < a.min_cpus:
            raise Refused(f"the cgroup's cpu.max gives {cpus:g} CPUs < --min-cpus {a.min_cpus}")
        projs = projects(ROOT)
        mods = package_modules(ROOT, projs)
        names = [m["name"] for m in mods]
        plan = make_plan(mods, dependency_edges(ROOT, projs, mods), a.top, a.heavy, a.light_mb, caps)
        bad = plan_violations(plan, names)
        if bad:
            raise Refused("; ".join(bad))
        (out / "plan").mkdir(parents=True)
        (out / "plan" / "modules.tsv").write_text("".join(f"{m['name']}\t{m['path']}\t{m['bytes']}\n" for m in mods))
        (out / "plan" / "roots.txt").write_text("".join(r + "\n" for r in plan["roots"]))
        for i, ms in plan["shards"].items():
            (out / "plan" / f"shard-{i}.txt").write_text("".join(n + "\n" for n in ms))
        (out / "plan" / "caps.txt").write_text("".join(f"{i} {c} {g}".rstrip() + "\n" for i, (c, g) in sorted(plan["caps"].items())))
        size = {m["name"]: m["bytes"] for m in mods}
        print(f"PLAN modules {len(names)} in {len(projs)} projects; roots {len(plan['roots'])}; shard 1 {len(plan['shards'][1])} modules "
              f"{sum(size[n] for n in plan['shards'][1]) / 1e6:.1f} MB; shards 0..{max(plan['shards'])} "
              f"({sum(1 for c in plan['caps'].values() if c[1] == 'h')} heavy, serial); budget {a.budget} GiB; limit {a.limit_s} s")
        if a.plan_only:
            print("PLAN_ONLY: nothing checked")
            return 0
        env = ROCQ.environment()
        version = subprocess.run(["rocqchk", "--version"], env=env, capture_output=True, text=True).stdout.strip()
        log_f = open(out / "schedule.log", "w")
        log = lambda line: (log_f.write(line + "\n"), log_f.flush(), print(line))  # noqa: E731
        ns = set(projs.values())
        launch = (ROOT, projs, env)
        s1 = Shard(1, plan["caps"][1][0], "", plan["shards"][1], False, out / "shard-1")
        schedule([s1], a.budget, a.poll_s, a.limit_s, launch, log, a.heartbeat_s)
        externals = externals_from_joint((out / "shard-1" / "rocqchk.out").read_text(errors="replace"), names) if s1.rc == 0 else []
        (out / "plan" / "externals.txt").write_text("".join(e + "\n" for e in externals))
        rest, stop = [], None
        if a.shard1_only:
            stop = "--shard1-only"
        elif s1.rc != 0:                                  # E is unknown and the joint load failed: nothing else is worth hours
            stop = f"shard 1 rc {s1.rc}"
        elif not externals:                               # a1 (Marcol N-2): an output without library lines
            stop = "shard 1 rc 0 but no external library derived (an output without library lines?)"
        if stop:
            log(f"STOP: {stop}; shards 0 and 2.. not run")
        else:
            rest.append(Shard(0, plan["caps"][0][0], "", externals, True, out / "shard-0"))
            rest += [Shard(i, plan["caps"][i][0], plan["caps"][i][1], ms, False, out / f"shard-{i}")
                     for i, ms in sorted(plan["shards"].items()) if i >= 2]
            schedule(rest, a.budget, a.poll_s, a.limit_s, launch, log, a.heartbeat_s)
        shards = {s.i: s for s in [s1] + rest}
        verdict, lines, outs = "PASS", [], {}
        for i, s in sorted(shards.items()):
            text = (s.dir / "rocqchk.out").read_text(errors="replace")
            outs[i] = text
            v, line, proj, ext = shard_verdict(s.rc, text, externals if i == 0 else plan["shards"][i], ns)
            (s.dir / "axioms.project.txt").write_text("".join(x + "\n" for x in proj))
            (s.dir / "axioms.external.txt").write_text("".join(x + "\n" for x in ext))
            (s.dir / "verdict.txt").write_text(f"{v} {line}\n")
            lines.append(f"shard {i}: {v} {line}")
            verdict = "FAIL" if "FAIL" in (v, verdict) else ("INCOMPLETE" if "INCOMPLETE" in (v, verdict) else verdict)
        if stop and not a.shard1_only and verdict == "PASS":
            verdict, lines = "FAIL", lines + [f"STOP: {stop}"]
        guards = []
        if verdict == "PASS" and not a.shard1_only:
            prefixes = tuple(str(ROOT / pkg) + "/" for pkg in projs)
            package_vo = {m["vo"] for m in mods}
            lists = {i: s.modules for i, s in shards.items()}
            guards = coverage_violations(outs, lists, names, externals, package_vo, prefixes)
            if guards:
                verdict = "FAIL"
        if a.shard1_only:                                 # a measurement, never the whole check's verdict
            final = (f"ROCQCHK_ALL_SHARD1_ONLY_{verdict} shard 1: {len(s1.modules)} of {len(names)} modules listed; externals "
                     f"{len(externals)}; elapsed {s1.elapsed} s; max_rss {s1.max_rss_kb} kB (not a verdict on the whole check)")
        else:
            final = (f"ROCQCHK_ALL_{verdict} modules {len(names)} + externals {len(externals)} in {len(shards)} shards; "
                     f"guards failed: {' '.join(sorted({g.split(':')[0] for g in guards})) or 'none'}")
        for l in lines + guards + [final]:
            print(l)
        (out / "verdict.txt").write_text("\n".join(lines + guards + [final]) + "\n")
        receipt = {"tool": "meta/rocqchk_all.py", "tool_sha256": sha256(Path(__file__)), "head": git_read("rev-parse", "HEAD").strip(),
                   "tracked_changes": bool(git_read("status", "--porcelain", "--untracked-files=no")),
                   "rocqchk_version": version, "ocamlrunparam": os.environ.get("OCAMLRUNPARAM"), "budget_gib": a.budget,
                   "cgroup_memory_max": mem, "cgroup_cpus": cpus, "os_cpu_count": os.cpu_count(), "limit_s": a.limit_s,
                   "mode": "shard1-only" if a.shard1_only else "full",
                   "args": {"top": a.top, "heavy": a.heavy, "light_mb": a.light_mb, "caps": list(caps), "min_cpus": a.min_cpus},
                   "modules": len(names), "externals": len(externals), "projects": projs, "stop": stop,
                   "shards": {str(i): {"modules": len(s.modules), "mode": "rec" if s.recursive else "norec", "cap_gib": s.cap,
                                       "lane": s.lane, "rc": s.rc, "elapsed_s": s.elapsed, "max_rss_kb": s.max_rss_kb,
                                       "rocqchk_out_sha256": sha256(s.dir / "rocqchk.out")} for i, s in sorted(shards.items())},
                   "guards_failed": guards, "verdict": final}
        (out / "receipt.json").write_text(json.dumps(receipt, indent=1, sort_keys=True) + "\n")
        return {"PASS": 0, "INCOMPLETE": 3}.get(verdict, 1)
    except Refused as exc:
        print(f"REFUSED: {exc}")
        return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

#!/usr/bin/env python3
"""Mutation tests for the statement-faithfulness checks.

The runner copies the minimum workspace needed for a target milestone, mutates
the copy, and then requires ``check_milestone.py`` to reject the mutant for the
expected reason.  This validates the checks themselves without dirtying the real
worktree.

The first two canaries exercise the exact-type faithfulness gate.  These are the
signatures that would have caught the historical U4-style failure:

  * an undecided row made trivially true, with a committed direct proof;
  * an undecided row made false, with a committed unconditional refutation.

The next canaries mutate load-bearing definitions and require existing
grounding / settled-case lemmas to fail compilation.  A surviving mutant means
that the current faithfulness net did not notice a targeted semantic drift.
The v2 canaries exercise the prospective static lint on the historical
quantifier-order and fixed-ratio-for-whp defect classes.
"""

from __future__ import annotations

import argparse
import dataclasses
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import textwrap
import time
from pathlib import Path

import rocq_toolchain as ROCQ


ROOT = Path(__file__).resolve().parents[1]
# Exact-type canaries request a milestone-scoped build; other canaries retain
# the historical finite bound around their full detector.
DEFAULT_TIMEOUT = 300

# Resource guards (the reviewed parmut r4 F2 / F3 guards of the batch runner): a check that ran out of
# memory, disk or time, or was killed by a signal, is never counted as a killed mutant.  They are
# checked on the baseline and on the mutant call BEFORE the kill rule.  The timeout value is unchanged.
CGROUP = Path("/sys/fs/cgroup")
RESOURCE_MARKERS = ("No space left on device", "ENOSPC", "Cannot allocate memory", "ENOMEM", "Killed", "Error 137")
GRACE_S = 5


def cgroup_oom_kills() -> int | None:
    """The oom_kill counter of this container's cgroup v2 memory.events, or None where it is unreadable
    (no cgroup v2, e.g. macOS: the guard is then unavailable).  It counts the WHOLE container, so an
    OOM kill of a concurrent process also fails the check: that fails closed, which is acceptable."""
    try:
        text = (CGROUP / "memory.events").read_text()
    except OSError:
        return None
    for line in text.splitlines():
        parts = line.split()
        if len(parts) == 2 and parts[0] == "oom_kill" and parts[1].isdigit():
            return int(parts[1])
    return None


def group_live(pgid: int) -> list[int]:
    """The non-zombie processes of a process group, from this machine's own /proc (a zombie never
    counts as live and is reaped when it is our child).  Without /proc (macOS) the POSIX probe
    killpg(pgid, 0) is used, where a zombie counts as live: that fails closed."""
    if os.path.isdir("/proc"):
        live = []
        for entry in os.listdir("/proc"):
            if not entry.isdigit():
                continue
            try:
                stat = Path(f"/proc/{entry}/stat").read_text()
            except OSError:
                continue
            fields = stat[stat.rindex(")") + 2:].split()      # after "pid (comm) ": state ppid pgrp ...
            if int(fields[2]) != pgid:
                continue
            if fields[0] == "Z":
                try:
                    os.waitpid(int(entry), os.WNOHANG)
                except ChildProcessError:
                    pass
                continue
            live.append(int(entry))
        return live
    try:
        os.killpg(pgid, 0)
    except ProcessLookupError:
        return []
    except PermissionError:
        pass
    return [pgid]


def kill_group(pgid: int) -> bool:
    """TERM the call's process group, wait a grace, KILL, then wait until no live process of the group
    remains -> True iff the group is empty."""
    for sig, wait in ((signal.SIGTERM, GRACE_S), (signal.SIGKILL, 10)):
        if not group_live(pgid):
            return True
        try:
            os.killpg(pgid, sig)
        except ProcessLookupError:
            return True
        deadline = time.time() + wait
        while time.time() < deadline:
            if not group_live(pgid):
                return True
            time.sleep(0.1)
    return not group_live(pgid)


@dataclasses.dataclass(frozen=True)
class CheckResult:
    returncode: int | None          # None: the call timed out
    stdout: str
    stderr: str
    group_empty: bool
    oom_kill_delta: int | None      # None: memory.events unreadable here
    markers: tuple[str, ...]

    @property
    def output(self) -> str:
        return self.stdout + self.stderr


def run_guarded(command: list[str], cwd: Path, env: dict[str, str], timeout: int) -> CheckResult:
    """One check call in its own session: the timeout, then the group kill; the oom_kill delta and the
    resource markers recorded."""
    oom_before = cgroup_oom_kills()
    proc = subprocess.Popen(command, cwd=cwd, env=env, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, start_new_session=True)
    timed_out = False
    try:
        stdout, stderr = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        timed_out = True
        kill_group(proc.pid)
        stdout, stderr = proc.communicate()
    empty = kill_group(proc.pid)
    oom_after = cgroup_oom_kills()
    delta = None if oom_before is None or oom_after is None else oom_after - oom_before
    text = (stdout or "") + (stderr or "")
    return CheckResult(None if timed_out else proc.returncode, stdout or "", stderr or "", empty, delta,
                       tuple(m for m in RESOURCE_MARKERS if m in text))


def resource_failure(result: CheckResult, timeout: int) -> str | None:
    """The guards, in order -> the FAILED detail, or None."""
    if result.oom_kill_delta:
        return f"resource: oom_kill {result.oom_kill_delta}"
    if result.markers:
        return f"resource: markers {list(result.markers)}"
    if not result.group_empty:
        return "resource: the process group is not empty after the kill"
    if result.returncode is not None and result.returncode < 0:
        return f"resource: signal {-result.returncode}"
    if result.returncode is None:
        return f"timed out after {timeout}s"
    return None


@dataclasses.dataclass(frozen=True)
class Replacement:
    relpath: str
    definition: str
    command: str


@dataclasses.dataclass(frozen=True)
class Appendix:
    relpath: str
    text: str


@dataclasses.dataclass(frozen=True)
class Mutant:
    name: str
    phase: str
    package: str
    replacements: tuple[Replacement, ...]
    appendices: tuple[Appendix, ...]
    expected_signature: str
    note: str
    detector: str = "milestone"


# The exact-type fixtures use the open list-total-colouring row, whose only
# external references are metadata comments. The former bounded-order row now
# has a migration equivalence proof: mutating it stops compilation at that proof
# before the intended exact-type detector can run. Only temporary copies change.
MUTANTS = [
    Mutant(
        name="u4_open_row_trivial_true_direct_proof",
        phase="U4",
        package="chromatic-theory",
        replacements=(
            Replacement(
                "chromatic-theory/theories/conjectures/U4.v",
                "list_total_colouring_statement",
                "Definition list_total_colouring_statement : Prop :=\n  True.",
            ),
        ),
        appendices=(
            Appendix(
                "chromatic-theory/theories/conjectures/grounding_U4.v",
                """

(** MUTATION TEST CANARY: this lemma is written only in a temporary copy.
    If committed, it would prove an open row directly and must be rejected by
    the exact-type faithfulness gate. *)
Lemma mutation_direct_proof_list_total_colouring_statement :
  list_total_colouring_statement.
Proof. exact I. Qed.
""",
            ),
        ),
        expected_signature="direct-proof-undecided",
        note="trivializes an open row (no dependent theorem, so the exact-type gate is what must catch it) to True and commits a direct proof",
        detector="milestone-scoped",
    ),
    Mutant(
        name="u4_open_row_false_unconditional_refutation",
        phase="U4",
        package="chromatic-theory",
        replacements=(
            Replacement(
                "chromatic-theory/theories/conjectures/U4.v",
                "list_total_colouring_statement",
                "Definition list_total_colouring_statement : Prop :=\n  False.",
            ),
        ),
        appendices=(
            Appendix(
                "chromatic-theory/theories/conjectures/grounding_U4.v",
                """

(** MUTATION TEST CANARY: this lemma is written only in a temporary copy.
    If committed, it would refute a non-disproved row unconditionally and must
    be rejected by the exact-type faithfulness gate. *)
Lemma mutation_refutes_list_total_colouring_statement :
  ~ list_total_colouring_statement.
Proof. by []. Qed.
""",
            ),
        ),
        expected_signature="unconditional-refutation",
        note="mutates an open row to False and commits an unconditional refutation",
        detector="milestone-scoped",
    ),
    Mutant(
        name="u4_open_row_alias_hidden_direct_proof",
        phase="U4",
        package="chromatic-theory",
        replacements=(
            Replacement(
                "chromatic-theory/theories/conjectures/U4.v",
                "list_total_colouring_statement",
                "Definition list_total_colouring_statement : Prop :=\n  True.",
            ),
        ),
        appendices=(
            Appendix(
                "chromatic-theory/theories/conjectures/grounding_U4.v",
                """

(** A transparent alias must not hide a forbidden direct proof from the gate. *)
Definition mutation_statement_alias : Prop :=
  list_total_colouring_statement.
Definition mutation_hidden_direct_proof : mutation_statement_alias := I.
""",
            ),
        ),
        expected_signature="direct-proof-undecided",
        note=("hides a direct proof of a trivialized open row behind a transparent alias; "
              "targets a row that no implication proof uses structurally"),
        detector="milestone-scoped",
    ),
    Mutant(
        name="base_list_colourable_on_total_coloring",
        phase="U4",
        package="chromatic-theory",
        replacements=(
            Replacement(
                "base/theories/base.v",
                "list_colourable_on",
                """
Definition list_colourable_on (G : sgraph) (C : finType) (L : G -> {set C}) (W : {set G}) : Prop :=
  exists f : G -> C,
    (forall v : G, v \\in W -> f v \\in L v) /\\
    (forall x y : G, x \\in W -> y \\in W -> x -- y -> f x != f y).
""",
            ),
        ),
        appendices=(),
        expected_signature="[FAIL] milestone closure compiles",
        note="reintroduces the historical total-colouring bug for list_colourable_on",
        detector="milestone-scoped",
    ),
    Mutant(
        name="base_girth_geq_without_genuine_cycle_guard",
        phase="U1",
        package="chromatic-theory",
        replacements=(
            Replacement(
                "base/theories/base.v",
                "girth_geq",
                """
Definition girth_geq (G : sgraph) (g : nat) : Prop :=
  forall c : seq G, ucycle (--) c -> g <= size c.
""",
            ),
        ),
        appendices=(),
        expected_signature="[FAIL] milestone closure compiles",
        note="drops the load-bearing 2 < size c guard from girth_geq",
        detector="milestone-scoped",
    ),
    Mutant(
        name="base_wagner_planar_trivial_true",
        phase="U7",
        package="minor-theory",
        replacements=(
            Replacement(
                "base/theories/base.v",
                "wagner_planar",
                """
Definition wagner_planar (G : sgraph) : Prop := True.
""",
            ),
        ),
        appendices=(),
        expected_signature="[FAIL] milestone closure compiles",
        note="weakens the Wagner-planarity guard to True",
        detector="milestone-scoped",
    ),
    Mutant(
        name="base_has_girth_drops_witness_cycle",
        phase="U13",
        package="graph-theory-misc",
        replacements=(
            Replacement(
                "base/theories/base.v",
                "has_girth",
                """
Definition has_girth (G : sgraph) (g : nat) : Prop :=
  girth_geq G g.
""",
            ),
        ),
        appendices=(),
        expected_signature="[FAIL] milestone closure compiles",
        note="weakens exact girth by deleting the required witnessed g-cycle",
        detector="milestone-scoped",
    ),
    Mutant(
        name="u4_strongly_colorable_exists_partition",
        phase="U4",
        package="chromatic-theory",
        replacements=(
            Replacement(
                "chromatic-theory/theories/conjectures/U4.v",
                "strongly_colorable",
                """
Definition strongly_colorable (G : sgraph) (r : nat) : Prop :=
  exists P : {set {set G}},
    partition P [set: G] /\\ (forall B : {set G}, B \\in P -> #|B| <= r) /\\
    exists f : G -> 'I_r,
      (forall x y : G, x -- y -> f x != f y) /\\
      (forall B : {set G}, B \\in P -> {in B &, injective f}).
""",
            ),
        ),
        appendices=(),
        expected_signature="[FAIL] milestone closure compiles",
        note="flips strongly_colorable from all partitions to one partition",
        detector="milestone-scoped",
    ),
    Mutant(
        name="cycle_subdeg_counts_loop_once",
        phase="X212",
        package="cycle-theory",
        replacements=(
            Replacement(
                "cycle-theory/theories/foundations/connectivity.v",
                "subdeg",
                """
Definition subdeg (G : mgraph) (H : {set edge G}) (v : G) : nat :=
  #|edges_at v :&: H|.
""",
            ),
        ),
        appendices=(),
        expected_signature="[FAIL] package compiles",
        note=("reverts subdeg to the incidence count, giving a LOOP degree 1 instead of the "
              "textbook 2; killed inside the foundation by connectivity.subdeg_loop and "
              "downstream by grounding_U6.mdeg_Gloop / grounding_X212.x212_mdeg_Lp, the "
              "lemmas that make the one-vertex one-loop multigraph a circuit and an even "
              "subgraph"),
    ),
    Mutant(
        name="base_surface_vertices_orbit_count",
        phase="X213",
        package="chromatic-theory",
        replacements=(
            Replacement(
                "base/theories/surface.v",
                "surface_embedding_vertices",
                """
Definition surface_embedding_vertices (E : surface_embedding) : nat :=
  #|porbits (surface_erot E)|.
""",
            ),
        ),
        appendices=(),
        expected_signature="[FAIL] package compiles",
        note=("reverts the Euler-formula vertex count of base/theories/surface.v to the "
              "rotation-orbit count repaired on 2026-09-23, which by surface_erot_vertex sees "
              "only the vertices CARRYING A DART: isolated vertices become invisible and every "
              "edgeless graph is pushed to genus 1, so surface_euler_genus overstates the genus "
              "of any graph with an isolated vertex and the surface rows (X150/X152/X164/X210/"
              "X213/X219, X167, X138/X202) silently admit fewer graphs than intended; killed "
              "inside the foundation by surface.surface_edgeless_genus0 and the canary "
              "surface.surface_embeddable_K1 (K_1 is planar)"),
    ),
    Mutant(
        name="x185_class_bound_quantifier_swap",
        phase="X185",
        package="chromatic-theory",
        replacements=(
            Replacement(
                "chromatic-theory/theories/conjectures/X185.v",
                "every_multigraph_widespread_statement",
                """
Definition every_multigraph_widespread_statement : Prop :=
  forall (H : mgraph) (nu ell : nat) (G : sgraph),
    loopless H ->
    ω([set: G]) <= nu ->
    exists c : nat,
      c < χ([set: G]) ->
      x185_contains_induced_long_subdivision G (line_graph H) ell.
""",
            ),
        ),
        appendices=(),
        expected_signature="[exists-after-graph-forall]",
        note="moves the class-uniform widespreadness threshold inside forall G",
        detector="lint",
    ),
    Mutant(
        name="x125_fixed_ratio_for_whp",
        phase="X125",
        package="extremal-graph-theory",
        replacements=(
            Replacement(
                "extremal-graph-theory/theories/conjectures/X125.v",
                "x125_almost_all",
                """
Definition x125_almost_all
    (ell : nat -> nat) (P : forall n : nat, sgraph -> Prop) : Prop :=
  exists (M : x125_lift_model ell)
         (good : forall n : nat, pred (x125_sample M n)),
    (forall n : nat,
       @fg_event_at_least_ratio (x125_sample M n) (@x125_weight ell M n)
         (good n) 9 10) /\\
    forall (n : nat) (x : x125_sample M n),
      good n x -> P n (@x125_observe ell M n x).
""",
            ),
        ),
        appendices=(),
        expected_signature="[fixed-ratio-whp]",
        note="replaces ratio-to-one whp with a fixed 9/10 event threshold",
        detector="lint",
    ),
]


BUILD_SUFFIXES = (
    ".aux",
    ".coqaux",
    ".glob",
    ".timing",
    ".vio",
    ".vo",
    ".vok",
    ".vos",
)
BUILD_NAMES = {
    "__pycache__",
    "Makefile.coq",
}


def ignore_build_artifacts(_dir: str, names: list[str]) -> list[str]:
    ignored = []
    for name in names:
        if name in BUILD_NAMES or name.startswith("._"):
            ignored.append(name)
        elif name.endswith(BUILD_SUFFIXES):
            ignored.append(name)
    return ignored


def sibling_deps(package: str) -> list[str]:
    """Sibling packages the target references in its _CoqProject (e.g. hamiltonicity-theory
    and packing-theory map ../topological-graph-theory) — the sandbox build fails without them.
    Comments are stripped line-wise; references to non-existent directories are skipped with a
    warning rather than crashing the suite."""
    cqp = ROOT / package / "_CoqProject"
    if not cqp.is_file():
        return []
    deps = []
    for raw in cqp.read_text().splitlines():
        line = raw.split("#", 1)[0]
        for dep in re.findall(r"-[QR]\s+\.\./([\w.-]+)/theories\s+\S+", line):
            if (ROOT / dep).is_dir():
                deps.append(dep)
            else:
                print(f"  [warn] {package}/_CoqProject references missing sibling ../{dep} — skipped",
                      file=sys.stderr)
    return deps


def copy_workspace(mutant: Mutant, dst: Path) -> None:
    """Copy the minimal monorepo subset needed by check_milestone."""
    # The fidelity registry includes the area-local D7 complexity surface, so lint mutants
    # need that source present even when their target package is elsewhere.
    rels = ["meta", "base", mutant.package]
    # Fidelity fragments can enroll an area foundation outside the mutated
    # package. The copied gate must inspect those same source declarations.
    import foundation_fidelity as fidelity

    for spec in fidelity.load_registry()["modules"].values():
        package = Path(spec["path"]).parts[0]
        if package not in rels:
            rels.append(package)
    # Explicit public migration sources need not own a fidelity fragment. The
    # copied registry must still resolve their current source paths.
    from family_registry import load_library_registry

    for spec in load_library_registry(ROOT)["primitives"].values():
        for source in spec.get("repository_sources", {}).values():
            package = Path(source["path"]).parts[0]
            if package not in rels:
                rels.append(package)
    if "graph-theory-misc" not in rels:
        rels.append("graph-theory-misc")
    for dep in sibling_deps(mutant.package):
        if dep not in rels:
            rels.append(dep)
    for rel in rels:
        shutil.copytree(
            ROOT / rel,
            dst / rel,
            ignore=ignore_build_artifacts,
            symlinks=True,
        )


def coq_sentence_end(src: str, start: int) -> int:
    """Return the end offset of the Rocq sentence beginning at start."""
    i = start
    while True:
        j = src.find(".", i)
        if j < 0:
            raise ValueError("unterminated Rocq sentence")
        nxt = src[j + 1 : j + 2]
        if not nxt or nxt.isspace():
            return j + 1
        i = j + 1


def replace_definition(path: Path, definition: str, replacement_command: str) -> None:
    src = path.read_text()
    prefix = f"Definition {definition}"
    start = src.find(prefix)
    if start < 0:
        raise ValueError(f"definition not found: {definition}")
    end = coq_sentence_end(src, start)
    replacement = textwrap.dedent(replacement_command).strip()
    path.write_text(src[:start] + replacement + src[end:])


def apply_mutation(workspace: Path, mutant: Mutant) -> None:
    for repl in mutant.replacements:
        replace_definition(workspace / repl.relpath, repl.definition, repl.command)
    for appendix in mutant.appendices:
        with (workspace / appendix.relpath).open("a") as f:
            f.write(textwrap.dedent(appendix.text).lstrip("\n"))


def run_check(workspace: Path, mutant: Mutant, timeout: int) -> CheckResult:
    env = ROCQ.environment()
    if mutant.detector == "lint":
        command = [sys.executable, "meta/faithfulness_lint.py", "--files",
                   *sorted({replacement.relpath for replacement in mutant.replacements}),
                   "--check"]
    else:
        if mutant.detector == "milestone-scoped":
            env["CHECK_MILESTONE_SCOPED_BUILD"] = mutant.phase
        command = [sys.executable, "meta/check_milestone.py", mutant.phase, mutant.package]
    return run_guarded(command, workspace, env, timeout)


def baseline_verdict(baseline: CheckResult, timeout: int) -> str | None:
    """None when the unmutated workspace was accepted cleanly; otherwise the FAILED detail."""
    failure = resource_failure(baseline, timeout)
    if failure:
        return failure
    if baseline.returncode != 0:
        tail = baseline.output[-800:].replace("\n", "\\n")
        return f"BASELINE REJECTED before mutation; tail={tail}"
    return None


def mutant_verdict(proc: CheckResult, signature: str, timeout: int) -> tuple[bool, str]:
    """The resource guards first; then the kill rule: KILLED iff a non-zero exit and the expected signature."""
    failure = resource_failure(proc, timeout)
    if failure:
        return False, failure
    output = proc.output
    killed = proc.returncode != 0 and signature in output
    if killed:
        return True, f"baseline accepted; killed by {signature}"
    if proc.returncode == 0:
        return False, "SURVIVED: check_milestone accepted the mutant"
    tail = output[-800:].replace("\n", "\\n")
    return False, f"rejected for the wrong reason; expected {signature}; tail={tail}"


def run_mutant(mutant: Mutant, timeout: int, keep: bool) -> tuple[bool, str, Path | None]:
    tmp = Path(tempfile.mkdtemp(prefix=f"faith-mut-{mutant.name}-"))
    kept: Path | None = tmp if keep else None
    try:
        copy_workspace(mutant, tmp)
        failure = baseline_verdict(run_check(tmp, mutant, timeout), timeout)
        if failure:
            return False, failure, kept
        apply_mutation(tmp, mutant)
        killed, detail = mutant_verdict(run_check(tmp, mutant, timeout), mutant.expected_signature, timeout)
        return killed, detail, kept
    finally:
        if not keep:
            shutil.rmtree(tmp, ignore_errors=True)


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--timeout", type=int, default=DEFAULT_TIMEOUT)
    parser.add_argument("--keep", action="store_true", help="keep temporary mutant workspaces")
    parser.add_argument("--list", action="store_true", help="list available mutants and exit")
    parser.add_argument("--mutant", action="append", choices=[m.name for m in MUTANTS],
                        help="run only the named mutant; may be repeated")
    args = parser.parse_args(argv)

    selected = MUTANTS
    if args.mutant:
        wanted = set(args.mutant)
        selected = [m for m in MUTANTS if m.name in wanted]

    if args.list:
        for mutant in selected:
            print(f"{mutant.name}: {mutant.note}")
        return 0

    contracts = subprocess.run(
        [sys.executable, "meta/gate_contracts.py"], cwd=ROOT, text=True
    )
    if contracts.returncode != 0:
        print("REJECTED: gate-contract regression fixture failed")
        return 1

    failures = 0
    print(f"running {len(selected)} faithfulness mutation canary/canaries")
    for mutant in selected:
        print(f"- {mutant.name}: {mutant.note}")
        try:
            ok, detail, kept = run_mutant(mutant, args.timeout, args.keep)
        except subprocess.TimeoutExpired:
            ok, detail, kept = False, f"timed out after {args.timeout}s", None
        status = "KILLED" if ok else "FAILED"
        print(f"  [{status}] {detail}")
        if kept is not None:
            print(f"  kept workspace: {kept}")
        failures += 0 if ok else 1

    if failures:
        print(f"\nREJECTED: {failures}/{len(selected)} mutation canaries did not die as expected")
        return 1
    print(f"\nACCEPTED: {len(selected)}/{len(selected)} mutation canaries killed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))

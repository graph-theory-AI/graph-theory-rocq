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

The remaining canaries mutate load-bearing definitions and require existing
grounding / settled-case lemmas to fail compilation.  A surviving mutant means
that the current faithfulness net did not notice a targeted semantic drift.
"""

from __future__ import annotations

import argparse
import dataclasses
import os
import re
import shutil
import subprocess
import sys
import tempfile
import textwrap
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_TIMEOUT = 180


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


MUTANTS = [
    Mutant(
        name="u4_open_row_trivial_true_direct_proof",
        phase="U4",
        package="chromatic-theory",
        replacements=(
            Replacement(
                "chromatic-theory/theories/conjectures/U4.v",
                "choice_number_of_k_chromatic_graphs_of_bounded_order_statement",
                "Definition choice_number_of_k_chromatic_graphs_of_bounded_order_statement : Prop :=\n  True.",
            ),
        ),
        appendices=(
            Appendix(
                "chromatic-theory/theories/conjectures/grounding_U4.v",
                """

(** MUTATION TEST CANARY: this lemma is written only in a temporary copy.
    If committed, it would prove an open row directly and must be rejected by
    the exact-type faithfulness gate. *)
Lemma mutation_direct_proof_choice_number_of_k_chromatic_graphs_of_bounded_order_statement :
  choice_number_of_k_chromatic_graphs_of_bounded_order_statement.
Proof. exact I. Qed.
""",
            ),
        ),
        expected_signature="direct-proof-undecided",
        note="trivializes an open row (no dependent theorem, so the exact-type gate is what must catch it) to True and commits a direct proof",
    ),
    Mutant(
        name="u4_open_row_false_unconditional_refutation",
        phase="U4",
        package="chromatic-theory",
        replacements=(
            Replacement(
                "chromatic-theory/theories/conjectures/U4.v",
                "choice_number_of_k_chromatic_graphs_of_bounded_order_statement",
                "Definition choice_number_of_k_chromatic_graphs_of_bounded_order_statement : Prop :=\n  False.",
            ),
        ),
        appendices=(
            Appendix(
                "chromatic-theory/theories/conjectures/grounding_U4.v",
                """

(** MUTATION TEST CANARY: this lemma is written only in a temporary copy.
    If committed, it would refute a non-disproved row unconditionally and must
    be rejected by the exact-type faithfulness gate. *)
Lemma mutation_refutes_choice_number_of_k_chromatic_graphs_of_bounded_order_statement :
  ~ choice_number_of_k_chromatic_graphs_of_bounded_order_statement.
Proof. by []. Qed.
""",
            ),
        ),
        expected_signature="unconditional-refutation",
        note="mutates an open row to False and commits an unconditional refutation",
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
        expected_signature="[FAIL] package compiles",
        note="reintroduces the historical total-colouring bug for list_colourable_on",
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
        expected_signature="[FAIL] package compiles",
        note="drops the load-bearing 2 < size c guard from girth_geq",
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
        expected_signature="[FAIL] package compiles",
        note="weakens the Wagner-planarity guard to True",
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
        expected_signature="[FAIL] package compiles",
        note="weakens exact girth by deleting the required witnessed g-cycle",
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
        expected_signature="[FAIL] package compiles",
        note="flips strongly_colorable from all partitions to one partition",
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
    rels = ["meta", "base", mutant.package]
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


def run_check(workspace: Path, mutant: Mutant, timeout: int) -> subprocess.CompletedProcess[str]:
    env = dict(os.environ)
    switch_bin = Path.home() / ".opam" / "digraph" / "bin"
    if switch_bin.is_dir():
        env["PATH"] = str(switch_bin) + os.pathsep + env.get("PATH", "")
        env.setdefault("OPAM_SWITCH_PREFIX", str(Path.home() / ".opam" / "digraph"))
    return subprocess.run(
        [sys.executable, "meta/check_milestone.py", mutant.phase, mutant.package],
        cwd=workspace,
        env=env,
        text=True,
        capture_output=True,
        timeout=timeout,
    )


def run_mutant(mutant: Mutant, timeout: int, keep: bool) -> tuple[bool, str, Path | None]:
    tmp = Path(tempfile.mkdtemp(prefix=f"faith-mut-{mutant.name}-"))
    kept: Path | None = tmp if keep else None
    try:
        copy_workspace(mutant, tmp)
        apply_mutation(tmp, mutant)
        proc = run_check(tmp, mutant, timeout)
        output = proc.stdout + proc.stderr
        killed = proc.returncode != 0 and mutant.expected_signature in output
        if killed:
            detail = f"killed by {mutant.expected_signature}"
        elif proc.returncode == 0:
            detail = "SURVIVED: check_milestone accepted the mutant"
        else:
            tail = output[-800:].replace("\n", "\\n")
            detail = f"rejected for the wrong reason; expected {mutant.expected_signature}; tail={tail}"
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

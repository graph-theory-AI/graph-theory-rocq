#!/usr/bin/env python3
"""Edge-level acceptance gate for the federation dependency graph (G1).

Two independent checks, selected by flag (both run when neither is given):

  --assumptions   Every PROVED edge of meta/dependency_graph.json (status
                  `verified` or `conditional`, kind implies/equiv/specializes —
                  `refutes` is never machine-checked) really is backed, IN ROCQ,
                  by a constant of EXACTLY the type the edge claims, and that
                  constant is closed under the global context.

                  For each hosting package (taken from `sources[0]`) one probe
                  file <pkg>/theories/conjectures/_assum_edges.v is written with

                      From <NS>.conjectures Require Import <stems...>.
                      Check (<proof> : <expected type>).
                      Print Assumptions <proof>.

                  and compiled by `coqc` with the package's own _CoqProject
                  include flags.  The expected type is

                      implies / specializes   <from> -> <to>
                      equiv                   <from> <-> <to>
                      conditional             <ext1> -> ... -> <from> -> <to>

                  (the externals in the order the edge lists them: a conditional
                  edge is proved WITHOUT an Axiom by carrying its cited classical
                  input as an explicit Prop hypothesis — see
                  cycle-theory/theories/conjectures/implications_X228.v).

                  A package passes iff coqc exits 0, the output has no `Axioms:`
                  block, and "Closed under the global context" occurs exactly
                  once per edge of that package.  The probe is deleted again
                  unless --keep.

  --registry      meta/edge_waves.json (the per-edge wave/review ledger) agrees
                  with the graph: every proved graph edge has an entry in the
                  same state, reviewed by somebody other than its prover; every
                  `refuted-direction`/`blocked` entry carries a reason; no entry
                  contradicts the graph's status (registry `blocked` matches a
                  graph `candidate`, annotated BLOCKED: or not).  A missing
                  registry file is a warning (an error under --strict).

Exit 0 iff every selected check passes.  The proof files and their .vo already
exist, so --assumptions is a handful of coqc runs against the built objects; no
package is rebuilt.
"""

from __future__ import annotations

import argparse
import glob
import json
import os
import re
import subprocess
import sys
import time

META = os.path.dirname(os.path.abspath(__file__))
MONO = os.path.dirname(META)
sys.path.insert(0, META)
import gate_contracts as CONTRACTS      # noqa: E402
import rocq_toolchain as ROCQ           # noqa: E402

GRAPH_PATH = os.path.join(META, "dependency_graph.json")
REGISTRY_PATH = os.path.join(META, "edge_waves.json")

PROBE_STEM = "_assum_edges"
#: Kinds whose claim is a Rocq type we can `Check`.  A `refutes` edge is a
#: metatheoretic claim about the pair, not an inhabitant of a type, so it is out
#: of scope here (and the graph currently holds none).
PROVED_KINDS = ("implies", "equiv", "specializes")
PROVED_STATUSES = ("verified", "conditional")
CLOSED = "Closed under the global context"

REGISTRY_STATES = ("verified", "conditional", "candidate", "refuted-direction", "blocked")
#: A registry state that is deliberately NOT spelled the same way in the graph.
STATE_ALIASES = {"blocked": ("candidate",)}


# ── the graph ───────────────────────────────────────────────────────────────────────────

def load_json(path, default=None):
    if not os.path.exists(path):
        return default
    with open(path) as handle:
        return json.load(handle)


def edge_key(edge) -> str:
    """The registry key of an edge: `<from>-><to>:<kind>`."""
    return f"{edge.get('from')}->{edge.get('to')}:{edge.get('kind')}"


def externals(edge) -> list[str]:
    """Explicit external hypotheses of a conditional edge (defensive: the field
    is being introduced by the graph builder, so its absence means none)."""
    return list(edge.get("external", []) or [])


def proved_edges(graph) -> list[dict]:
    return [e for e in graph.get("edges", [])
            if e.get("status") in PROVED_STATUSES and e.get("kind") in PROVED_KINDS]


def host_package(edge) -> str:
    """Package hosting the edge's proof: the first component of `sources[0]`."""
    sources = edge.get("sources") or []
    return sources[0].split("/")[0] if sources else ""


def source_stem(source: str) -> str:
    base = os.path.basename(source)
    return base[:-2] if base.endswith(".v") else base


def endpoint_names(edge) -> list[str]:
    return [edge.get("from"), edge.get("to")] + externals(edge)


def expected_type(edge, qualify=None) -> str:
    """The Rocq type the edge claims for its `proof` constant."""
    q = qualify or (lambda name: name)
    core = (f"{q(edge['from'])} <-> {q(edge['to'])}" if edge.get("kind") == "equiv"
            else f"{q(edge['from'])} -> {q(edge['to'])}")
    ext = externals(edge)
    if not ext:
        return core
    if edge.get("kind") == "equiv":
        core = f"({core})"
    return " -> ".join([q(name) for name in ext] + [core])


# ── package layout ──────────────────────────────────────────────────────────────────────

def conjectures_dir(root, package) -> str:
    return os.path.join(root, package, "theories", "conjectures")


def read_cqp(root, package) -> str:
    path = os.path.join(root, package, "_CoqProject")
    return open(path).read() if os.path.exists(path) else ""


def definition_index(root, package) -> tuple[dict[str, str], dict[str, list[str]]]:
    """Map `Definition <name>` -> defining module stem over the package's
    conjecture files, plus the names defined in more than one of them."""
    index: dict[str, str] = {}
    seen: dict[str, list[str]] = {}
    for path in sorted(glob.glob(os.path.join(conjectures_dir(root, package), "*.v"))):
        stem = os.path.basename(path)[:-2]
        if stem.startswith("_"):            # our own (or a sibling gate's) probe file
            continue
        try:
            source = CONTRACTS.strip_comments(open(path).read())
        except OSError:
            continue
        for name in re.findall(r"^\s*Definition\s+([A-Za-z0-9_']+)", source, re.M):
            index.setdefault(name, stem)
            seen.setdefault(name, []).append(stem)
    return index, {n: mods for n, mods in seen.items() if len(mods) > 1}


def foreign_definition_index(root, package) -> dict[str, tuple[str, str]]:
    """Map `Definition <name>` -> (namespace, module stem) over the conjecture
    files of every OTHER package with a `-R theories <NS>` line: the atlas
    package hosts edges whose endpoints live in area packages."""
    index: dict[str, tuple[str, str]] = {}
    for cqp in sorted(glob.glob(os.path.join(root, "*", "_CoqProject"))):
        pkg = os.path.basename(os.path.dirname(cqp))
        if pkg == package:
            continue
        ns = CONTRACTS.namespace_from_cqp(open(cqp).read())
        if not ns or not os.path.isdir(conjectures_dir(root, pkg)):
            continue
        local, _ = definition_index(root, pkg)
        for name, stem in local.items():
            index.setdefault(name, (ns, stem))
    return index


def foreign_imports(edges, foreign) -> list[str]:
    """`From <NS>.conjectures Require Import <stems>.` lines for the endpoints
    that live outside the hosting package."""
    by_ns: dict[str, set[str]] = {}
    for e in edges:
        for n in endpoint_names(e):
            if n in foreign:
                ns, stem = foreign[n]
                by_ns.setdefault(ns, set()).add(stem)
    return [f"From {ns}.conjectures Require Import {' '.join(sorted(stems))}."
            for ns, stems in sorted(by_ns.items())]


def probe_text(namespace, edges, defmod=None, qualified=True, foreign=None) -> str:
    """The generated probe file for one package's edges.

    `defmod` maps an endpoint/external name to the module stem that defines it;
    those modules are imported too (endpoints often live in an earlier wave's
    file), and, when `qualified`, every name is written out in full so the check
    cannot silently land on a homonym re-exported from elsewhere.
    """
    defmod = defmod or {}
    foreign = foreign or {}

    def q(name):
        if qualified and name in defmod:
            return f"{namespace}.conjectures.{defmod[name]}.{name}"
        if qualified and name in foreign:
            ns, stem = foreign[name]
            return f"{ns}.conjectures.{stem}.{name}"
        return name

    stems = {source_stem((e.get("sources") or ["?.v"])[0]) for e in edges}
    stems |= {defmod[n] for e in edges for n in endpoint_names(e) if n in defmod}
    lines = ["(* GENERATED by meta/check_edges.py --assumptions — dependency-graph edge audit.",
             "   Transient: the gate deletes it again (keep it with --keep). *)"]
    lines += foreign_imports(edges, foreign)
    lines.append(f"From {namespace}.conjectures Require Import {' '.join(sorted(stems))}.")
    for edge in edges:
        proof = edge.get("proof") or ""
        stem = source_stem((edge.get("sources") or ["?.v"])[0])
        qproof = f"{namespace}.conjectures.{stem}.{proof}" if qualified else proof
        lines.append(f"(* {edge_key(edge)}  [{edge.get('status')}]  {edge.get('cite', '')[:60]} *)")
        lines.append(f"Check ({qproof} : {expected_type(edge, q)}).")
        lines.append(f"Print Assumptions {qproof}.")
    return "\n".join(lines) + "\n"


def diagnostic_text(namespace, edges, defmod=None, qualified=True, foreign=None) -> str:
    """Probe that only prints the ACTUAL type of each proof constant — written
    when the real probe fails, so the report says what the theorem proves
    instead of only that it does not prove what was claimed."""
    defmod = defmod or {}
    foreign = foreign or {}
    stems = {source_stem((e.get("sources") or ["?.v"])[0]) for e in edges}
    stems |= {defmod[n] for e in edges for n in endpoint_names(e) if n in defmod}
    lines = foreign_imports(edges, foreign)
    lines.append(f"From {namespace}.conjectures Require Import {' '.join(sorted(stems))}.")
    for edge in edges:
        proof = edge.get("proof") or ""
        stem = source_stem((edge.get("sources") or ["?.v"])[0])
        lines.append(f"Check {namespace}.conjectures.{stem}.{proof}." if qualified
                     else f"Check {proof}.")
    return "\n".join(lines) + "\n"


NOISE_RE = re.compile(r"^\s*(?:Warning:|\[[a-z-]+,[a-z,-]+\]$|File \"[^\"]*\", line \d+)")


def interesting_lines(output) -> list[str]:
    """Drop the `notation-overridden` warning storm that any mathcomp Require
    emits, so a failure report shows the Rocq error and nothing else."""
    kept, skipping = [], False
    for line in output.splitlines():
        if NOISE_RE.match(line):
            skipping = "Warning:" in line or line.lstrip().startswith("File \"")
            continue
        if skipping:
            if line.startswith(" ") or line.startswith("["):
                continue
            skipping = False
        if line.strip():
            kept.append(line)
    return kept


def parse_probe_output(output, returncode, n_edges) -> tuple[list[str], int]:
    """Verdict on one package's probe run: (problems, number of closed proofs)."""
    closed = output.count(CLOSED)
    problems: list[str] = []
    if returncode != 0:
        problems.append(f"coqc exited {returncode} (a claimed edge type does not typecheck)")
    if "Axioms:" in output:
        problems.append("`Axioms:` block in Print Assumptions (proof not closed under the "
                        "global context)")
    if closed != n_edges and (returncode == 0 or closed):
        # After a failed Check, coqc never reaches the Print Assumptions, so a bare
        # "0 of 1" would only restate the type error.
        problems.append(f"{closed} of {n_edges} `{CLOSED}`")
    return problems, closed


# ── --assumptions ───────────────────────────────────────────────────────────────────────

def cleanup_probe(directory, stem) -> None:
    for path in glob.glob(os.path.join(directory, f"{stem}*")) + \
            glob.glob(os.path.join(directory, f".{stem}*")):
        try:
            os.remove(path)
        except OSError:
            pass


def check_assumptions(graph, root=MONO, packages=None, keep=False, qualified=True,
                      out=None) -> int:
    out = out or sys.stdout          # resolved at call time, so a redirect_stdout is honoured
    edges = proved_edges(graph)
    by_package: dict[str, list[dict]] = {}
    orphans: list[str] = []
    for edge in edges:
        package = host_package(edge)
        if not package:
            orphans.append(f"{edge_key(edge)}: no sources[] — cannot locate the hosting package")
            continue
        by_package.setdefault(package, []).append(edge)
    if packages:
        by_package = {p: e for p, e in by_package.items() if p in set(packages)}

    print(f"=== check_edges --assumptions ({len(edges)} proved edges, "
          f"{len(by_package)} package(s)) ===", file=out)
    env = ROCQ.environment()
    failures = list(orphans)
    total_closed = 0
    for package in sorted(by_package):
        pkg_edges = sorted(by_package[package], key=edge_key)
        started = time.time()
        directory = conjectures_dir(root, package)
        cqp_txt = read_cqp(root, package)
        namespace = CONTRACTS.namespace_from_cqp(cqp_txt)
        statuses = {}
        for edge in pkg_edges:
            statuses[edge.get("status")] = statuses.get(edge.get("status"), 0) + 1
        label = ", ".join(f"{n} {s}" for s, n in sorted(statuses.items()))
        if not namespace or not os.path.isdir(directory):
            failures.append(f"{package}: no `-R theories <NS>` in _CoqProject or no "
                            f"theories/conjectures/ ({directory})")
            print(f"  [FAIL] {package:24s} unusable package layout", file=out)
            continue
        missing_proof = [edge_key(e) for e in pkg_edges if not e.get("proof")]
        if missing_proof:
            failures += [f"{package}: {k}: proved edge without proof=<theorem>"
                         for k in missing_proof]
            print(f"  [FAIL] {package:24s} {len(missing_proof)} edge(s) name no proof", file=out)
            continue
        defmod, duplicates = definition_index(root, package)
        foreign = {}
        if any(n not in defmod for e in pkg_edges for n in endpoint_names(e)):
            foreign = {n: v for n, v in foreign_definition_index(root, package).items()
                       if n not in defmod}
        unknown = sorted({n for e in pkg_edges for n in endpoint_names(e)
                          if n not in defmod and n not in foreign})
        clash = sorted({n for e in pkg_edges for n in endpoint_names(e) if n in duplicates})

        incl_flags = CONTRACTS.incl_flags_from_cqp(cqp_txt) or ["-R", "theories", namespace]
        probe = os.path.join(directory, f"{PROBE_STEM}.v")
        open(probe, "w").write(probe_text(namespace, pkg_edges, defmod, qualified, foreign))
        run = subprocess.run(["coqc"] + incl_flags + [f"theories/conjectures/{PROBE_STEM}.v"],
                             cwd=os.path.join(root, package), env=env,
                             capture_output=True, text=True)
        output = run.stdout + run.stderr
        problems, closed = parse_probe_output(output, run.returncode, len(pkg_edges))
        elapsed = time.time() - started
        if problems:
            # coqc stops at the first bad Check, so the batch probe alone cannot say WHICH
            # edges are wrong: re-run one edge per probe (only on failure), and print what
            # the constants actually prove so the fix is obvious from the report.
            print(f"  [FAIL] {package:24s} {len(pkg_edges)} edge(s) ({label}) "
                  f"{elapsed:5.1f}s", file=out)
            for problem in problems:
                print(f"         - {problem}", file=out)
            if unknown:
                print(f"         - endpoint(s) with no `Definition` in {package}: "
                      f"{', '.join(unknown)}", file=out)
            one = f"{PROBE_STEM}_one"
            pkg_failures: list[str] = []
            closed = 0
            for edge in pkg_edges:
                open(os.path.join(directory, f"{one}.v"), "w").write(
                    probe_text(namespace, [edge], defmod, qualified, foreign))
                er = subprocess.run(["coqc"] + incl_flags + [f"theories/conjectures/{one}.v"],
                                    cwd=os.path.join(root, package), env=env,
                                    capture_output=True, text=True)
                eout = er.stdout + er.stderr
                eprobs, _ = parse_probe_output(eout, er.returncode, 1)
                cleanup_probe(directory, one)
                if eprobs:
                    print(f"         [bad ] {edge_key(edge)}  <-  {edge['proof']}: "
                          f"{'; '.join(eprobs)}", file=out)
                    pkg_failures.append(f"{package}: {edge_key(edge)}: {'; '.join(eprobs)}")
                    for line in interesting_lines(eout)[:10]:
                        print(f"                | {line}", file=out)
                else:
                    closed += 1
                    print(f"         [ok  ] {edge_key(edge)}  <-  {edge['proof']}", file=out)
            diag = os.path.join(directory, f"{PROBE_STEM}_diag.v")
            open(diag, "w").write(diagnostic_text(namespace, pkg_edges, defmod, qualified, foreign))
            dr = subprocess.run(["coqc"] + incl_flags +
                                [f"theories/conjectures/{PROBE_STEM}_diag.v"],
                                cwd=os.path.join(root, package), env=env,
                                capture_output=True, text=True)
            actual = (dr.stdout + dr.stderr).strip()
            if not keep:
                cleanup_probe(directory, f"{PROBE_STEM}_diag")
            if actual:
                print("         actual types of the proof constants:", file=out)
                for line in interesting_lines(actual)[:60]:
                    print(f"           | {line}", file=out)
            # A batch that fails while every edge passes alone is itself a defect (a name
            # clash between two modules, say), so it must not be swallowed.
            failures += pkg_failures or [f"{package}: {p}" for p in problems]
            total_closed += closed
        else:
            total_closed += closed
            print(f"  [PASS] {package:24s} {len(pkg_edges)} edge(s) ({label}), "
                  f"{closed} closed under the global context {elapsed:5.1f}s", file=out)
            for edge in pkg_edges:
                print(f"         {edge_key(edge)}  <-  {edge['proof']}", file=out)
            if clash:
                print(f"         note: homonym definitions in this package for "
                      f"{', '.join(clash)} (the probe qualifies every name)", file=out)
        if not keep:
            cleanup_probe(directory, PROBE_STEM)
        else:
            print(f"         probe kept: {probe}", file=out)

    selected = sum(len(e) for e in by_package.values())
    print(f"\n{'ACCEPTED' if not failures else 'REJECTED'}: {total_closed}/{selected} "
          f"proved edges backed by a constant of exactly the claimed type and closed under the "
          f"global context.", file=out)
    for failure in failures:
        print(f"  FAIL {failure}", file=out)
    return 0 if not failures else 1


# ── --registry ──────────────────────────────────────────────────────────────────────────

MAX_NOTES = 6


def check_registry(graph, registry, strict=False, out=None) -> int:
    """Cross-check meta/edge_waves.json against the dependency graph."""
    out = out or sys.stdout          # resolved at call time, so a redirect_stdout is honoured
    if registry is None:
        print("=== check_edges --registry ===", file=out)
        message = (f"{os.path.relpath(REGISTRY_PATH, MONO)} does not exist yet — the per-edge "
                   f"wave/review ledger is not being checked")
        if strict:
            print(f"  REJECTED: {message} (--strict)", file=out)
            return 1
        print(f"  WARNING: {message}", file=out)
        return 0

    entries = registry.get("edges", {}) or {}
    graph_edges = {edge_key(e): e for e in graph.get("edges", [])}
    proved = {edge_key(e): e for e in proved_edges(graph)}
    violations: list[str] = []
    notes: list[str] = []

    for key in sorted(proved):
        edge = proved[key]
        entry = entries.get(key)
        if entry is None:
            violations.append(f"{key}: {edge.get('status')} in the graph, absent from the registry")
            continue
        state = entry.get("state")   # the state/status comparison is done once, below
        prover = (entry.get("proved_by") or "").strip()
        reviewer = (entry.get("reviewed_by") or "").strip()
        if not reviewer:
            violations.append(f"{key}: {state} without reviewed_by (a proved edge needs a "
                              f"second reader)")
        elif reviewer == prover:
            violations.append(f"{key}: reviewed_by == proved_by ({reviewer!r}) — the reviewer "
                              f"must differ from the prover")

    by_state: dict[str, int] = {}
    for key in sorted(entries):
        entry = entries[key]
        state = entry.get("state")
        by_state[state] = by_state.get(state, 0) + 1
        if state not in REGISTRY_STATES:
            violations.append(f"{key}: out-of-vocabulary state {state!r} "
                              f"(expected one of {', '.join(REGISTRY_STATES)})")
        if state in ("refuted-direction", "blocked") and not (entry.get("reason") or "").strip():
            violations.append(f"{key}: state {state} without a reason")
        graph_edge = graph_edges.get(key)
        if graph_edge is None:
            notes.append(f"{key}: registry entry with no edge in the dependency graph "
                         f"(state {state}; planned, or the annotation is gone)")
            continue
        status = graph_edge.get("status")
        if state != status and status not in STATE_ALIASES.get(state, ()):
            violations.append(f"{key}: ledger/annotation drift — registry state {state!r} != "
                              f"graph status {status!r} (the @EDGE annotation is the graph's "
                              f"source of truth)")

    print("=== check_edges --registry ===", file=out)
    print(f"  {len(entries)} registry entries: "
          f"{', '.join(f'{n} {s}' for s, n in sorted(by_state.items())) or 'none'}", file=out)
    print(f"  {len(proved)} proved graph edges (verified/conditional), "
          f"{len(graph_edges)} edges in the graph", file=out)
    reviewed = sum(1 for k in proved
                   if (entries.get(k, {}).get("reviewed_by") or "").strip())
    print(f"  {reviewed}/{len(proved)} proved edges carry a reviewer", file=out)
    for note in notes[:MAX_NOTES]:
        print(f"  note: {note}", file=out)
    if len(notes) > MAX_NOTES:
        print(f"  note: ... and {len(notes) - MAX_NOTES} further registry entries with no edge "
              f"in the dependency graph (planned edges, or vanished annotations)", file=out)
    for violation in violations:
        print(f"  FAIL {violation}", file=out)
    print(f"  {'ACCEPTED' if not violations else 'REJECTED'}: {len(violations)} violation(s)",
          file=out)
    return 0 if not violations else 1


# ── CLI ─────────────────────────────────────────────────────────────────────────────────

def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        description="Edge-level gate for meta/dependency_graph.json: proved edges really are "
                    "proved (in Rocq, axiom-free, at exactly the claimed type), and the "
                    "edge-wave registry agrees with the graph.")
    parser.add_argument("--assumptions", action="store_true",
                        help="compile a Check/Print Assumptions probe per hosting package")
    parser.add_argument("--registry", action="store_true",
                        help="cross-check meta/edge_waves.json against the graph")
    parser.add_argument("--strict", action="store_true",
                        help="a missing edge_waves.json is an error, not a warning")
    parser.add_argument("--keep", action="store_true",
                        help="keep the generated _assum_edges.v probe files")
    parser.add_argument("--package", action="append", default=None, metavar="PKG",
                        help="restrict --assumptions to this package (repeatable)")
    parser.add_argument("--graph", default=GRAPH_PATH, help="path to dependency_graph.json")
    parser.add_argument("--registry-file", default=REGISTRY_PATH, help="path to edge_waves.json")
    parser.add_argument("--root", default=MONO, help="monorepo root holding the packages")
    parser.add_argument("--no-qualify", action="store_true",
                        help="write bare names in the probe instead of <NS>.conjectures.<mod>.<n>")
    args = parser.parse_args(argv)

    graph = load_json(args.graph)
    if graph is None:
        print(f"check_edges: no dependency graph at {args.graph}", file=sys.stderr)
        return 1
    run_assumptions = args.assumptions or not (args.assumptions or args.registry)
    run_registry = args.registry or not (args.assumptions or args.registry)

    code = 0
    if run_assumptions:
        code |= check_assumptions(graph, root=args.root, packages=args.package, keep=args.keep,
                                  qualified=not args.no_qualify)
    if run_registry:
        if run_assumptions:
            print("", file=sys.stdout)
        code |= check_registry(graph, load_json(args.registry_file), strict=args.strict)
    return 1 if code else 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Active vacuity / refutability probe for conjecture `_statement` definitions.

The acceptance gate (`check_milestone.py` step 7) *rejects* committed trivial proofs or
refutations; `faithfulness_mutation.py` mutation-tests the checks.  Neither *actively searches*
for a trivial proof of each statement.  This probe closes that gap: for every `_statement` it
tries to close both `<stmt>` and `~ <stmt>` and flags any statement a bounded automation budget
(or a curated witness) can settle — a formalized open conjecture should be settleable by neither.

Two complementary layers:

  1. AUTO tripwire (fully generic, zero per-statement input): a ssreflect/`eauto`/`firstorder`
     tactic ladder.  High precision, but low recall on statements whose refutation needs a bespoke
     finite counterexample (e.g. a pigeonhole on K_4) — those are exactly what layer 2 is for.

  2. WITNESS hints (`meta/probe_hints/<statement_name>.v`): an explicit `~<stmt>` (or `<stmt>`)
     proof.  If it compiles, the statement is settleable ⇒ FLAG.  These capture the bespoke
     counterexamples the auto layer cannot find, and double as fix-verification: once a statement
     is corrected, its witness must STOP compiling (the probe reports `hint-stale-FIX-OK`).

Usage:
  python3 meta/vacuity_probe.py --names foo_statement,bar_statement   # probe specific statements
  python3 meta/vacuity_probe.py --files pkg/theories/conjectures/X.v  # every _statement in a file
  python3 meta/vacuity_probe.py --wave X35                            # every _statement of a wave (via waves json)
  python3 meta/vacuity_probe.py --all                                 # whole v2 conjecture corpus (slow)
  python3 meta/vacuity_probe.py --validate                            # self-test: regression + recall + control
Runs with the coqc on PATH, or through `opam exec --switch $ROCQ_OPAM_SWITCH` when set (Rocq 9.1.1).  Read-only w.r.t. the repo (scratch in a tmpdir).
Exit code 0 iff nothing was FLAGGED (suitable for `make probe`).
"""
from __future__ import annotations
import argparse, json, os, re, subprocess, sys, tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
META = ROOT / "meta"
HINTS = META / "probe_hints"
SWITCH = os.environ.get("ROCQ_OPAM_SWITCH", "")   # empty: use the coqc on PATH (default switch)


def coqc_cmd():
    """The coqc invocation: through `opam exec --switch $ROCQ_OPAM_SWITCH` when that variable is
    set, else the ambient coqc. A missing toolchain must abort the probe rather than report every
    statement as `ok` (a silent false green, observed on a machine without the `digraph` switch)."""
    return (["opam", "exec", "--switch", SWITCH, "--", "coqc"] if SWITCH else ["coqc"])
DEFAULT_TIMEOUT = 45

sys.path.insert(0, str(META))
import corpus_registry as REG  # noqa: E402  (package -> namespace map)

STMT_RE = re.compile(r"^Definition\s+([A-Za-z0-9_']+_statement)\b", re.M)

# The generic automation ladder.  `by []`/`done` come from ssreflect (re-exported by base).
LADDER = r"""
Ltac __probe :=
  solve
    [ done | by [] | trivial | now firstorder | typeclasses eauto
    | now eauto 6
    | (do 12 (try eexists)); now eauto 6
    | (hnf; intros; solve [ done | by [] | now firstorder | now eauto 6 ]) ].
""".strip()


def sh(args, timeout):
    try:
        p = subprocess.run(args, cwd=ROOT, capture_output=True, text=True, timeout=timeout)
        return p.returncode, (p.stdout + p.stderr)
    except subprocess.TimeoutExpired:
        return 124, "<timeout>"


def area_flags(area: str) -> list[str]:
    """Load-path flags for an area, parsed from its _CoqProject (paths made absolute)."""
    cp = ROOT / area / "_CoqProject"
    flags: list[str] = []
    for line in cp.read_text().splitlines():
        line = line.strip()
        if line.startswith(("-R ", "-Q ")):
            parts = line.split()
            tag, d, logical = parts[0], parts[1], parts[2]
            absd = (ROOT / area / d).resolve()
            # -R and -Q both work for Require Import; use -Q uniformly.
            flags += ["-Q", str(absd), logical]
    flags += ["-w", "-notation-overridden"]
    return flags


def build_index() -> dict[str, tuple[str, str, str]]:
    """statement_name -> (area, module_stem, namespace)."""
    idx: dict[str, tuple[str, str, str]] = {}
    for vf in ROOT.glob("*/theories/conjectures/*.v"):
        area = vf.relative_to(ROOT).parts[0]
        ns = REG.NS.get(area)
        if ns is None:
            continue
        try:
            text = vf.read_text()
        except Exception:
            continue
        for name in STMT_RE.findall(text):
            idx[name] = (area, vf.stem, ns)
    return idx


def compile_snippet(area: str, ns: str, stem: str, body: str, timeout: int) -> tuple[bool, str]:
    """Write a scratch .v that imports the module and appends `body`; return (compiled_ok, log)."""
    header = f"From {ns}.conjectures Require Import {stem}.\n"
    with tempfile.TemporaryDirectory() as td:
        f = Path(td) / "probe.v"
        f.write_text(header + body + "\n")
        rc, log = sh([*coqc_cmd(), "-q", *area_flags(area), str(f)], timeout)
        if rc != 0 and ("No such file" in log or "not installed" in log or "command not found" in log):
            sys.exit(f"vacuity_probe: coqc toolchain unavailable ({log.strip()[:200]})")
        return rc == 0, log


def compile_hint(area: str, hint: Path, timeout: int) -> bool:
    """Compile a witness hint's TEXT in a throwaway tmpdir so NO .vo/.glob/.vos/.vok/.aux
    artifacts land next to the hint (the probe stays read-only w.r.t. the repo; hints only
    use logical `From ... Require` imports resolved via `area_flags`, so location is irrelevant).
    rc==0 ⇒ the refutation still compiles ⇒ the statement is settleable."""
    with tempfile.TemporaryDirectory() as td:
        f = Path(td) / hint.name
        f.write_text(hint.read_text())
        rc, _ = sh([*coqc_cmd(), "-q", *area_flags(area), str(f)], max(timeout, 90))
        return rc == 0


def probe_statement(name: str, idx, timeout: int) -> dict:
    if name not in idx:
        return {"name": name, "status": "NOT-FOUND", "flag": False}
    area, stem, ns = idx[name]
    # Layer 1: auto tripwire, both polarities.
    ok_true, _ = compile_snippet(area, ns, stem, f"{LADDER}\nLemma __pt : {name}. Proof. __probe. Qed.", timeout)
    ok_false, _ = compile_snippet(area, ns, stem, f"{LADDER}\nLemma __pf : ~ ({name}). Proof. __probe. Qed.", timeout)
    # Layer 2: curated witness hint, if present.
    hint = HINTS / f"{name}.v"
    hint_state = "none"
    if hint.exists():
        hint_state = "settles" if compile_hint(area, hint, timeout) else "stale-FIX-OK"
    flag = ok_true or ok_false or hint_state == "settles"
    return {
        "name": name, "area": area, "flag": flag,
        "auto_true": ok_true, "auto_false": ok_false, "hint": hint_state,
        "status": "FLAGGED" if flag else "ok",
    }


def names_from_wave(wave: str) -> list[str]:
    data = json.loads((META / "v2_statement_waves.json").read_text())
    w = data.get("waves", {}).get(wave, {})
    return [r.get("formal_name") for r in w.get("rows", {}).values() if r.get("formal_name")]


def names_from_files(files: list[str]) -> list[str]:
    out: list[str] = []
    for fp in files:
        out += STMT_RE.findall(Path(fp if os.path.isabs(fp) else ROOT / fp).read_text())
    return out


def report(rows: list[dict]) -> int:
    flagged = [r for r in rows if r.get("flag")]
    print(f"\n{'statement':52s} {'auto=T':6s} {'auto=F':6s} {'hint':14s} verdict")
    print("-" * 92)
    for r in sorted(rows, key=lambda r: (not r.get("flag"), r["name"])):
        if r.get("status") == "NOT-FOUND":
            print(f"{r['name']:52s} {'-':6s} {'-':6s} {'-':14s} NOT-FOUND")
            continue
        print(f"{r['name']:52s} {str(r['auto_true']):6s} {str(r['auto_false']):6s} "
              f"{r['hint']:14s} {'*** FLAGGED ***' if r['flag'] else 'ok'}")
    print("-" * 92)
    print(f"{len(rows)} probed · {len(flagged)} FLAGGED")
    return 1 if flagged else 0


# --- self-test: two independent guards + a false-positive control ---
# HISTORICAL_FIXES: five statements that were once refutable and have since been FIXED
# (X35/X55/X83/X89/X100).  Their curated witness refutations no longer compile, so the probe
# reports `stale-FIX-OK` (NOT `settles`) and does NOT flag them — that is the fix in action.
# They anchor the REGRESSION guard: revert any fix and its hint flips back to `settles`, the
# statement is FLAGGED again, and the guard fails.  (Because a healthy tree flags NONE of them,
# they cannot on their own prove the flagging path still works — hence the separate RECALL guard.)
HISTORICAL_FIXES = ["sparse_graph_low_chromatic_cut_statement", "chen_chvatal_metric_lines_statement",
                    "aravind_rainbow_induced_chromatic_path_statement",
                    "bandelt_dress_maximum_quartet_distance_statement",
                    "modular_edge_colouring_k_plus_constant_statement"]
CONTROL_GOOD = ["small_quasi_kernel_statement", "ryser_intersecting_partite_cover_gap_statement",
                "brualdi_stein_partial_transversal_statement",
                "induced_saturation_even_cycle_existence_statement",
                "planar_linear_arboricity_statement", "even_hole_k4_diamond_free_bounded_treewidth_statement"]


def recall_flags(idx, timeout: int) -> bool:
    """RECALL guard: prove the FLAG path actually fires.  Inject a genuinely vacuous statement
    (`... : Prop := True`) into the AUTO tripwire inside a real module's import context and
    confirm the ladder settles it.  A dead/broken tripwire would return False here and fail
    the self-test, instead of silently passing every real statement."""
    ctx = next((idx[n] for n in HISTORICAL_FIXES if n in idx), None) or next(iter(idx.values()), None)
    if ctx is None:
        return False
    area, stem, ns = ctx
    body = (f"{LADDER}\n"
            f"Definition __probe_selftest_vacuous_statement : Prop := True.\n"
            f"Lemma __pt : __probe_selftest_vacuous_statement. Proof. __probe. Qed.")
    ok, _ = compile_snippet(area, ns, stem, body, timeout)
    return ok


def validate(idx, timeout: int) -> int:
    """Self-test.  Exits 0 in a healthy tree; exits 1 if EITHER a historical fix is reverted
    (regression) OR the recall fixture stops flagging OR a control produces a false positive.

      (a) REGRESSION — every historical fix must still hold: its witness must report
          `stale-FIX-OK` and NOT be flagged.  Reverting a fix flips the hint to `settles`.
      (b) RECALL — a genuinely settleable (trivially-true) fixture MUST be flagged, proving
          the flagging path works even though (a) flags nothing in a healthy tree.
      (c) CONTROL — known-good statements must stay ok (no false positives).
    """
    print("== REGRESSION: historical fixes — hints must be stale-FIX-OK (NOT flagged) ==")
    b = [probe_statement(n, idx, timeout) for n in HISTORICAL_FIXES]
    report(b)
    reverted = [r for r in b if r.get("flag") or r.get("hint") != "stale-FIX-OK"]
    for r in reverted:
        print(f"!! REGRESSION: {r['name']} expected hint=stale-FIX-OK, got "
              f"hint={r.get('hint')} flag={r.get('flag')} — was a fix reverted?")

    print("\n== RECALL: synthetic vacuous fixture — MUST FLAG ==")
    recall_ok = recall_flags(idx, timeout)
    print(f"synthetic trivially-true statement flagged by AUTO tripwire: {recall_ok}   (want True)")
    if not recall_ok:
        print("!! RECALL: the flagging path did not fire on a trivially-true statement")

    print("\n== CONTROL: known-good — should stay ok ==")
    g = [probe_statement(n, idx, timeout) for n in CONTROL_GOOD]
    report(g)
    fp = sum(r["flag"] for r in g)

    print("\n== summary ==")
    print(f"regression (historical fixes stale-FIX-OK): {'PASS' if not reverted else 'FAIL'}")
    print(f"recall (synthetic vacuous flagged):         {'PASS' if recall_ok else 'FAIL'}")
    print(f"control false-positives:                    {fp}/{len(g)}   (want 0)")
    return 0 if (not reverted and recall_ok and fp == 0) else 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--names"); ap.add_argument("--files", nargs="*")
    ap.add_argument("--wave"); ap.add_argument("--all", action="store_true")
    ap.add_argument("--validate", action="store_true")
    ap.add_argument("--timeout", type=int, default=DEFAULT_TIMEOUT)
    a = ap.parse_args()
    idx = build_index()
    if a.validate:
        sys.exit(validate(idx, a.timeout))
    if a.names:
        names = a.names.split(",")
    elif a.files:
        names = names_from_files(a.files)
    elif a.wave:
        names = names_from_wave(a.wave)
    elif a.all:
        names = sorted(idx)
    else:
        ap.error("one of --names/--files/--wave/--all/--validate required")
    sys.exit(report([probe_statement(n.strip(), idx, a.timeout) for n in names]))


if __name__ == "__main__":
    main()

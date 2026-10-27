#!/usr/bin/env python3
"""Active vacuity / refutability probe for conjecture `_statement` definitions.

The acceptance gate (`check_milestone.py` step 7) *rejects* committed trivial proofs or
refutations; `faithfulness_mutation.py` mutation-tests the checks.  Neither *actively searches*
for a trivial proof of each statement.  This probe closes that gap: for every `_statement` it
tries to close both `<stmt>` and `~ <stmt>` and flags any statement a bounded automation budget
(or a curated witness) can settle — a formalized open conjecture should be settleable by neither.

Three complementary layers:

  1. AUTO tripwire (fully generic, zero per-statement input): a ssreflect/`eauto`/`firstorder`
     tactic ladder.  High precision, but low recall on statements whose refutation needs a bespoke
     finite counterexample (e.g. a pigeonhole on K_4) — those are exactly what layer 2 is for.

  2. WITNESS hints (`meta/probe_hints/<statement_name>.v`): an explicit `~<stmt>` (or `<stmt>`)
     proof.  If it compiles, the statement is settleable ⇒ FLAG.  These capture the bespoke
     counterexamples the auto layer cannot find, and double as fix-verification: once a statement
     is corrected, its witness must STOP compiling (the probe reports `hint-stale-FIX-OK`).

  3. INSTANTIATION / small-model probes: specialize leading nat and sgraph quantifiers at
     0, 1, the empty graph, and complete labelled graphs K_1..K_6, then rerun the tactic ladder
     with `vm_compute`. This mechanizes the degenerate-parameter and K_6-style checks without
     pretending to be a complete finite-model finder.

Usage:
  python3 meta/vacuity_probe.py --names foo_statement,bar_statement   # probe specific statements
  python3 meta/vacuity_probe.py --files pkg/theories/conjectures/X.v  # every _statement in a file
  python3 meta/vacuity_probe.py --wave X35                            # every _statement of a wave (via waves json)
  python3 meta/vacuity_probe.py --all                                 # whole v2 conjecture corpus (slow)
  python3 meta/vacuity_probe.py --target area/STEM:name[,...]         # any Definition of one named module
  python3 meta/vacuity_probe.py --validate                            # self-test: regression + recall + control
Runs with the coqc on PATH, or through `opam exec --switch $ROCQ_OPAM_SWITCH` when set (Rocq 9.1.1).  Read-only w.r.t. the repo (scratch in a tmpdir).
Exit code 0 iff every requested target was searched and none was FLAGGED (suitable for `make probe`);
every other verdict below prints its row and makes the exit code 1 (one code for all of them).
  NOT-FOUND   a requested name the index does not hold (a misspelled or renamed statement), or a
              --target whose module or definition does not exist.
  AMBIGUOUS   a --names name that two or more conjecture files define: the index never picks one
              of them; name the module with --target.  --files, --wave and --all probe each name
              against the file that defines it.
  PARAMETRIC  the setup does not compile because the target's type is a product (Section variables
              or explicit parameters), not Prop; the row lists the --target form of every corpus
              Definition that applies the name (an instantiated statement) to probe instead.
  INCOMPLETE  the probes could not search: one of its coqc runs ended abnormally (killed, e.g. by the
              OOM killer), the probes' common setup does not compile (the preflight: a parse error,
              an unbuilt or stale module, a renamed statement), the name does not resolve to the
              probed module's definition in both probe contexts (the preflight's two Locate checks),
              its hint's imports do not load, or its small-model file failed outside its Fail commands.
Such runs settle nothing, so the probe fails closed instead of reporting `ok`; the designed timeout
stays a search budget.  Every searched target prints a "RESOLVED <name> -> <constant> | <constant>"
line: the definition the bare name means in the auto layers' and in the small model's context.
"""
from __future__ import annotations
import argparse, concurrent.futures, itertools, json, os, re, subprocess, sys, tempfile
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
    [ done | by [] | trivial | now firstorder | typeclasses eauto | now vm_compute
    | now eauto 6
    | (do 12 (try eexists)); now eauto 6
    | (hnf; intros; solve [ done | by [] | now firstorder | now eauto 6 ]) ].
""".strip()

# Specialization is repeated over several concrete parameters, so its ladder must stay
# sharply bounded. Bespoke pigeonhole/counting arguments belong in probe_hints instead.
SMALL_LADDER = r"""
Ltac __small_probe :=
  solve [ done | by [] | trivial | congruence | now vm_compute ].
""".strip()


def strip_comments(src: str) -> str:
    out: list[str] = []
    i = depth = 0
    while i < len(src):
        if src.startswith("(*", i):
            depth += 1; out.extend("  "); i += 2
        elif depth and src.startswith("*)", i):
            depth -= 1; out.extend("  "); i += 2
        elif depth:
            out.append("\n" if src[i] == "\n" else " "); i += 1
        else:
            out.append(src[i]); i += 1
    return "".join(out)


def sentence_end(src: str, start: int) -> int:
    i = start
    while True:
        j = src.find(".", i)
        if j < 0:
            return len(src)
        if not src[j + 1:j + 2] or src[j + 1:j + 2].isspace():
            return j + 1
        i = j + 1


def statement_bodies(src: str) -> dict[str, str]:
    clean = strip_comments(src)
    out = {}
    for match in STMT_RE.finditer(clean):
        command = clean[match.start():sentence_end(clean, match.start())]
        out[match.group(1)] = command.split(":=", 1)[1] if ":=" in command else ""
    return out


def definition_body(src: str, name: str) -> str | None:
    """The body of `Definition <name>` in a source (any name, not only *_statement), comments
    stripped; None if the source does not define it."""
    clean = strip_comments(src)
    match = re.search(rf"^Definition\s+{re.escape(name)}(?![A-Za-z0-9_'])", clean, re.M)
    if match is None:
        return None
    command = clean[match.start():sentence_end(clean, match.start())]
    return command.split(":=", 1)[1] if ":=" in command else ""


def sh(args, timeout):
    try:
        p = subprocess.run(args, cwd=ROOT, capture_output=True, text=True, timeout=timeout)
        return p.returncode, (p.stdout + p.stderr)
    except subprocess.TimeoutExpired:
        return 124, "<timeout>"


# A coqc run that ends abnormally settles nothing either way: killed by a signal (a negative return
# code; the OOM killer's SIGKILL is -9) or killed under a wrapper shell or `opam exec` (137 = 128 + 9).
# That is an environment failure, not a probe outcome, so the statement is INCOMPLETE, never `ok`
# (fail closed).  The designed timeout (124 above) keeps its meaning: a search budget, not a failure.
KILLED_RCS = {137}


class ProbeIncomplete(Exception):
    """A probe's coqc run ended abnormally; the statement it was probing gets no verdict."""


def killed(rc: int) -> bool:
    return rc < 0 or rc in KILLED_RCS


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


class Index(dict):
    """statement_name -> (area, module_stem, namespace, source body) for the names that exactly one
    conjecture file defines; `dups` maps every name that two or more files define to their
    "area/stem" list.  A duplicated name is NOT in the mapping: no file order picks one definer."""

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.dups: dict[str, list[str]] = {}


def conjecture_files() -> list[Path]:
    return sorted(ROOT.glob("*/theories/conjectures/*.v"))


def build_index() -> Index:
    """statement_name -> (area, module_stem, namespace, unfolded source body); duplicates in .dups."""
    seen: dict[str, list[tuple[str, str, str, str]]] = {}
    for vf in conjecture_files():
        area = vf.relative_to(ROOT).parts[0]
        ns = REG.NS.get(area)
        if ns is None:
            continue
        try:
            text = vf.read_text()
        except Exception:
            continue
        for name, body in statement_bodies(text).items():
            seen.setdefault(name, []).append((area, vf.stem, ns, body))
    idx = Index()
    for name, entries in seen.items():
        if len(entries) == 1:
            idx[name] = entries[0]
        else:
            idx.dups[name] = sorted(f"{area}/{stem}" for area, stem, _ns, _body in entries)
    return idx


def compile_snippet(area: str, ns: str, stem: str, body: str, timeout: int) -> tuple[bool, str]:
    """Write a scratch .v that imports the module and appends `body`; return (compiled_ok, log).
    A coqc run that ended abnormally raises ProbeIncomplete.  The ladders are ssreflect tactics
    (`done`, `by []`, `move=>`), so the header imports MathComp's all_boot first: a statement file
    that only Require Imports its dependencies does not bring ssreflect into the snippet."""
    header = f"From mathcomp Require Import all_boot.\nFrom {ns}.conjectures Require Import {stem}.\n"
    with tempfile.TemporaryDirectory() as td:
        f = Path(td) / "probe.v"
        f.write_text(header + body + "\n")
        rc, log = sh([*coqc_cmd(), "-q", *area_flags(area), str(f)], timeout)
        if rc != 0 and ("No such file" in log or "not installed" in log or "command not found" in log):
            sys.exit(f"vacuity_probe: coqc toolchain unavailable ({log.strip()[:200]})")
        if killed(rc):
            raise ProbeIncomplete(f"coqc ended abnormally (rc {rc})")
        return rc == 0, log


def compile_hint(area: str, hint: Path, timeout: int) -> bool:
    """Compile a witness hint's TEXT in a throwaway tmpdir so NO .vo/.glob/.vos/.vok/.aux
    artifacts land next to the hint (the probe stays read-only w.r.t. the repo; hints only
    use logical `From ... Require` imports resolved via `area_flags`, so location is irrelevant).
    rc==0 ⇒ the refutation still compiles ⇒ the statement is settleable.  An abnormal end raises
    ProbeIncomplete (it must not read as `stale-FIX-OK`), and so do imports that do not load: the
    hint's leading Require / Import / Set block is compiled alone first, so a hint that fails only
    because its libraries are unbuilt or stale is not a verified fix."""
    with tempfile.TemporaryDirectory() as td:
        text = hint.read_text()
        setup = Path(td) / "hint_setup.v"
        setup.write_text(hint_setup(text) + "\n")
        rc, log = sh([*coqc_cmd(), "-q", *area_flags(area), str(setup)], max(timeout, 90))
        if killed(rc):
            raise ProbeIncomplete(f"coqc ended abnormally on the imports of the hint {hint.name} (rc {rc})")
        if rc != 0:
            raise ProbeIncomplete(f"the imports of the hint {hint.name} do not load: {first_error(log)}")
        f = Path(td) / hint.name
        f.write_text(text)
        rc, _ = sh([*coqc_cmd(), "-q", *area_flags(area), str(f)], max(timeout, 90))
        if killed(rc):
            raise ProbeIncomplete(f"coqc ended abnormally on the hint {hint.name} (rc {rc})")
        return rc == 0


HINT_SETUP_RE = re.compile(r"(From|Require|Import|Export|Set|Unset|Local|Global|Open|Close)\b")


def hint_setup(text: str) -> str:
    """The leading sentences of a hint that load and configure (From / Require / Import / Set ...),
    up to its first definition, lemma or section."""
    clean = strip_comments(text)
    i, out = 0, []
    while True:
        while i < len(clean) and clean[i].isspace():
            i += 1
        if i >= len(clean) or not HINT_SETUP_RE.match(clean, i):
            return "\n".join(out)
        j = sentence_end(clean, i)
        out.append(clean[i:j].strip())
        i = j


def first_error(log: str) -> str:
    """The first error message of a coqc log: the line starting with "Error" together with its
    continuation lines (Rocq prints a long message after a bare "Error:" line), up to a blank line or
    the next "File " / "Warning" line, whitespace-normalised; the last line if there is no error."""
    lines = [line.strip() for line in log.splitlines()]
    for i, line in enumerate(lines):
        if line.startswith("Error"):
            parts = [line]
            for nxt in lines[i + 1:]:
                if not nxt or nxt.startswith(("File ", "Warning")):
                    break
                parts.append(nxt)
            return " ".join(" ".join(parts).split())[:300]
    nonempty = [line for line in lines if line]
    return nonempty[-1][:300] if nonempty else ""


class ProbeParametric(Exception):
    """The target's type is a product (Section variables or explicit parameters), not Prop."""


RESOLUTION_MARK = "__vacuity_probe_resolution_mark"


def resolved_constants(log: str) -> tuple[str, str]:
    """The constants the preflight's two `Locate` commands print first: before and after the
    printed mark.  Tokens are read across line breaks, since Rocq wraps a long qualified name onto
    the line after "Constant"; "<none>" when a Locate printed no Constant."""
    toks = log.split()
    cut = next((i for i, tok in enumerate(toks) if RESOLUTION_MARK in tok), len(toks))

    def first_constant(part: list[str]) -> str:
        i = next((k for k, tok in enumerate(part) if tok == "Constant"), None)
        return part[i + 1] if i is not None and i + 1 < len(part) else "<none>"

    return first_constant(toks[:cut]), first_constant(toks[cut:])


def instance_candidates(name: str) -> list[str]:
    """--target forms of the corpus Definitions whose body applies `name` (its instantiated forms)."""
    pat = re.compile(rf"^Definition\s+([A-Za-z0-9_']+)\s*:\s*Prop\s*:=\s*@?{re.escape(name)}(?![A-Za-z0-9_'])",
                     re.M)
    out: list[str] = []
    for vf in conjecture_files():
        try:
            clean = strip_comments(vf.read_text())
        except Exception:
            continue
        out += [f"{vf.relative_to(ROOT).parts[0]}/{vf.stem}:{m.group(1)}" for m in pat.finditer(clean)]
    return out


def preflight(area: str, ns: str, stem: str, name: str, timeout: int) -> tuple[str, str]:
    """The probes' common setup must compile on its own: the header, both ladders, the small-model
    import, the statement as a Prop, and each ladder closing a trivial goal.  Otherwise every probe
    would fail before searching (a parse error, an unbuilt or stale module, a renamed statement)
    and read as "not settled", so the statement is INCOMPLETE instead.  The same snippet locates the
    name twice, in the auto layers' context (header + LADDER) and in the small model's (after the
    finite_graph import): both must be the probed module's own definition, or a bare name would
    search another definition (a re-export or a duplicated name).  A setup that fails only because
    the target's type is a product, not Prop, is PARAMETRIC (one classification run)."""
    want = f"{ns}.conjectures.{stem}.{name}"
    body = "\n".join([LADDER, f"Locate {name}.",
                      f"Definition {RESOLUTION_MARK} := 0.", f"Print {RESOLUTION_MARK}.",
                      "From GTBase Require Import finite_graph.", SMALL_LADDER, f"Locate {name}.",
                      f"Check ({name} : Prop).",
                      "Goal True. Proof. __probe. Qed.", "Goal True. Proof. __small_probe. Qed."])
    ok, log = compile_snippet(area, ns, stem, body, max(timeout, 90))
    if not ok:
        classify = "\n".join([f"Check ({name} : forall __vp_x : _, _).", f"Fail Check ({name} : Prop)."])
        is_product, _ = compile_snippet(area, ns, stem, classify, max(timeout, 90))
        if is_product:
            found = instance_candidates(name)
            raise ProbeParametric(
                "its type is a product (Section variables or explicit parameters), not Prop; probe an "
                "instantiated form with --target " + (",".join(found) if found else "<area>/<STEM>:<name>"))
        raise ProbeIncomplete(f"probe setup does not compile: {first_error(log)}")
    got = resolved_constants(log)
    if got != (want, want):
        raise ProbeIncomplete(f"the name does not resolve to {want} in both probe contexts "
                              f"(auto layers: {got[0]}; small model: {got[1]})")
    return got


def leading_binder_types(body: str, limit: int = 2) -> list[str]:
    """Parse the simple leading forall syntax used by conjecture statements."""
    rest = body.strip()
    types: list[str] = []
    while len(types) < limit and rest.startswith("forall"):
        rest = rest[len("forall"):].lstrip()
        groups = []
        while rest.startswith("("):
            end = rest.find(")")
            if end < 0:
                return types
            groups.append(rest[1:end])
            rest = rest[end + 1:].lstrip()
        if groups:
            if not rest.startswith(","):
                return types
            rest = rest[1:].lstrip()
            for group in groups:
                if ":" not in group:
                    return types
                names, typ = group.split(":", 1)
                types.extend([typ.strip()] * len(names.split()))
                if len(types) >= limit:
                    return types[:limit]
            continue
        match = re.match(
            r"([A-Za-z_][A-Za-z0-9_']*(?:\s+[A-Za-z_][A-Za-z0-9_']*)*)\s*:\s*([^,]+),",
            rest,
        )
        if not match:
            return types
        types.extend([match.group(2).strip()] * len(match.group(1).split()))
        rest = rest[match.end():].lstrip()
    return types[:limit]


def small_terms(typ: str) -> list[str]:
    compact = re.sub(r"\s+", "", typ)
    if compact == "nat":
        return ["0", "1"]
    if compact == "sgraph":
        return [
            f"(@fg_mk_sgraph 'I_{n} (fun x y : 'I_{n} => x != y))"
            for n in range(7)
        ]
    if compact == "finType":
        return ["'I_0", "'I_1"]
    if compact == "bool":
        return ["false", "true"]
    return []


def compile_instantiations(area: str, ns: str, stem: str, name: str, body: str,
                           timeout: int) -> tuple[bool, str]:
    binder_types = leading_binder_types(body)
    term_sets = [small_terms(typ) for typ in binder_types]
    if not term_sets or any(not terms for terms in term_sets):
        return False, "<no-supported-leading-binders>"
    combinations = list(itertools.product(*term_sets))[:16]
    commands = ["From GTBase Require Import finite_graph.", SMALL_LADDER]
    for i, terms in enumerate(combinations):
        specialize = " ".join(f"specialize (H {term});" for term in terms)
        commands.append(
            f"Fail Definition __probe_inst_{i} : ~ ({name}) := "
            f"ltac:(move=> H; rewrite /{name} in H; {specialize} __small_probe)."
        )
    ok, log = compile_snippet(area, ns, stem, "\n".join(commands), timeout)
    # All attempted definitions are expected to fail. If one unexpectedly succeeds, Rocq
    # rejects its `Fail` wrapper with this diagnostic: that specialization settled the row.
    settled = (not ok) and "The command has not failed" in log
    # Any other failure (not the timeout budget) happened outside the Fail commands: the
    # specializations never ran, so the row has no verdict.
    if not ok and not settled and log != "<timeout>":
        raise ProbeIncomplete(f"small-model file failed outside its Fail commands: {first_error(log)}")
    return settled, log


def probe_statement(name: str, idx, timeout: int) -> dict:
    dups = getattr(idx, "dups", {})
    if name in dups:
        return {"name": name, "status": "AMBIGUOUS", "flag": False,
                "reason": f"defined in {', '.join(dups[name])}; name the module with --target"}
    if name not in idx:
        return {"name": name, "status": "NOT-FOUND", "flag": False}
    return probe_entry(name, idx[name], timeout)


def probe_entry(name: str, entry: tuple[str, str, str, str], timeout: int) -> dict:
    """Probe `name` as defined in one module: entry = (area, stem, namespace, source body)."""
    area, stem, ns, body = entry
    try:
        # The common setup must compile, and the name must resolve to this module's definition,
        # or no probe below searches the intended statement.
        resolved = preflight(area, ns, stem, name, timeout)
        # Layer 1: auto tripwire, both polarities.
        ok_true, _ = compile_snippet(area, ns, stem, f"{LADDER}\nLemma __pt : {name}. Proof. __probe. Qed.", timeout)
        ok_false, _ = compile_snippet(area, ns, stem, f"{LADDER}\nLemma __pf : ~ ({name}). Proof. __probe. Qed.", timeout)
        # Layer 2: curated witness hint, if present.
        hint = HINTS / f"{name}.v"
        hint_state = "none"
        if hint.exists():
            hint_state = "settles" if compile_hint(area, hint, timeout) else "stale-FIX-OK"
        instantiation, _ = compile_instantiations(area, ns, stem, name, body, timeout)
    except ProbeParametric as exc:
        return {"name": name, "area": area, "flag": False, "status": "PARAMETRIC", "reason": str(exc)}
    except ProbeIncomplete as exc:
        # A probe that could not search (a killed run, a setup that does not compile) leaves the
        # statement without a verdict: neither ok nor FLAGGED.
        return {"name": name, "area": area, "flag": False, "status": "INCOMPLETE", "reason": str(exc)}
    flag = ok_true or ok_false or hint_state == "settles" or instantiation
    return {
        "name": name, "area": area, "flag": flag,
        "auto_true": ok_true, "auto_false": ok_false, "instantiation": instantiation,
        "hint": hint_state, "resolved": resolved,
        "status": "FLAGGED" if flag else "ok",
    }


def names_from_wave(wave: str) -> list[str]:
    data = json.loads((META / "v2_statement_waves.json").read_text())
    w = data.get("waves", {}).get(wave, {})
    return [r.get("formal_name") for r in w.get("rows", {}).values() if r.get("formal_name")]


# A target is (name, entry): entry = (area, stem, namespace, body) probes `name` in that module;
# None looks the name up in the index (probe_statement: NOT-FOUND / AMBIGUOUS / the one definer);
# a dict is a row decided before any coqc run (a --target whose module or definition is missing).

def conjecture_entry(path: Path) -> tuple[str, str, Path]:
    """(area, namespace, path) of a conjecture file; exits on a path outside <area>/theories/conjectures."""
    path = path.resolve()
    try:
        rel = path.relative_to(ROOT)
    except ValueError:
        sys.exit(f"vacuity_probe: {path} is outside the repository")
    if len(rel.parts) != 4 or rel.parts[1:3] != ("theories", "conjectures") or REG.NS.get(rel.parts[0]) is None:
        sys.exit(f"vacuity_probe: {rel} is not <package>/theories/conjectures/<module>.v")
    return rel.parts[0], REG.NS[rel.parts[0]], path


def targets_from_files(files: list[str]) -> list[tuple[str, object]]:
    """Every _statement of each file, probed against THAT file (no index lookup)."""
    out: list[tuple[str, object]] = []
    for fp in files:
        area, ns, path = conjecture_entry(Path(fp if os.path.isabs(fp) else ROOT / fp))
        out += [(name, (area, path.stem, ns, body)) for name, body in statement_bodies(path.read_text()).items()]
    return out


def targets_from_wave(wave: str) -> list[tuple[str, object]]:
    """The formal names of a wave's rows, probed against the wave's defines_file in its repo; a
    name that file does not define falls back to the index.  An unknown wave is an error."""
    w = json.loads((META / "v2_statement_waves.json").read_text()).get("waves", {}).get(wave)
    if not w:
        sys.exit(f"vacuity_probe: no wave {wave} in meta/v2_statement_waves.json")
    area, ns = w.get("repo", ""), REG.NS.get(w.get("repo", ""))
    path = ROOT / area / "theories" / "conjectures" / w.get("defines_file", "")
    bodies = statement_bodies(path.read_text()) if ns and path.is_file() else {}
    out: list[tuple[str, object]] = []
    for row in w.get("rows", {}).values():
        name = row.get("formal_name")
        if name:
            out.append((name, (area, path.stem, ns, bodies[name]) if name in bodies else None))
    return out


def targets_from_all() -> list[tuple[str, object]]:
    """Every _statement of every conjecture file, each probed against its own file."""
    return targets_from_files([str(vf) for vf in conjecture_files() if REG.NS.get(vf.relative_to(ROOT).parts[0])])


def targets_from_specs(specs: list[str]) -> list[tuple[str, object]]:
    """--target area/STEM:name: any Definition `name` of <area>/theories/conjectures/STEM.v."""
    out: list[tuple[str, object]] = []
    for spec in specs:
        module, _, name = spec.partition(":")
        area, _, stem = module.partition("/")
        path = ROOT / area / "theories" / "conjectures" / f"{stem}.v"
        ns = REG.NS.get(area)
        body = definition_body(path.read_text(), name) if (ns and name and stem and path.is_file()) else None
        if body is None:
            out.append((name or spec, {"name": name or spec, "status": "NOT-FOUND", "flag": False,
                                       "reason": f"no Definition {name} in {area}/theories/conjectures/{stem}.v"}))
        else:
            out.append((name, (area, stem, ns, body)))
    return out


NO_SEARCH = ("NOT-FOUND", "AMBIGUOUS", "PARAMETRIC", "INCOMPLETE")


def report(rows: list[dict]) -> int:
    flagged = [r for r in rows if r.get("flag")]
    count = {status: [r for r in rows if r.get("status") == status] for status in NO_SEARCH}
    print(f"\n{'statement':52s} {'auto=T':6s} {'auto=F':6s} {'small':6s} {'hint':14s} verdict")
    print("-" * 100)
    for r in sorted(rows, key=lambda r: (not r.get("flag"), r["name"])):
        if r.get("status") in NO_SEARCH:
            reason = f" ({r['reason']})" if r.get("reason") else ""
            print(f"{r['name']:52s} {'-':6s} {'-':6s} {'-':6s} {'-':14s} {r['status']}{reason}")
            continue
        print(f"{r['name']:52s} {str(r['auto_true']):6s} {str(r['auto_false']):6s} "
              f"{str(r['instantiation']):6s} "
              f"{r['hint']:14s} {'*** FLAGGED ***' if r['flag'] else 'ok'}")
    print("-" * 100)
    for r in sorted(rows, key=lambda r: r["name"]):
        if r.get("resolved"):
            print(f"RESOLVED {r['name']} -> {r['resolved'][0]} | {r['resolved'][1]}")
    print(f"{len(rows)} probed · {len(flagged)} FLAGGED"
          + (f" · {len(count['INCOMPLETE'])} INCOMPLETE (no search ran)" if count["INCOMPLETE"] else "")
          + (f" · {len(count['NOT-FOUND'])} NOT-FOUND (not in the index)" if count["NOT-FOUND"] else "")
          + (f" · {len(count['AMBIGUOUS'])} AMBIGUOUS (defined in two or more files)" if count["AMBIGUOUS"] else "")
          + (f" · {len(count['PARAMETRIC'])} PARAMETRIC (type not Prop; probe an instantiated form)"
             if count["PARAMETRIC"] else ""))
    return 1 if flagged or any(count.values()) else 0


def probe_many(names: list[str], idx, timeout: int, jobs: int) -> list[dict]:
    with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, jobs)) as pool:
        return list(pool.map(lambda name: probe_statement(name, idx, timeout), names))


def probe_target(target: tuple[str, object], idx, timeout: int) -> dict:
    name, entry = target
    if isinstance(entry, dict):
        return entry
    return probe_statement(name, idx, timeout) if entry is None else probe_entry(name, entry, timeout)


def probe_targets(targets: list[tuple[str, object]], idx, timeout: int, jobs: int) -> list[dict]:
    with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, jobs)) as pool:
        return list(pool.map(lambda target: probe_target(target, idx, timeout), targets))


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
    area, stem, ns, _body = ctx
    body = (f"{LADDER}\n"
            f"Definition __probe_selftest_vacuous_statement : Prop := True.\n"
            f"Lemma __pt : __probe_selftest_vacuous_statement. Proof. __probe. Qed.")
    ok, _ = compile_snippet(area, ns, stem, body, timeout)
    return ok


def recall_instantiations(idx, timeout: int) -> bool:
    """The specialized small-model path must refute `forall n, 0 < n` at n=0."""
    ctx = next(iter(idx.values()), None)
    if ctx is None:
        return False
    area, stem, ns, _body = ctx
    fixture = (f"{LADDER}\n"
               "Definition __probe_inst_fixture_statement : Prop := forall n : nat, 0 < n.\n"
               "Definition __probe_inst_fixture_refutation : "
               "~ __probe_inst_fixture_statement := "
               "ltac:(move=> H; rewrite /__probe_inst_fixture_statement in H; "
               "specialize (H 0); __probe).")
    ok, _ = compile_snippet(area, ns, stem, fixture, timeout)
    return ok


def validate(idx, timeout: int, jobs: int) -> int:
    """Self-test.  Exits 0 in a healthy tree; exits 1 if EITHER a historical fix is reverted
    (regression) OR the recall fixture stops flagging OR a control produces a false positive.

      (a) REGRESSION — every historical fix must still hold: its witness must report
          `stale-FIX-OK` and NOT be flagged.  Reverting a fix flips the hint to `settles`.
      (b) RECALL — a genuinely settleable (trivially-true) fixture MUST be flagged, proving
          the flagging path works even though (a) flags nothing in a healthy tree.
      (c) CONTROL — known-good statements must stay ok (no false positives).
    """
    print("== REGRESSION: historical fixes — hints must be stale-FIX-OK (NOT flagged) ==")
    b = probe_many(HISTORICAL_FIXES, idx, timeout, jobs)
    report(b)
    reverted = [r for r in b if r.get("flag") or r.get("hint") != "stale-FIX-OK"]
    for r in reverted:
        print(f"!! REGRESSION: {r['name']} expected hint=stale-FIX-OK, got "
              f"hint={r.get('hint')} flag={r.get('flag')} — was a fix reverted?")

    print("\n== RECALL: synthetic vacuous fixture — MUST FLAG ==")
    try:
        recall_ok = recall_flags(idx, timeout)
    except ProbeIncomplete as exc:
        print(f"!! RECALL: {exc}")
        recall_ok = False
    print(f"synthetic trivially-true statement flagged by AUTO tripwire: {recall_ok}   (want True)")
    if not recall_ok:
        print("!! RECALL: the flagging path did not fire on a trivially-true statement")
    try:
        instantiation_ok = recall_instantiations(idx, timeout)
    except ProbeIncomplete as exc:
        print(f"!! RECALL: {exc}")
        instantiation_ok = False
    print(f"synthetic forall-n statement refuted at n=0:             {instantiation_ok}   (want True)")
    if not instantiation_ok:
        print("!! RECALL: the instantiation/small-model path did not fire")

    print("\n== CONTROL: known-good — should stay ok ==")
    g = probe_many(CONTROL_GOOD, idx, timeout, jobs)
    report(g)
    fp = sum(r["flag"] for r in g)
    # An INCOMPLETE or NOT-FOUND row is not a pass: no search ran on it, so it was never checked.
    incomplete = [r["name"] for r in b + g if r.get("status") in ("INCOMPLETE", "NOT-FOUND")]

    print("\n== summary ==")
    print(f"regression (historical fixes stale-FIX-OK): {'PASS' if not reverted else 'FAIL'}")
    print(f"recall (synthetic vacuous flagged):         {'PASS' if recall_ok else 'FAIL'}")
    print(f"recall (small-model specialization):        {'PASS' if instantiation_ok else 'FAIL'}")
    print(f"control false-positives:                    {fp}/{len(g)}   (want 0)")
    print(f"rows without a verdict (no search ran):     {len(incomplete)}   (want 0)")
    return 0 if (not reverted and recall_ok and instantiation_ok and fp == 0 and not incomplete) else 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--names"); ap.add_argument("--files", nargs="*")
    ap.add_argument("--wave"); ap.add_argument("--all", action="store_true")
    ap.add_argument("--target", help="comma-separated area/STEM:name (any Definition of that module)")
    ap.add_argument("--validate", action="store_true")
    ap.add_argument("--timeout", type=int, default=DEFAULT_TIMEOUT)
    ap.add_argument("--jobs", type=int, default=4)
    a = ap.parse_args()
    idx = build_index()
    if a.validate:
        sys.exit(validate(idx, a.timeout, a.jobs))
    if a.names:
        targets = [(n.strip(), None) for n in a.names.split(",") if n.strip()]
    elif a.files:
        targets = targets_from_files(a.files)
    elif a.wave:
        targets = targets_from_wave(a.wave)
    elif a.all:
        targets = targets_from_all()
    elif a.target:
        targets = targets_from_specs([s.strip() for s in a.target.split(",") if s.strip()])
    else:
        ap.error("one of --names/--files/--wave/--all/--target/--validate required")
    if not targets:
        # Nothing to search is not a pass: a request that names no target probes nothing.
        sys.exit("vacuity_probe: the request names no target to probe")
    sys.exit(report(probe_targets(targets, idx, a.timeout, a.jobs)))


if __name__ == "__main__":
    main()

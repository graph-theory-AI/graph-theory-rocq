#!/usr/bin/env python3
"""Acceptance gate for a landed milestone:  python3 meta/check_milestone.py <phase> <package>

Verifies, against the live opam switch `digraph`:
  1. every expected formal_name (from milestone_rows.py) is Defined in theories/conjectures/<phase>.v;
  2. the milestone .v files are listed in the package _CoqProject;
  3. the package compiles (coq_makefile + make);
  4. Print Assumptions is clean (Closed under the global context) for every statement node;
  5. no top-level Axiom / Parameter / Admitted / Conjecture / Hypothesis (outside comments);
  6. each non-todo leg in the corpus overlay (meta/opg_legs_state.json or meta/v2_legs_state.json,
     routed by phase via meta/corpus_registry.py) is justified by an artifact + carries provenance;
     for source-verified corpora (v2), a statement leg may be `done` only with a complete
     source-verification tuple (locator + hash + second-reader identity + date).
  7. no forbidden exact-type faithfulness signatures are committed:
     unconditional refutations of non-disproved rows, or direct proofs of undecided rows.
Exit 0 iff all pass. Run only inside (or with) the `digraph` switch on PATH.
"""
import json, os, re, sys, subprocess, glob

META = os.path.dirname(os.path.abspath(__file__))
MONO = os.path.dirname(META)
sys.path.insert(0, META)
import corpus_registry as REG
import gate_contracts as CONTRACTS
import rocq_toolchain as ROCQ
import formal_resolutions as RESOLUTIONS
NS = REG.NS

argv = sys.argv[1:]
# `--overlay <path>` (debugging only): read the leg-state overlay of check 6 from another file,
# e.g. a scratch copy produced by `meta/sync_edge_legs.py --write`, so a candidate sync can be
# gate-tested before it touches the committed overlays. Everything else is unaffected.
overlay_override = None
if "--overlay" in argv:
    i = argv.index("--overlay")
    if i + 1 >= len(argv):
        sys.exit("usage: check_milestone.py <phase> <package> [--overlay <legs_state.json>]")
    overlay_override = os.path.abspath(argv[i + 1])
    del argv[i:i + 2]
if len(argv) < 2:
    sys.exit("usage: check_milestone.py <phase> <package> [--overlay <legs_state.json>]")
phase, package = argv[0], argv[1]
CORPUS = REG.corpus_for_phase(phase)
pkg = os.path.join(MONO, package)
# graph-theory-base is in the registry NS map (report display) but is NOT a milestone package —
# keep the historical rejection the private dict encoded by omitting it.
ns = None if package == "graph-theory-base" else NS.get(package)
results = []  # (ok, label, detail)
def chk(ok, label, detail=""): results.append((bool(ok), label, detail))

def strip_comments(t):
    """Strip nested Rocq block comments while preserving line/column shape."""
    out, i, depth = [], 0, 0
    while i < len(t):
        if t.startswith("(*", i):
            depth += 1
            out.extend("  ")
            i += 2
        elif depth and t.startswith("*)", i):
            depth -= 1
            out.extend("  ")
            i += 2
        elif depth:
            out.append("\n" if t[i] == "\n" else " ")
            i += 1
        else:
            out.append(t[i])
            i += 1
    return "".join(out)

DECL_RE = re.compile(
    r"^\s*(?:(?:Local|Global|Polymorphic|Program)\s+)*"
    r"(?:Lemma|Theorem|Corollary|Proposition|Fact|Remark)\s+([A-Za-z0-9_']+)\b",
    re.M,
)
IDENT_CHARS = "A-Za-z0-9_'"

def coq_sentence_from(t, start):
    """Return the declaration command starting at start, approximately through its final period."""
    i = start
    while True:
        j = t.find(".", i)
        if j < 0:
            return t[start:]
        nxt = t[j + 1:j + 2]
        # Qualified names contain dots followed by identifier chars; command terminators do not.
        if not nxt or nxt.isspace():
            return t[start:j + 1]
        i = j + 1

def module_of_rel(ns, rel):
    mod = rel[:-2].replace(os.sep, ".").replace("/", ".")
    if mod.startswith("theories."):
        mod = mod[len("theories."):]
    return f"{ns}.{mod}"

def project_v_files(pkg, cqp_txt):
    files = []
    for raw in cqp_txt.splitlines():
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        rel = line.split()[0]
        if rel.startswith("theories/") and rel.endswith(".v") and os.path.exists(os.path.join(pkg, rel)):
            files.append(rel)
    return files

def incl_flags_from_cqp(cqp_txt):
    incl_flags = []
    for m in re.findall(r"-[QR]\s+\S+\s+\S+", cqp_txt):
        incl_flags += m.split()
    return incl_flags

def faithfulness_candidates(pkg, ns, cqp_txt, target_names):
    files = project_v_files(pkg, cqp_txt)
    sources = []
    for rel in files:
        try:
            src = open(os.path.join(pkg, rel)).read()
        except OSError:
            continue
        mod = module_of_rel(ns, rel)
        sources.append((mod, rel, src))
    return CONTRACTS.faithfulness_candidate_records(sources, target_names)

# Use the same toolchain as the formal-resolution checker.
env = ROCQ.environment()
def run(cmd, cwd=None):
    return subprocess.run(cmd, cwd=cwd or pkg, env=env, capture_output=True, text=True)

# expected formal_names from the deterministic loader
proc = subprocess.run([sys.executable, os.path.join(META, "milestone_rows.py"), phase, package],
                      capture_output=True, text=True)
if proc.returncode != 0:
    sys.exit(f"milestone_rows.py failed:\n{proc.stderr}")
rows = json.loads(proc.stdout)
expected = [r["formal_name"] for r in rows]
slugs = [r["slug"] for r in rows]

stmt = os.path.join(pkg, "theories", "conjectures", f"{phase}.v")
grounding = os.path.join(pkg, "theories", "conjectures", f"grounding_{phase}.v")
implications = os.path.join(pkg, "theories", "conjectures", f"implications_{phase}.v")
chk(ns, "package known", package if ns else f"unknown package {package}")
chk(os.path.exists(stmt), "statement file exists", stmt)

# 1) every expected formal_name is Defined — search ALL conjecture files, not just
#    <phase>.v: some milestones (e.g. the absorbed Digraph P9) define "already-formalized"
#    rows in sibling files (classic_core.v / packing.v / sad.v) re-exported by <phase>.v.
conj_dir = os.path.join(pkg, "theories", "conjectures")
def_re = re.compile(r"^\s*Definition\s+([A-Za-z0-9_']+)", re.M)
defined_in = {}  # formal_name -> module basename (no .v) that defines it
for vf in sorted(glob.glob(os.path.join(conj_dir, "*.v"))):
    base = os.path.basename(vf)[:-2]
    try:
        for n in def_re.findall(open(vf).read()):
            defined_in.setdefault(n, base)
    except OSError:
        pass
defined = set(defined_in)
missing = [n for n in expected if n not in defined]
chk(not missing, f"all {len(expected)} formal_names Defined", f"missing: {missing}" if missing else "")

# 2) milestone .v files in _CoqProject
cqp = os.path.join(pkg, "_CoqProject")
cqp_txt = open(cqp).read() if os.path.exists(cqp) else ""
need_files = [f"theories/conjectures/{phase}.v"] + \
             [f"theories/conjectures/{os.path.basename(p)}" for p in (grounding, implications) if os.path.exists(p)]
notlisted = [f for f in need_files if f not in cqp_txt]
chk(os.path.exists(cqp) and not notlisted, "files in _CoqProject", f"not listed: {notlisted}" if notlisted else "")

# 3) build sibling dependencies referenced in _CoqProject (e.g. -Q ../base/theories GTBase), then compile
deps = re.findall(r"-[QR]\s+\.\./([\w.-]+)/theories\s+\S+", cqp_txt)
dep_fail = []
for dep in deps:
    dpath = os.path.join(MONO, dep)
    if os.path.isfile(os.path.join(dpath, "_CoqProject")):
        dm = run(["bash", "-c", "rocq makefile -f _CoqProject -o Makefile.coq && make -f Makefile.coq"], cwd=dpath)
        if dm.returncode != 0:
            dep_fail.append(dep)
chk(not dep_fail, f"dependencies build ({', '.join(deps) or 'none'})", f"failed: {dep_fail}" if dep_fail else "")
mk = run(["bash", "-c", "rocq makefile -f _CoqProject -o Makefile.coq && make -f Makefile.coq"])
compiles = mk.returncode == 0
chk(compiles, "package compiles", "" if compiles else (mk.stdout + mk.stderr)[-500:])

# 5) no top-level axioms/admits (outside comments)
axiom_re = re.compile(r"^\s*(Axiom|Parameter|Admitted|Conjecture|Hypothesis|admit)\b", re.M)
ax_hits = []
for p in (stmt, grounding, implications):
    if os.path.exists(p):
        for m in axiom_re.finditer(strip_comments(open(p).read())):
            ax_hits.append(f"{os.path.basename(p)}:{m.group(1)}")
chk(not ax_hits, "no top-level Axiom/Parameter/Admitted", f"found: {ax_hits}" if ax_hits else "")

# 4) Print Assumptions clean for every statement node (probe compiled against the built .vo)
assum_ok, assum_detail = False, "skipped (compile failed)"
if compiles and ns:
    probe = os.path.join(pkg, "theories", "conjectures", f"_assum_{phase}.v")
    # import EVERY conjecture module that defines an expected name (not just <phase>.v):
    # milestones like Digraph P9 spread "already-formalized" rows across sibling files.
    mods = sorted({defined_in[n] for n in expected if n in defined_in} | {phase})
    body = f"From {ns}.conjectures Require Import {' '.join(mods)}.\n" + \
           "".join(f"Print Assumptions {n}.\n" for n in expected)
    open(probe, "w").write(body)
    # build coqc include flags as an argv LIST (no shell string interpolation of _CoqProject paths)
    incl_flags = incl_flags_from_cqp(cqp_txt)
    if not incl_flags:
        incl_flags = ["-R", "theories", ns]
    pr = run(["coqc"] + incl_flags + [f"theories/conjectures/_assum_{phase}.v"])
    out = pr.stdout + pr.stderr
    closed = out.count("Closed under the global context")
    has_axioms = "Axioms:" in out
    assum_ok = (pr.returncode == 0) and (not has_axioms) and (closed == len(expected))
    assum_detail = "" if assum_ok else f"closed={closed}/{len(expected)} has_axioms={has_axioms}; {out[-300:]}"
    for f in glob.glob(os.path.join(pkg, "theories", "conjectures", f"_assum_{phase}*")) + \
             glob.glob(os.path.join(pkg, "theories", "conjectures", f"._assum_{phase}*")):
        os.remove(f)
n_axfree = closed if (compiles and ns) else 0
chk(assum_ok, f"Print Assumptions clean ({n_axfree}/{len(expected)} statements)", assum_detail)

# 7) Exact-type faithfulness probes:
#    - no unconditional refutation of a non-disproved row;
#    - no direct proof of an undecided row (manifest status open/partial).
faith_ok, faith_detail = False, "skipped (compile failed)"
cases = []
verified_resolution_keys = set()
resolution_error = ""
if compiles and ns:
    statement_names = {f"{ns}.conjectures.{defined_in[n]}.{n}"
                       for n in expected if n in defined_in}
    try:
        checked_resolutions = RESOLUTIONS.verify_resolutions(
            package=package, statement_names=statement_names, build=False)
        verified_resolution_keys = {r.exact_type_key for r in checked_resolutions}
    except (RESOLUTIONS.ResolutionError, RuntimeError) as exc:
        resolution_error = str(exc)
    chk(not resolution_error, "registered formal resolutions checked", resolution_error)
if compiles and ns:
    probe = os.path.join(pkg, "theories", "conjectures", f"_faith_{phase}.v")
    incl_flags = incl_flags_from_cqp(cqp_txt)
    if not incl_flags:
        incl_flags = ["-R", "theories", ns]
    rows_by_name = {r["formal_name"]: r for r in rows}
    candidates = faithfulness_candidates(pkg, ns, cqp_txt, [n for n in expected if n in defined_in])
    modules = {f"{ns}.conjectures.{defined_in[n]}" for n in expected if n in defined_in}
    for n in expected:
        row = rows_by_name.get(n, {})
        status = row.get("status", "")
        stmt_q = f"{ns}.conjectures.{defined_in[n]}.{n}" if n in defined_in else n
        for qname, rel, decl in candidates.get(n, []):
            modules.add(qname.rsplit(".", 1)[0])
            for kind, typ in CONTRACTS.forbidden_exact_types(
                    status, stmt_q, qname, verified_resolution_keys):
                cases.append((kind, n, qname, rel, decl, typ))

    lines = [f"Require Import {m}." for m in sorted(modules)]
    line_map = {}
    for kind, n, qname, rel, decl, typ in cases:
        lines.append(f"(* FAITHFULNESS {kind}: {rel}:{decl} against {n} *)")
        line_no = len(lines) + 1
        line_map[line_no] = f"{kind}: {qname} has forbidden exact type {typ}"
        lines.append(f"Fail Check ({qname} : {typ}).")
    open(probe, "w").write("\n".join(lines) + "\n")
    pr = run(["coqc"] + incl_flags + [f"theories/conjectures/_faith_{phase}.v"])
    out = pr.stdout + pr.stderr
    faith_ok = pr.returncode == 0
    if faith_ok:
        faith_detail = ""
    else:
        line_matches = re.findall(r"_faith_[^\"']+\.v\"?, line (\d+)", out)
        mapped = ""
        if line_matches:
            mapped = line_map.get(int(line_matches[-1]), "")
        faith_detail = (mapped + "; " if mapped else "") + out[-500:]
    for f in glob.glob(os.path.join(pkg, "theories", "conjectures", f"_faith_{phase}*")) + \
             glob.glob(os.path.join(pkg, "theories", "conjectures", f"._faith_{phase}*")):
        os.remove(f)
chk(faith_ok, f"faithfulness exact-type probes ({len(cases)} forbidden shapes tested)", faith_detail)

# 6) overlay legs justified by artifacts + provenance (+ v2: source-verification tuple)
legs_path = overlay_override or REG.overlay_path(CORPUS)
overlay = json.load(open(legs_path)).get("entries", {}) if os.path.exists(legs_path) else {}
needs_sver = REG.CORPORA[CORPUS]["requires_source_verification"]
rows_by_slug = {r["slug"]: r for r in rows}
# An `edges` leg is justified either by THIS milestone's implications file, or by an artifact the
# milestone does not host: the proof of an edge touching the row may live in another phase's
# implications file (waves X21x/X22x host cross-milestone edges) or, later, in the `atlas`
# package, and a corpus relation may be discharged by a DOCUMENTED NON-EDGE instead of a proof.
# The discharge logic is not duplicated here: meta/sync_edge_legs.py owns it (EdgeEvidence.
# leg_artifact) and derives the same legs the overlay carries. The import is guarded — the wave
# registry meta/edge_waves.json and meta/corpus_relations.json are optional inputs, and a missing
# module must degrade to the historical "implications file required" rule, never crash the gate.
EDGE_EVIDENCE = None
try:
    import sync_edge_legs as EDGELEGS
    EDGE_EVIDENCE = EDGELEGS.EdgeEvidence()
except Exception as _exc:                                    # noqa: BLE001 (gate must not crash)
    sys.stderr.write(f"WARNING: edge-evidence unavailable ({_exc}); an `edges` leg is justified "
                     f"only by this milestone's implications file\n")

def edges_leg_artifact(slug):
    """Reason a non-todo `edges` leg on this row is backed by an out-of-milestone artifact, or ''."""
    if EDGE_EVIDENCE is None:
        return ""
    return EDGE_EVIDENCE.leg_artifact(rows_by_slug.get(slug, {}).get("formal_name")) or ""

unjust = []
for s in slugs:
    e = overlay.get(s)
    if not e:
        unjust.append(f"{s}: no overlay entry (every milestone row needs overlay leg-state + provenance)")
        continue
    if e.get("statement") == "done" and not (compiles and not missing):
        unjust.append(f"{s}: statement=done but not (compiles & defined)")
    if e.get("grounding") == "done" and not (compiles and os.path.exists(grounding)):
        unjust.append(f"{s}: grounding=done but grounding file missing/not compiled")
    if e.get("edges") in ("partial", "done") and not os.path.exists(implications) \
            and not edges_leg_artifact(s):
        unjust.append(f"{s}: edges={e.get('edges')} but no implications file, no "
                      f"verified/conditional edge touching "
                      f"{rows_by_slug.get(s, {}).get('formal_name')!r} in "
                      f"meta/dependency_graph.json, and an undischarged corpus relation")
    for lg in ("statement", "grounding", "edges", "correspondence", "audit_page"):
        if e.get(lg, "todo") not in ("todo", "partial", "done", "blocked"):
            unjust.append(f"{s}: leg {lg} has out-of-vocabulary state {e.get(lg)!r}")
    for lg in ("statement", "grounding", "edges"):
        if e.get(lg, "todo") != "todo" and not (e.get("commit") and e.get("package")):
            unjust.append(f"{s}: non-todo {lg} lacks commit+package provenance")
    # v2 invariant (plan §2): statement=done requires the auditable verification tuple —
    # locator + hash + a second reader distinct from the implementer + a date. The tuple lives
    # on the manifest row (emitted by milestone_rows.py); the boolean flag is never trusted.
    if needs_sver and e.get("statement") == "done":
        for err in REG.verification_tuple_errors(rows_by_slug.get(s, {})):
            unjust.append(f"{s}: statement=done without source verification ({err})")
chk(not unjust, "overlay leg-state justified by artifacts", "; ".join(unjust[:6]) if unjust else "")

# ── report ──
print(f"\n=== check_milestone {phase} / {package} ===")
print(f"  {len(expected)} statement nodes: {', '.join(expected)}")
for ok, label, detail in results:
    print(f"  [{'PASS' if ok else 'FAIL'}] {label}" + (f"  — {detail}" if (detail and not ok) else ""))
allok = all(ok for ok, _, _ in results)
n_def = len(expected) - len(missing)
print(f"\n{'ACCEPTED' if allok else 'REJECTED'}: {sum(ok for ok,_,_ in results)}/{len(results)} CHECKS passed | "
      f"statements: {n_def}/{len(expected)} Defined, {n_axfree}/{len(expected)} axiom-free.")
print("  (NB: the X/Y above counts acceptance CHECKS, not statement rows — the row count is the line above.)")
sys.exit(0 if allok else 1)

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
  8. prospective v2 waves (X211+) pass hard faithfulness lint and every done row carries
     independently-audited grounding metadata naming Qed certificates in grounding_<phase>.v.
Exit 0 iff all pass. Run only inside (or with) the `digraph` switch on PATH.
"""
import json, os, re, sys, subprocess, glob

META = os.path.dirname(os.path.abspath(__file__))
MONO = os.path.dirname(META)
sys.path.insert(0, META)
import corpus_registry as REG
NS = REG.NS

if len(sys.argv) < 3:
    sys.exit("usage: check_milestone.py <phase> <package>")
phase, package = sys.argv[1], sys.argv[2]
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
    candidates = {n: [] for n in target_names}
    pats = {n: re.compile(rf"(?<![{IDENT_CHARS}]){re.escape(n)}(?![{IDENT_CHARS}])")
            for n in target_names}
    for rel in files:
        try:
            src = strip_comments(open(os.path.join(pkg, rel)).read())
        except OSError:
            continue
        mod = module_of_rel(ns, rel)
        for m in DECL_RE.finditer(src):
            decl = coq_sentence_from(src, m.start())
            mentioned = [n for n, pat in pats.items() if pat.search(decl)]
            if not mentioned:
                continue
            qname = f"{mod}.{m.group(1)}"
            for n in mentioned:
                candidates[n].append((qname, rel, m.group(1)))
    return candidates

# switch resolution: prefer PATH, else the known global switch bin
SW = os.path.expanduser("~/.opam/digraph/bin")
env = dict(os.environ)
if os.path.isdir(SW):
    env["PATH"] = SW + os.pathsep + env.get("PATH", "")
    env.setdefault("OPAM_SWITCH_PREFIX", os.path.expanduser("~/.opam/digraph"))
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

# 8) Prospective acceptance policy. Legacy X1-X210 rows remain auditable backlog; X211+
# cannot reach statement=done without hard lint, an independent wave verdict, and named
# grounding certificates for inhabited hypotheses / non-triviality / helper sanity.
policy = json.load(open(os.path.join(META, "faithfulness_policy.json")))
phase_number = re.fullmatch(r"X(\d+)", phase)
prospective = CORPUS == "v2" and phase_number \
    and int(phase_number.group(1)) >= int(policy["prospective_v2_wave_min"])
grounding_certificates = []
prospective_errors = []
if prospective:
    lint = subprocess.run(
        [sys.executable, os.path.join(META, "faithfulness_lint.py"),
         "--files", os.path.relpath(stmt, MONO), "--check"],
        cwd=MONO, capture_output=True, text=True,
    )
    chk(lint.returncode == 0, "prospective hard faithfulness lint",
        "" if lint.returncode == 0 else (lint.stdout + lint.stderr)[-1000:])

    wave_data = json.load(open(os.path.join(META, "v2_statement_waves.json"))).get("waves", {})
    matching_waves = [w for w in wave_data.values()
                      if w.get("phase") == phase and w.get("repo") == package]
    if len(matching_waves) != 1:
        prospective_errors.append(f"expected one wave metadata record, found {len(matching_waves)}")
        wave = {"rows": {}}
    else:
        wave = matching_waves[0]
        reader = wave.get("faithfulness_verified_by")
        if not reader or not wave.get("faithfulness_result"):
            prospective_errors.append("wave lacks faithfulness_verified_by/faithfulness_result")
        if reader and reader == wave.get("implemented_by"):
            prospective_errors.append("faithfulness_verified_by equals implemented_by")

    manifest_by_slug = {r["slug"]: r for r in REG.load_manifest(CORPUS)["rows"]}
    statement_src = strip_comments(open(stmt).read()) if os.path.exists(stmt) else ""
    helper_prefix = f"x{phase_number.group(1)}_"
    local_helpers = [name for name in re.findall(
        r"^\s*Definition\s+([A-Za-z0-9_']+)", statement_src, re.M)
                     if name.startswith(helper_prefix) and not name.endswith("_statement")]
    required_fields = policy["grounding"]["required_fields"]
    required_states = set(policy["grounding"]["required_statement_states"])
    for slug in slugs:
        row = manifest_by_slug[slug]
        state = row.get("legs", {}).get("statement", "todo")
        if state not in required_states:
            continue
        row_wave = wave.get("rows", {}).get(slug, {})
        spec = row_wave.get("grounding")
        if not isinstance(spec, dict):
            prospective_errors.append(f"{slug}: missing grounding metadata object")
            continue
        missing_fields = [field for field in required_fields if field not in spec]
        if missing_fields:
            prospective_errors.append(f"{slug}: grounding metadata misses {missing_fields}")
            continue
        for field in ("hyp_inhabited", "not_trivially_true"):
            if not isinstance(spec[field], str) or not spec[field]:
                prospective_errors.append(f"{slug}: grounding.{field} must name one certificate")
            else:
                grounding_certificates.append(spec[field])
        helpers = spec["helper_sanity"]
        if not isinstance(helpers, list) or not all(isinstance(x, str) and x for x in helpers):
            prospective_errors.append(f"{slug}: grounding.helper_sanity must be a list of names")
        else:
            grounding_certificates.extend(helpers)
            if local_helpers and not helpers:
                prospective_errors.append(
                    f"{slug}: local helpers {local_helpers[:5]} require helper_sanity certificates")

    if not os.path.exists(grounding):
        prospective_errors.append(f"prospective done rows require {os.path.basename(grounding)}")
    else:
        grounding_src = strip_comments(open(grounding).read())
        proof_decl_re = re.compile(
            r"^\s*(?:Lemma|Theorem|Corollary|Proposition|Fact|Remark|Definition)\s+"
            r"([A-Za-z0-9_']+)\b", re.M)
        declared_certs = set(proof_decl_re.findall(grounding_src))
        missing_certs = sorted(set(grounding_certificates) - declared_certs)
        if missing_certs:
            prospective_errors.append(f"grounding file misses named certificates {missing_certs}")
    chk(not prospective_errors, "prospective audit + grounding contract",
        "; ".join(prospective_errors[:8]) if prospective_errors else "")

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
    if grounding_certificates:
        mods.append(f"grounding_{phase}")
    assumption_names = expected + grounding_certificates
    body = f"From {ns}.conjectures Require Import {' '.join(sorted(set(mods)))}.\n" + \
           "".join(f"Print Assumptions {n}.\n" for n in assumption_names)
    open(probe, "w").write(body)
    # build coqc include flags as an argv LIST (no shell string interpolation of _CoqProject paths)
    incl_flags = incl_flags_from_cqp(cqp_txt)
    if not incl_flags:
        incl_flags = ["-R", "theories", ns]
    pr = run(["coqc"] + incl_flags + [f"theories/conjectures/_assum_{phase}.v"])
    out = pr.stdout + pr.stderr
    closed = out.count("Closed under the global context")
    has_axioms = "Axioms:" in out
    assum_ok = (pr.returncode == 0) and (not has_axioms) and (closed == len(assumption_names))
    assum_detail = "" if assum_ok else \
        f"closed={closed}/{len(assumption_names)} has_axioms={has_axioms}; {out[-300:]}"
    for f in glob.glob(os.path.join(pkg, "theories", "conjectures", f"_assum_{phase}*")) + \
             glob.glob(os.path.join(pkg, "theories", "conjectures", f"._assum_{phase}*")):
        os.remove(f)
n_axfree = min(closed, len(expected)) if (compiles and ns) else 0
chk(assum_ok, f"Print Assumptions clean ({n_axfree}/{len(expected)} statements"
    + (f" + {len(grounding_certificates)} grounding certificates" if grounding_certificates else "")
    + ")", assum_detail)

# 7) Exact-type faithfulness probes:
#    - no unconditional refutation of a non-disproved row;
#    - no direct proof of an undecided row (manifest status open/partial).
faith_ok, faith_detail = False, "skipped (compile failed)"
cases = []
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
            if status != "disproved":
                cases.append(("unconditional-refutation", n, qname, rel, decl, f"~ {stmt_q}"))
            if status in ("open", "partial"):
                cases.append(("direct-proof-undecided", n, qname, rel, decl, stmt_q))

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
legs_path = REG.overlay_path(CORPUS)
overlay = json.load(open(legs_path)).get("entries", {}) if os.path.exists(legs_path) else {}
needs_sver = REG.CORPORA[CORPUS]["requires_source_verification"]
rows_by_slug = {r["slug"]: r for r in rows}
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
    if e.get("edges") in ("partial", "done") and not os.path.exists(implications):
        unjust.append(f"{s}: edges={e.get('edges')} but no implications file")
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

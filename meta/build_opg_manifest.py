#!/usr/bin/env python3
"""Build the validated 227-row corpus manifest (v2 — review fixes 2026-06-26):
valid+unique Rocq formal_names, no empty source_propositions, exact status_semantics for all
18 non-open records, resolved routing, corrected existing-node mapping, precise Ádám encoding."""
import json, re, os, sys
from collections import Counter, OrderedDict

META = os.path.dirname(os.path.abspath(__file__))           # graph-theory-rocq/meta
REPO = os.path.dirname(META)                                # graph-theory-rocq (monorepo root)
sys.path.insert(0, META)
import corpus_registry as REG
GC = REG.graph_conjectures_dir()                            # the nested graph-conjectures clone
# HEAD of the clone, and the last commit touching data/problems.json (the OPG source array).
SRC_COMMIT_REPO = "b72c5857060addbe4523016e88ae3aa626e958fd"
SRC_COMMIT_PROBLEMS = "56fa4523d69544a34c6df4280302fcc2af3943fe"

prob = {p['slug']: p for p in json.load(open(f"{GC}/data/problems.json"))}
# raw classifier output committed in meta/ (the manifest's upstream); GRAPH_CONJECTURES env
# overrides the corpus location for provenance/source_text.
cls = json.load(open(f"{META}/opg_full_classification.json"))['classifications']

# slugs already covered by digraph-theory's existing nodes (verified constant names)
ALREADY = {
 'seymours_second_neighbourhood_conjecture':'seymour_second_neighbourhood_statement',
 'caccetta_haggkvist_conjecture':'caccetta_haggkvist_statement',
 'woodalls_conjecture':'woodall_statement',
 'the_bermond_thomassen_conjecture':'bermond_thomassen_statement',
 'arc_disjoint_strongly_connected_spanning_subdigraphs':'bang_jensen_yeo_SAD_statement',
 'splitting_a_digraph_with_minimum_outdegree_constraints':'splitting_min_outdegree_statement',
 'long_directed_cycles_in_digraph_with_minimum_in_and_out_degree':'long_dicycle_diregular_statement',
 'stable_set_meeting_all_longest_directed_paths':'stable_meeting_longest_dipaths_statement',
 'monochromatoc_reachability_in_arc_colored_digraphs':'mono_reach_or_rainbow_statement',
 'directed_cycle_of_length_twice_the_minimum_outdegree':'cheng_keevash_conj1_statement',  # FIX (was long_dipath_statement)
 'linial_berge_path_partition_duality':'linial_berge_statement',
 'erdos_posa_property_for_long_directed_cycles':'erdos_posa_long_dicycles_statement',
}

# exact settled/open semantics for every non-open record (14 partial + 3 solved + 1 disproved)
STATUS_SEM = {
 'hedetniemis_conjecture':"DISPROVED — Shitov (2019): there exist finite G,H with χ(G×H) < min(χ(G),χ(H)). The historical equality is stated as a Definition; its negation/refutation is OPTIONAL applications/ work (not required for M-CORE).",
 'erdos_faber_lovasz_conjecture':"SOLVED for all large n — Kang–Kelly–Kühn–Methuku–Osthus (2023). Stated as a Definition (statement-only goal); a proof is optional applications/ work.",
 'signing_a_graph_to_have_small_magnitude_eigenvalues':"SOLVED (Bilu–Linial signing → bipartite Ramanujan, Marcus–Spielman–Srivastava 2015). DEFERRED (spectral, D5); stated as a Definition only.",
 'ptas_for_feedback_arc_set_in_tournaments':"SOLVED — Kenyon-Mathieu-Schudy PTAS (2007). Stated as the math predicate ∃ approximation-scheme; the cost-model/algorithm is out of scope (D7).",
 'double_critical_graph_conjecture':"PARTIAL — verified for k ≤ 5 (Mozhan; Stiebitz); open for k ≥ 6. Node states the full conjecture; the small-k cases are optional applications/.",
 'large_induced_forest_in_a_planar_graph':"PARTIAL — partial lower bounds on the induced-forest size are proven; the conjectured fraction is open. Node states the conjectured bound (DEFERRED-adjacent: planarity, gate G2).",
 'partial_list_coloring':"PARTIAL — the floor bound holds in special cases (Albertson–Grossman–Haas and successors); the general inequality is open. Node states the general conjecture.",
 'cycles_in_graphs_of_large_chromatic_number':"PARTIAL — several special cases (specific cycle-length sets, girth conditions) proven; the general statement is open.",
 'monochromatoc_reachability_in_arc_colored_digraphs':"PARTIAL — known for few colours / tournament sub-cases; general open. Already formalized in digraph-theory (mono_reach_or_rainbow_statement) as the open general proposition.",
 'hoand_reed_conjecture':"PARTIAL — proven for k ≤ 3; general k open. Already formalized in digraph-theory (hoang_reed_statement).",
 'erdos_posa_property_for_long_directed_cycles':"PARTIAL — the (unrestricted) directed Erdős–Pósa property is known (Reed–Robertson–Seymour–Thomas); the LONG-directed-cycle variant is open. Already formalized (erdos_posa_long_dicycles_statement).",
 'jones_conjecture':"PARTIAL — proven for planar graphs (Jones); the general bound is open. (Planarity → gate G2 for the planar case.)",
 'stable_set_meeting_all_longest_directed_paths':"PARTIAL — proven for special digraph classes; general open. Already formalized (stable_meeting_longest_dipaths_statement).",
 'vertex_coloring_of_graph_fractional_powers':"PARTIAL — special cases (specific power/fraction regimes) proven; general open.",
 'crossing_sequences':"PARTIAL — partial characterization of realizable crossing sequences; full characterization open. DEFERRED (crossing/geometry, D3).",
 'circular_flow_number_of_regular_class_1_graphs':"PARTIAL — known for some regularities r; general open. DEFERRED (flows, D1).",
 'hamiltonian_cycles_in_powers_of_infinite_graphs':"PARTIAL — the finite analogue (Fleischner: square of a 2-connected graph is Hamiltonian) is a theorem; the infinite case is partial/open. DEFERRED (infinite, D4).",
 'strong_colorability':"PARTIAL — strong chromatic number bounds (e.g. ≤ 3Δ−1) are known; the conjectured 2Δ is open.",
}

# per-row field overrides (precise proposition selection / encoding)
OVERRIDE = {
 'adams_conjecture': {
   'status_semantics':"OPEN as encoded. The original (general digraph) conjecture is DISPROVED for multidigraphs (Grünbaum); the TOURNAMENT case is open (OPG discussion). This node SELECTS and encodes the open tournament proposition; the disproved multidigraph variant is recorded separately as a proved ~ theorem, never as a global negation.",
   'rocq_idiom':"forall T:tournament, (exists c:seq T, dicycle c) -> exists a:T*T, arc a /\\ num_dicycles (reverse_arc T a) < num_dicycles T",
   'selected_proposition':'tournament case (open)',
 },
}
# phase re-routes for previously-flagged deferred rows (resolve the routing flags)
PHASE_OVERRIDE = {
 '3_colourability_of_arrangements_of_great_circles':'D3',   # arrangement/geometry
 'counting_3_colorings_of_the_hex_lattice':'D4',            # infinite lattice entropy
}

# ── phase routing (tier-respecting; counts reconcile by construction) ──────────
DIRECTED_KW = ['digraph','dicycle','dipath','tournament','outdegree','out-degree','feedback-arc',
 'second-neighbourhood','disjoint-dicycles','arc-disjoint','branching','dichromatic','oriented-colouring',
 'monochromatic-reachability','directed-cycle','acyclic-subdigraph','erdos-posa-directed','girth-outdegree',
 'subgraph-containment-digraph','digraph-','edge-colored-tournament','tournament-','spanning-structure']
CORE_PHASES = OrderedDict([
 ('U2', ['hamilton']),
 ('U3', ['homomorphism','graph-product-coloring','graph-product','graph-power','endomorphism','longest-path','longest-cycle','core']),
 ('U4', ['list-colour','list-colouring','list-coloring','choosability','choice']),
 ('U5', ['edge-colour','edge-coloring','total-colour','total-coloring']),
 ('U8', ['chi-bounded','chi-boundedness']),
 ('U7', ['minor','immersion']),
 ('U11',['reconstruction']),
 ('U12',['hypergraph','set-systems','turan-hypergraph']),
 ('U6', ['cycle-double-cover','cycle-cover','cycle-decomposition','edge-decomposition','path-decomposition','cubic-2-factor','eulerian']),
 ('U10',['snark','perfect-matching','matchings-and-snarks','cubic-snark','petersen']),
 ('U9', ['packing','covering','triangle-packing','transversal','connectivity','edge-connectivity','edge-disjoint-trees','vertex-partition','saturation','t-join','disjoint-cycles','matching-cut','matching-extension','path-partition','odd-cycle-transversal','degree-partition']),
 ('U1', ['chromatic-bound','chromatic-number','chromatic-critic','chromatic-exist','chi-equals-omega','valency','double-critical','chi-cycles','girth-chromatic']),
 ('U13',['planar','domination','graph-labeling','degree-sequence','pebbling','combinatorial-games','network-routing','layered-network','book-embedding','degeneracy-coloring','weighted-colouring','average-degree-girth','cages-moore','graph-power-colouring','immersion-coloring','clique-colouring','chromatic-number-misc','degenerate']),
])
DEFER_PHASES = OrderedDict([
 ('D1', ['flow','tension','nowhere-zero']),
 ('D3', ['crossing','geometry','point-set','obstacle','drawing','incidence-poset']),
 ('D6', ['surface','genus','embedding','non-orientable','curvature']),
 ('D7', ['complexity','algorithm','approximation','running-time']),
 ('D5', ['spectr','strongly-regular','eigen','energy','laplacian','adjacency','symmetric-function','algebraic']),
 ('D4', ['infinite','ends','arc-transitive','unfriendly','aleph','ray']),
 ('D2', ['density','asymptotic','turan','random','sidorenko','ramsey','erdos-hajnal','growth','spectrum','expander','probabil']),
])
PHASE_REPO = {
 'U1':'chromatic-theory','U4':'chromatic-theory','U5':'chromatic-theory','U8':'chromatic-theory',
 'U2':'hamiltonicity-theory','U3':'homomorphism-theory','U6':'cycle-theory','U10':'cycle-theory',
 'U7':'minor-theory','U9':'packing-theory','U11':'reconstruction-theory','U12':'hypergraph-theory',
 'U13':'topological-graph-theory','P9':'digraph-theory',
 'D1':'cycle-theory','D2':'extremal-graph-theory','D3':'topological-graph-theory',
 'D4':'infinite-graph-theory','D5':'spectral-graph-theory','D6':'topological-graph-theory','D7':'graph-theory-misc',
}

def route(c):
    cl=(c.get('cluster') or '').lower(); topic=c.get('topic') or ''
    if c['core_or_deferred']=='core':
        if c.get('is_directed') or any(k in cl for k in DIRECTED_KW): return 'P9','directed'
        for ph,kws in CORE_PHASES.items():
            if any(k in cl for k in kws): return ph,'cluster'
        fb={'Coloring':'U1','Basic Graph Theory':'U9','Graph Theory':'U9','Topological Graph Theory':'U13',
            'Algebraic Graph Theory':'U2','Extremal Graph Theory':'U9','Hypergraphs':'U12'}.get(topic,'U13')
        return fb,'topic-fallback'
    f=c.get('formalizability')
    for ph,kws in DEFER_PHASES.items():
        if any(k in cl for k in kws): return ph,'cluster'
    if f=='needs-flow': return 'D1','formalizability'
    if f=='infinite' or topic=='Infinite Graphs': return 'D4','formalizability'
    if f=='needs-computation-model': return 'D7','formalizability'
    if f=='needs-planarity': return 'D6','formalizability'
    if topic=='Algebraic Graph Theory': return 'D5','formalizability'
    return 'D2','formalizability'

NUM={'0':'zero','2':'two','3':'three','4':'four','5':'five','6':'six','7':'seven','57':'fiftyseven'}
def formal_name(slug):
    parts=slug.lower().split('_')
    if parts and parts[0].isdigit(): parts[0]=NUM.get(parts[0],'n'+parts[0])
    s=re.sub(r'[^a-z0-9]+','_','_'.join(parts)).strip('_')
    s=re.sub(r'_(conjecture|problem|graph_theoretic_form)$','',s)   # keep trailing _0 disambiguators
    name=s[:52].strip('_')+'_statement'
    return ('n'+name) if name[0].isdigit() else name

rows=[]; used=set()
for c in cls:
    slug=c['slug']; p=prob.get(slug,{}); ph,basis=route(c)
    if slug in PHASE_OVERRIDE: ph,basis=PHASE_OVERRIDE[slug],'override'
    repo=PHASE_REPO[ph]
    if ph=='U13':
        cl=(c.get('cluster') or '').lower()
        repo=('topological-graph-theory' if 'planar' in cl else
              'packing-theory' if 'domination' in cl else 'graph-theory-misc')
    done=slug in ALREADY
    fn=ALREADY.get(slug) or formal_name(slug)
    if not done:                                   # global uniqueness guard for derived names
        base=fn; i=2
        while fn in used: fn=base[:-len('_statement')]+f'_{i}_statement'; i+=1
    used.add(fn)
    props=[{'kind':s.get('kind'),'text':re.sub(r'\s+',' ',(s.get('text') or s.get('html','') or '')).strip()[:600]}
           for s in p.get('statements',[])]
    if not props:                                  # fallback so no row is empty
        props=[{'kind':'Statement','text':(p.get('statement_text') or c['title']).strip()[:600]}]
    ov=OVERRIDE.get(slug,{})
    sem=ov.get('status_semantics') or STATUS_SEM.get(slug) or ('' if c.get('status','open')=='open' else 'see source_propositions')
    rows.append(OrderedDict([
        ('slug',slug),('title',c['title']),('node_id',p.get('node_id')),
        ('canonical_url',p.get('canonical_url')),
        ('source_commit_repo',SRC_COMMIT_REPO),('source_commit_problems_json',SRC_COMMIT_PROBLEMS),
        ('source_text',(p.get('statement_text') or '').strip()),
        ('source_propositions',props),
        ('selected_proposition',ov.get('selected_proposition','primary OPG statement')),
        ('status',c.get('status','open')),('status_semantics',sem),
        ('topic',c.get('topic')),('stars',c.get('stars')),
        ('formalizability',c.get('formalizability')),('tier',c['core_or_deferred']),
        ('requires_planarity',c.get('formalizability')=='needs-planarity'),  # ROW-LEVEL G2 gate
        ('defer_reason',c.get('defer_reason','')),
        ('phase',ph),('repo',repo),('formal_name',fn),('phase_basis',basis),
        ('cluster_raw',c.get('cluster')),
        ('reuses',c.get('reuses',[])),('new_primitives',c.get('new_primitives',[])),
        ('rocq_idiom',ov.get('rocq_idiom') or c.get('rocq_idiom','')),
        ('legs',OrderedDict([('statement','done' if done else 'todo'),('grounding','done' if done else 'todo'),
                             ('edges','partial' if done else 'todo'),('correspondence','done' if done else 'todo'),
                             ('audit_page','todo')])),
        ('already_formalized',done),
    ]))

# ── validation: HARD ASSERTS for every invariant the plan claims this builder gates ────────────
names=[r['formal_name'] for r in rows]
core=[r for r in rows if r['tier']=='core']; defr=[r for r in rows if r['tier']=='deferred']
def need(cond, msg):
    if not cond: raise AssertionError("MANIFEST INVARIANT VIOLATED: "+msg)
need(len(rows)==227, f"row count {len(rows)} != 227")
need(len(set(r['slug'] for r in rows))==227, "duplicate slugs")
bad_id=[n for n in names if not re.match(r'^[A-Za-z_][A-Za-z0-9_]*$',n)]
need(not bad_id, f"invalid Rocq identifiers: {bad_id[:5]}")
dups=[n for n,k in Counter(names).items() if k>1]
need(not dups, f"duplicate formal_names: {dups[:5]}")
empty=[r['slug'] for r in rows if not r['source_propositions']]
need(not empty, f"empty source_propositions: {empty}")
placeholder=[r['slug'] for r in rows if r['status']!='open' and (not r['status_semantics'] or 'record the exact' in r['status_semantics'] or r['status_semantics']=='see source_propositions')]
need(not placeholder, f"non-open rows w/o exact status_semantics: {placeholder}")
need('tournament' in [r for r in rows if r['slug']=='adams_conjecture'][0]['rocq_idiom'], "Ádám not encoded over tournaments")
need(len(core)==142 and len(defr)==85, f"tier reconciliation core={len(core)} deferred={len(defr)} (want 142/85)")
need(all((r['phase'].startswith('D'))==(r['tier']=='deferred') for r in rows), "tier/phase mismatch (D-phase must be deferred)")
need(all(r['source_text'] for r in rows), "row missing source_text provenance")
need(all(r['phase'] and r['repo'] for r in rows), "row missing phase/repo")
print("ALL MANIFEST INVARIANTS PASS:",
      f"227 rows | {len(core)} core / {len(defr)} deferred | {len(set(names))} unique valid ids |",
      f"{sum(1 for r in rows if r['requires_planarity'])} requires_planarity ({sum(1 for r in core if r['requires_planarity'])} core) |",
      f"{sum(1 for r in rows if r['already_formalized'])} already-formalized")

# ── leg-state OVERLAY (meta/opg_legs_state.json): VALIDATE + MERGE (never regenerate away) ──
# The manifest's `legs` are a generated DEFAULT; the overlay is the source of truth for progress
# and is merged in here, so re-running the builder preserves landed leg state instead of resetting.
SLUGS = {r['slug'] for r in rows}
LEGS = ['statement', 'grounding', 'edges', 'correspondence', 'audit_page']
ALLOWED = {'todo', 'partial', 'done', 'blocked'}
legs_path = f"{META}/opg_legs_state.json"
if os.path.exists(legs_path):
    overlay = json.load(open(legs_path)).get('entries', {})
    for slug, e in overlay.items():
        need(slug in SLUGS, f"overlay slug not in manifest: {slug}")
        for lg in LEGS:
            st = e.get(lg, 'todo')
            need(st in ALLOWED, f"overlay {slug}.{lg} invalid state {st!r}")
            if lg in ('statement', 'grounding', 'edges') and st != 'todo':
                need(e.get('commit') and e.get('package'),
                     f"overlay {slug}: non-todo {lg}={st} needs commit+package provenance")
    for r in rows:                       # overlay wins; missing legs keep the generated default
        e = overlay.get(r['slug'])
        if e: r['legs'] = OrderedDict((lg, e.get(lg, r['legs'][lg])) for lg in LEGS)
    print(f"overlay: validated + merged {len(overlay)} leg-state entries from opg_legs_state.json")

out={"_README":"Validated 227-row corpus manifest (v2, 2026-06-26). Each row → exactly one phase+repo "
      "(tier-respecting → counts reconcile to 142 core / 85 deferred / 227). formal_name is a VALID, UNIQUE "
      "planned Rocq identifier (finalized at implementation). status_semantics gives the exact settled/open "
      "proposition for every non-open record. Provenance: graph-conjectures@"+SRC_COMMIT_REPO[:10]+
      ", data/problems.json@"+SRC_COMMIT_PROBLEMS[:10]+". phase_basis records how the phase was chosen.",
     "provenance":{"corpus":"openproblemgarden via graph-conjectures/data/problems.json",
                   "repo_commit":SRC_COMMIT_REPO,"problems_json_commit":SRC_COMMIT_PROBLEMS,"n":227},
     "totals":{"core":len(core),"deferred":len(defr),
               "core_by_phase":dict(Counter(r['phase'] for r in core)),
               "deferred_by_phase":dict(Counter(r['phase'] for r in defr)),
               "by_repo":dict(Counter(r['repo'] for r in rows)),
               "by_status":dict(Counter(r['status'] for r in rows)),
               "already_formalized":sum(1 for r in rows if r['already_formalized'])},
     "rows":rows}
json.dump(out,open(f"{META}/opg_corpus_manifest.json","w"),ensure_ascii=False,indent=1)
print("wrote meta/opg_corpus_manifest.json")

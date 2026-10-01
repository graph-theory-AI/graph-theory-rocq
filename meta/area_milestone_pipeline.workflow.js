/*
 * area-milestone-pipeline (v3, aligned to OPG_FULL_FORMALIZATION_PLAN.md v4 / 2026-06-26)
 * =======================================================================================
 * ⚠️ ARCHIVED / HISTORICAL (post release opg-v1.0-227-attempted).
 *   The statement-generation phase this pipeline drove is COMPLETE (227/227 attempted). It is
 *   kept as a historical record of how milestones were generated. If ever reused for a NEW
 *   area, note two post-release corrections: (a) the milestone-rows loader path is `meta/`
 *   (fixed below); (b) the ALGORITHMIC/COMPLEXITY guidance below is SUPERSEDED — its abstract
 *   decoupled cost model was found VACUOUS by the D7 audit (alg := exact answer, cost := 0);
 *   use the cost-coupled interpreter model in
 *   graph-theory-misc/theories/foundations/complexity.v instead.
 * =======================================================================================
 * THIS IS A WORKFLOW-TOOL SCRIPT, NOT A STANDALONE NODE MODULE.
 *   Run it ONLY via  Workflow({ scriptPath: ".../docs/area_milestone_pipeline.workflow.js",
 *                               args: {...} }).
 *   The Workflow runtime injects the globals `agent`, `phase`, `parallel`, `log`, `args`,
 *   `budget`, `workflow` and wraps this body in an async function, so top-level `await` and
 *   `return` are the documented format here — `node file.js` will (correctly) reject them.
 *   The JS sandbox has NO filesystem access, so it CANNOT read the manifest; the caller MUST
 *   pass canonical, pre-validated rows (see below).
 *
 * INVOKE (one milestone = one (phase, repo) cell of the validated manifest):
 *   1) python3 meta/milestone_rows.py <phase> <repo>        # deterministic filter+validate gate
 *   2) Workflow({ scriptPath: <this file>,
 *        args: { phase:"U1", repo:"chromatic-theory", base_ready:false, rows:<step-1 JSON> } })
 *   `rows` is REQUIRED (no agent-side manifest filtering — that was unreliable). `repo` is
 *   REQUIRED (phases like U13 span 3 repos; one repo per run). `base_ready` declares whether
 *   graph-theory-base (plan gate G3) exists yet.
 *
 * QA loop:  implement → (code-review team ∥ mathematician faithfulness-audit team)
 *           → Rocq-expert correct+ground → implications/refutations → deterministic landing pack.
 */
export const meta = {
  name: 'area-milestone-pipeline',
  description: 'Drive ONE (phase,repo) milestone of the OPG plan (v4): implement statements, code-review + mathematician faithfulness-audit teams, Rocq-expert correct+ground, implications/refutations. Manifest-driven; rows supplied by scripts/milestone_rows.py.',
  phases: [
    { title: 'Implement', detail: 'draft the (phase,repo) Rocq from the supplied rows: area primitives + axiom-free _statement nodes (formal_name; type per row.rocq_idiom)' },
    { title: 'Review+Audit', detail: 'code-review team ∥ mathematician faithfulness-audit team (vs verbatim source_text + selected_proposition)' },
    { title: 'Correct+Ground', detail: 'Rocq experts: compile (rocq-mcp) + grounding lemmas; honour the planarity G2 gate without axioms' },
    { title: 'Implications', detail: 'prove ONLY verified-literature edges; never the refuted ones; Qed is the gate' },
  ],
}

// ALL paths are RELATIVE to the graph-theory-rocq monorepo root (the session working directory).
// NEVER write to an absolute standalone path — the absorbed copy under digraph-theory/ is the source
// of truth, and every package (chromatic-theory/, …, digraph-theory/) lives under the monorepo root.
const REPO = 'digraph-theory'   // the absorbed DIRECTED library (monorepo-relative)
const PLAN = 'meta/OPG_FULL_FORMALIZATION_PLAN.md'
const NS = { 'chromatic-theory': 'Chromatic', 'hamiltonicity-theory': 'Hamilton', 'homomorphism-theory': 'Hom',
  'cycle-theory': 'Cycle', 'minor-theory': 'Minor', 'packing-theory': 'Packing', 'reconstruction-theory': 'Reconstruction',
  'hypergraph-theory': 'Hypergraph', 'topological-graph-theory': 'Topological', 'graph-theory-misc': 'GTMisc',
  'digraph-theory': 'Digraph', 'extremal-graph-theory': 'Extremal', 'infinite-graph-theory': 'Infinite', 'spectral-graph-theory': 'Spectral' }

// ── preflight: REQUIRE phase + repo + canonical rows; record the external gate states ──
// Gates (plan §7): GLOBAL before any landing — g0 (monorepo+package exists), g1 (dep-graph gate),
// base_ready (=G3-core). ROW-LEVEL before a planar row — g2 (fourcolor installed). The driver is a
// pre-G0 dry-run QA harness when these are false; it never claims ready_to_land without them.
// <<MILESTONE-SPEC-START>>  (meta/make_milestone_workflow.py replaces this block with an
// embedded literal M — rows + gate flags inlined — because runtime `args` is NOT reliably
// delivered in this harness. Do not run this template directly; generate a wrapper instead.)
const M = { phase: args && args.phase, repo: args && args.repo, rows: args && args.rows,
  base_ready: !!(args && args.base_ready), g0_ready: !!(args && args.g0_ready),
  g1_ready: !!(args && args.g1_ready), g2_ready: !!(args && args.g2_ready) }
if (!M.phase || !M.repo || !Array.isArray(M.rows) || M.rows.length === 0) {
  return { error: 'PREFLIGHT FAILED: this is the TEMPLATE — run a generated wrapper from ' +
    '`python3 meta/make_milestone_workflow.py <phase> <package>` (runtime args are not delivered here).' }
}
// <<MILESTONE-SPEC-END>>
if (!NS[M.repo]) return { error: `Unknown repo "${M.repo}" — not one of the federation packages.` }
const rows = M.rows
// PLANARITY IS ROW-LEVEL (manifest requires_planarity), NOT repo/phase-level: needs-planarity rows
// occur across P9/U2/U3/U4/U7/U9/U13. Each such row is G2-blocked until g2_ready, independent of phase.
const planarSlugs = new Set(rows.filter((r) => r.requires_planarity).map((r) => r.slug))
const hasPlanar = planarSlugs.size > 0 && !M.g2_ready

// MCP tools are env-named mcp__rocq-mcp__* or mcp__rocq_mcp__*; agents find them by KEYWORD search.
const MCP = `To run Rocq: call ToolSearch with the keyword query "rocq coq compile query proof check" (NOT a fixed ` +
  `select: — the server is registered as rocq-mcp / rocq_mcp depending on environment; keyword search resolves either), ` +
  `then use the returned rocq_compile / rocq_query / rocq_start / rocq_check tools.`

const BASE = M.base_ready
  ? `graph-theory-base is INSTALLED (G3-core). Use \`From GTBase Require Import base.\` as the top import ` +
    `(base re-exports all_boot + the coq-graph-theory undirected vocabulary). base provides cross-area ` +
    `primitives — currently Delta (Δ), ceil_div, common_nbr, regular, girth_geq; is_hom, homs_to, is_core, ` +
    `cartesian_product (□), tensor_product (×); graph_power, subdivision, frac_power; list_colourable, ` +
    `list_colourable_on, choosable, is_choice_number; the [mgraph] notation + line_graph, total_graph, ` +
    `chromatic_index (χ'), total_chromatic_number (χ''), edge_colourable, total_colourable. BEFORE defining ` +
    `ANY cross-area primitive, CHECK base first via rocq_query (Search/Print/Locate over GTBase.base) and ` +
    `REUSE base's version verbatim — never redefine (e.g. edge/total colouring MUST use base's ` +
    `line_graph/total_graph/χ'/χ''; products/homs/cores/list-χ come from base). Only a genuinely NEW ` +
    `cross-area primitive is defined locally + tagged [@MOVE-to-base] (it migrates to base when a 2nd area ` +
    `needs it). IMPORT-ORDER WARNING: if this milestone needs coq-graph-theory's multigraph API (edge, ` +
    `source, target, incident, edges_at — i.e. a \`From GraphTheory Require Import mgraph.\`), put that ` +
    `import BEFORE the base import, because coq-graph-theory's mgraph defines a DIRECTED line_graph that ` +
    `would otherwise shadow base's undirected one. rocq_compile finds GTBase in the switch's user-contrib; ` +
    `the package _CoqProject also has -Q ../base/theories GTBase.`
  : (M.repo === 'digraph-theory'
    ? `DIRECTED REPO (digraph-theory, the absorbed self-contained directed library — NOT a GTBase consumer). ` +
      `This is a DIRECTED phase: the carrier is coq-graph-theory's diGraph (a -> b arcs), NOT the undirected sgraph. ` +
      `ALL paths are under the MONOREPO copy ${M.repo}/ (the absorbed subtree) — NEVER any standalone repo. ` +
      `FIRST explore + REUSE the existing API — ${M.repo}/theories/core/{digraph,tournament,oriented,dipath,order}, ` +
      `${M.repo}/theories/invariants/{strong,domination,critical}, ${M.repo}/theories/constructions/{...}. The repo ` +
      `ALREADY commits ~12 directed conjecture _statement constants (${M.repo}/theories/conjectures/{classic_core,packing,` +
      `sad,long_dipath,colouring_variants,implications,implications2}.v) — you add ONLY the NEW rows in M.rows; do ` +
      `NOT restate, redefine, or shadow any existing constant (rocq_query/Search first). Write the new statements to ` +
      `${M.repo}/theories/conjectures/${M.phase}.v (with -R theories Digraph) — the file paths below are authoritative. ` +
      `Do NOT import GTBase (undirected).`
    : `PRE-G3 MODE: graph-theory-base does NOT exist yet. Import the CORE primitives DIRECTLY from coq-graph-theory / ` +
    `digraph-theory in this file's preamble, and add a comment marking any cross-area def that will MOVE to ` +
    `graph-theory-base once G3 lands. Do NOT claim base reuse.`)

const API = `
TOOLCHAIN: opam switch 'digraph' (Rocq 9.1.1 + coq-graph-theory). ${MCP}
rocq_compile takes a full .v source string; GraphTheory resolves from the switch. Prefer rocq_start+rocq_check for
warm iteration; rocq_compile for the final green + Print Assumptions.

CORE undirected API (verified to load): \`From mathcomp Require Import all_boot. From GraphTheory Require Import digraph sgraph coloring.\`
G : sgraph (simple graphs); x -- y adjacency; degree of x = #|N(x)|; Δ = \\max_(x in G) #|N(x)|; ω is subset-relative
ω(A) for A:{set G} (whole-graph ω([set: G])); α independence; the chromatic number is in coloring.v (discover its exact
name via rocq_query). CORE minor/treewidth available (core/minor.vo). PLANARITY is NOT installed (needs
coq-graph-theory-planar + coq-fourcolor — plan gate G2). Directed rows use digraph-theory (diGraphType / orientedDigraph
/ tournament). ${BASE}

CARRIER TYPE — DO NOT impose \`forall G : sgraph\`. Choose each node's domain from the row's \`rocq_idiom\` and
\`selected_proposition\`: sgraph (undirected); diGraphType / orientedDigraph / tournament (directed P9); a finite
incidence/hyperedge type (hypergraphs); products/pairs/sequences as the statement needs.
Each node: \`Definition <formal_name> : Prop := …\`. AXIOM-FREE — no top-level Conjecture/Axiom/Parameter/Admitted in
statement files. Add non-triviality guards. Idiom refs: ${REPO}/theories/conjectures/classic_core.v, .../foundations/interop_graph_theory.v`

const STATUS_RULES = `STATUS DISCIPLINE (plan §3): name each constant exactly row.formal_name. State the EXACT
selected proposition (row.selected_proposition / row.status_semantics), anchored to the verbatim row.source_text. A
conjecture refuted in one class but open in another is stated as the OPEN proposition (Ádám → over tournaments, NOT
arbitrary digraphs). solved/disproved rows are STILL Definition _statement (statement-only); proofs/refutations are
optional applications/ work, out of scope here.`

const PLANAR_RULE = hasPlanar ? `
PLANARITY G2-GATE — applies ROW-BY-ROW to exactly these slugs (manifest requires_planarity=true), and ONLY these
(the rest of this milestone compiles normally): ${[...planarSlugs].join(', ')}.
-planar/fourcolor is NOT installed. For each such row, represent planarity as a Section \`Variable\` / a discharged
hypothesis INTO the statement (\`Definition … := forall (is_planar : sgraph -> Prop) …\`), NEVER a top-level
\`Parameter\`/\`Axiom\` (that contaminates Print Assumptions). Mark those rows compile_blocked; do NOT claim axiom-free
green for them — "blocked" is the honest leg state, not "done". Non-planar rows in this milestone are unaffected.` : ''

// ── PHASE 1: IMPLEMENT ──────────────────────────────────────────────────────
phase('Implement')
const IMPL_SCHEMA = { type: 'object', properties: {
  source: { type: 'string', description: `full theories/conjectures/${M.phase}.v content` },
  per_statement: { type: 'array', items: { type: 'object', properties: {
    slug: { type: 'string' }, formal_name: { type: 'string' }, carrier_type: { type: 'string' } }, required: ['slug', 'formal_name'] } },
  new_primitives: { type: 'array', items: { type: 'object', properties: {
    name: { type: 'string' }, definition: { type: 'string' }, area_specific: { type: 'boolean' } }, required: ['name'] } },
  api_findings: { type: 'string' }, compiles: { type: 'boolean' }, compile_blocked_reason: { type: 'string' }, notes: { type: 'string' } },
  required: ['source', 'per_statement', 'new_primitives'] }
// Spectral design spec (D5 / spectral-graph-theory) — preflighted carrier + matrix policy.
const SPECTRAL = M.repo === 'spectral-graph-theory'
  ? `\nSPECTRAL DESIGN (settled in preflight — follow it):\n` +
    `• TOOLCHAIN: algC / mathcomp.field are NOT installed. Do NOT import mathcomp.field; use ONLY ` +
    `\`From mathcomp Require Import all_algebra.\`. IMPORT ORDER (load-bearing for int/rat canonical ` +
    `structures): \`From mathcomp Require Import all_boot.\` → \`From GraphTheory Require Import sgraph.\` ` +
    `→ \`From GTBase Require Import base.\` → \`From mathcomp Require Import all_algebra.\`, then ` +
    `\`Local Open Scope ring_scope. Import GRing.Theory Num.Theory.\`\n` +
    `• CARRIER: (a) for COSPECTRALITY / 'determined by spectrum', use char_poly EQUALITY over int — no ` +
    `field, no roots: \`cospectral G H := char_poly (adjmx int G) = char_poly (adjmx int H)\`; ` +
    `'determined by spectrum' := \`forall H, cospectral G H -> inhabited (G ≃ H)\` (ISO via diso, NOT ` +
    `equality). (b) for rows about EIGENVALUE MAGNITUDE / ORDERING / SPECTRAL RADIUS (signing bound, ` +
    `Laplacian degrees), quantify over an ABSTRACT \`(R : rcfType)\` (real-closed field — the real ` +
    `symmetric adjacency/Laplacian eigenvalues live in any rcf; gives order, |·|, and Num.sqrt for the ` +
    `2*sqrt(d-1) bound). NO concrete algC needed for statement-only.\n` +
    `• MATRIX: define in spectral-graph-theory/theories/foundations/spectral.v (area-local, NOT base): ` +
    `\`adjmx (R:ringType)(G:sgraph) : 'M[R]_(#|G|) := \\matrix_(i,j) (if enum_val i -- enum_val j then 1 else 0)\`; ` +
    `Laplacian \`L = D - A\` (D = degree diagonal); char_poly; cospectral; determined_by_spectrum; ` +
    `\`spectral_radius_le A b := forall x, eigenvalue A x -> |x| <= b\` (over rcfType).\n` +
    `• SPECTRUM IS A MULTISET (counted with multiplicity), never a set. 'largest eigenvalue' = spectral radius.\n` +
    `• NON-SPECTRAL rows: triangle_free_strongly_regular → reuse a combinatorial strongly_regular (int, ` +
    `no matrices); symmetric_chromatic_function (distinguishing trees) → Stanley's SYMMETRIC CHROMATIC ` +
    `function (a combinatorial generating function over proper colourings, NOT eigenvalues); 'distinguish' ` +
    `:= exists non-iso trees with equal function.\n` +
    `• Keep base/ UNTOUCHED (new area; no other package consumes spectral vocab).`
  : ''
// Crossing-number design (D3cr / topological-graph-theory) — preflighted: faithful combinatorial cr.
const CROSSING = M.phase === 'D3cr'
  ? `\nCROSSING-NUMBER DESIGN (settled in preflight — follow it; FAITHFUL or PARTIAL, never a placeholder):\n` +
    `• Define a SINGLE faithful combinatorial \`crossing_number : sgraph -> nat\` in ` +
    `topological-graph-theory/theories/foundations/crossing.v, via PLANARIZATION onto base's ` +
    `\`wagner_planar\` (no geometry/drawings): cr(G) ≤ k IFF G admits a "k-crossing planarization" — a ` +
    `graph obtained by inserting k degree-4 crossing-vertices, each splitting a pair of independent ` +
    `edges of G — that is \`wagner_planar\`; \`crossing_number G\` is the LEAST such k (a min over a ` +
    `finite/decidable predicate). This is the standard planarization characterisation, hence faithful.\n` +
    `• MANDATORY non-vacuity grounding (a fake/trivial cr must FAIL these): \`crossing_number G = 0 <-> ` +
    `wagner_planar G\` (both directions), \`crossing_number\` monotone under sub-relation, and a concrete ` +
    `\`crossing_number 'K_5 != 0\` (K_5 is not wagner_planar ⇒ cr ≥ 1). If you CANNOT make crossing_number ` +
    `faithfully capture "min crossings" + prove these, DO NOT ship a placeholder — mark that row PARTIAL ` +
    `with an honest note on what's missing.\n` +
    `• Use it: cr('K_n) = Guy formula (statement-only Prop); cr(KB m n) = Zarankiewicz formula; ` +
    `χ(G)≥t → cr(G) ≥ cr('K_t) (relational); lim cr(Q_d)/4^d = 5/32 via the ε–N/eventual-bound idiom ` +
    `(Q_d = hypercube = iterated cartesian_product of K_2, reuse base \`cartesian_product\`).\n` +
    `• crossing_number is AREA-LOCAL (topological foundations), NOT base. Add an audit note that it is the ` +
    `planarization invariant. Do NOT introduce drawings/surfaces/faces/genus/point-sets.`
  : ''
// Embedding design (Wave 1 / D6emb) — the combinatorial embedding foundation is DONE; use it.
const EMBEDDING = M.phase === 'D6emb'
  ? `\nEMBEDDING DESIGN (the Track-A foundation is COMPLETE and axiom-free — USE it, do NOT rebuild):\n` +
    `• Import \`From Topological.foundations Require Import embedding.\` It provides (all take the graph ` +
    `\`(G:sgraph)\` explicitly, and an embedding \`(E : embedding G)\`): \`dart G\` (oriented edges), ` +
    `\`edge_perm G : {perm (dart G)}\` (edge involution), \`embedding G\` (Record: an orientable ` +
    `rotation system), \`face_perm E\`/\`face_of E d\`/\`face_size E d\` (faces = orbits of face_perm), ` +
    `\`planar_embedding E\` (genus 0), \`embeds_in_genus g\`, \`min_genus g\`, \`toroidal G\` (genus ≤ 1), ` +
    `\`triangulation E\` (every face_size = 3), \`combinatorial_curvature E v : rat\`, ` +
    `\`positive_curvature E\`, and crucially \`embedding_exists : inhabited (embedding G)\` (NON-VACUITY — ` +
    `every graph has an embedding, so these predicates are inhabited). base has \`k_connected\`, ` +
    `\`cartesian_product\` (□), \`cycle_graph\`, \`'K_n\`, \`N(v)\`, \`edge_colourable\`/\`chromatic_index\`.\n` +
    `• ENCODINGS (faithful; the foundation makes them non-vacuous):\n` +
    `  - grunbaums_conjecture: \`forall G (E:embedding G), triangulation E -> exists c : dart G -> 'I_3, ` +
    `(forall d, c d = c (edge_perm G d)) /\\ (forall d, the three edge-colours c d, c(face_perm E d), ` +
    `c(face_perm E (face_perm E d)) are PAIRWISE DISTINCT)\` — a proper 3-edge-colouring of the ` +
    `(3-regular) dual = the 3 edges bounding each triangular face get 3 distinct colours. (G:sgraph is ` +
    `simple+loopless; the rotation system is orientable by construction.)\n` +
    `  - the_circular_embedding_conjecture: \`forall G, k_connected G 2 -> exists E : embedding G, ` +
    `forall d, {in face_of E d &, injective (fun d' : dart G => (sval d').1)}\` — each face boundary is a ` +
    `CYCLE = no vertex repeats on the face (source map injective on each face's darts).\n` +
    `  - what_is_the_largest_graph_of_positive_curvature: \`exists N, forall G (E:embedding G), ` +
    `connected [set:G] -> planar_embedding E -> (forall v, 2 < #|N(v)|) -> positive_curvature E -> ` +
    `~ is_prism G -> ~ is_antiprism G -> #|G| <= N\`. Define \`is_prism G := exists n, 2<n /\\ ` +
    `inhabited (G ≃ cartesian_product (cycle_graph n) 'K_2)\` and a concrete \`antiprism\` sgraph on ` +
    `\`'I_n * bool\` (two n-cycles + connecting triangles: top i ~ bottom i and top i ~ bottom (i+1)), ` +
    `\`is_antiprism G := exists n, 2<n /\\ inhabited (G ≃ antiprism n)\`.\n` +
    `• AREA-LOCAL to topological-graph-theory/theories/conjectures/${M.phase}.v; only new primitives are ` +
    `is_prism/is_antiprism (+ antiprism). Everything AXIOM-FREE. No metric geometry.`
  : ''
// Infinite-graph design (D4 / infinite-graph-theory) — preflighted carrier (NOT sgraph; it is finite).
const INFINITE = M.repo === 'infinite-graph-theory'
  ? `\nINFINITE-GRAPH DESIGN (settled in preflight — follow it; FAITHFUL or PARTIAL, never a placeholder):\n` +
    `• DO NOT force infinite rows through \`sgraph\` (it is a finite finType — structurally UNFAITHFUL for ` +
    `infinite graphs). Define the carrier in infinite-graph-theory/theories/foundations/igraph.v:\n` +
    `  \`Definition irel_sym {V} (e:V->V->Prop) := forall x y, e x y -> e y x.\` ` +
    `\`Definition irel_irr {V} (e:V->V->Prop) := forall x, ~ e x x.\` ` +
    `\`Record iGraph := { iV : Type; iedge : iV -> iV -> Prop; iedge_sym : irel_sym iedge; ` +
    `iedge_irr : irel_irr iedge }.\` plus an accessor \`Definition iadj (G:iGraph)(x y:iV G):Prop := @iedge G x y.\`\n` +
    `• Predicates are PROP-LEVEL (mathcomp bool \`\\in\`/\`path\` need eqType/finType, UNAVAILABLE for an ` +
    `arbitrary iV): \`countable_graph G := exists f:iV G->nat, injective f\`; \`ray G r := injective r /\\ ` +
    `forall n, iadj (r n) (r n.+1)\`; \`locally_finite G := forall v, exists n (f:'I_n->iV G), forall w, ` +
    `iadj v w -> exists i, f i = w\`; connectivity via an INDEXED walk \`f:'I_k.+1->iV G\` (not bool path); ` +
    `colourings/partitions as functions \`iV G -> 'I_k\` / \`-> bool\` with a Prop constraint.\n` +
    `• THE 2 DOABLE ROWS: (1) counting_3_colorings_of_the_hex_lattice is a THERMODYNAMIC LIMIT over ` +
    `*finite* hexagonal tori — use a FINITE \`sgraph\` torus + count proper 3-colourings (\`{ffun _ -> 'I_3}\`) ` +
    `+ the ε–N/eventual-bound idiom for lim (count)^(1/|V|); it does NOT need iGraph. (2) ` +
    `exact_colorings_of_graphs is over K_ω = the COUNTABLE complete graph (\`iV:=nat\`, \`iedge x y := x<>y\`); ` +
    `state the exact-colouring counting predicate faithfully, or mark the row PARTIAL if it can't be.\n` +
    `• Keep ALL infinite vocabulary in foundations/, NEVER base. No cardinals beyond ℵ₀ (no ℵ₁), no ends/` +
    `compactification, no ℝ² geometry — those rows are out of scope here.`
  : ''
const draft = await agent(
  `You are a Rocq/MathComp engineer building milestone ${M.phase} of '${M.repo}' (namespace ${NS[M.repo]}), plan v4.\n` +
  `Milestone rows (canonical, pre-validated — use EXACTLY these formal_names and source_texts):\n${JSON.stringify(rows)}\n\n` +
  `Draft theories/conjectures/${M.phase}.v: for EACH row a \`Definition <formal_name> : Prop\`, carrier type chosen ` +
  `per row.rocq_idiom (NOT a blanket sgraph). Introduce only minimal AREA-SPECIFIC new primitives.\n${API}\n${STATUS_RULES}${PLANAR_RULE}\n` +
  `ALGORITHMIC/COMPLEXITY rows (decides / runs-in-time / approximation_ratio / PTAS / NP-hard): SUPERSEDED — ` +
  `the abstract decoupled cost model was VACUOUS (D7 audit: alg := exact-answer, cost := 0). Couple cost to ` +
  `the object that produces the output: reuse the fixed-language interpreter model in ` +
  `graph-theory-misc/theories/foundations/complexity.v (one 'eval' computes BOTH output and step count), so a ` +
  `positive existential-algorithm claim cannot be satisfied by a zero-cost oracle. A SOLVED row is still a \`Definition _statement : Prop\` ` +
  `(proofs are optional applications work). If ≥2 rows share such vocabulary, put it in a single ` +
  `${M.repo}/theories/foundations/<topic>.v module (area-local), not base.\n` +
  `${SPECTRAL}${CROSSING}${EMBEDDING}${INFINITE}\n` +
  `ASYMPTOTIC/EXTREMAL rows (lim / o / O / Ω / Θ / whp / 'almost all'): use an EVENTUAL-BOUND, ε–N ` +
  `formulation over ℕ (e.g. \`forall m, exists N, forall n, N<=n -> <bound>\`; ratios cross-multiplied), ` +
  `NEVER an informal 'o'/'O' token. Rows needing PROBABILITY SPACES, GRAPH LIMITS/graphons, hom-DENSITY, ` +
  `or analytic-density machinery you are NOT building: mark the row PARTIAL — state the cleanest faithful ` +
  `approximation (or the finite/eventual core) and note what's missing; do NOT fake it with a vacuous ` +
  `abstract predicate. Shared area vocabulary used by ≥2 rows → a ${M.repo}/theories/foundations/<topic>.v ` +
  `module (area-local), not base.\n` +
  `Discover exact graph-theory names via rocq_query, then iterate with rocq_compile until the non-planar rows type-check (statements only).\n` +
  `Return the source, per_statement (slug↔formal_name↔carrier_type), the new primitives (flag area_specific), API findings, compile status.`,
  { label: `implement:${M.phase}`, phase: 'Implement', schema: IMPL_SCHEMA, effort: 'high' })
if (!draft) return { error: 'implement step failed' }
log(`Implemented ${rows.length} statements for ${M.phase}/${M.repo}; compiles=${draft.compiles}${planarSlugs.size ? ` (${planarSlugs.size} planar row(s)${hasPlanar ? ', G2-blocked' : ', g2 ready'})` : ''}`)

// ── PHASE 2: REVIEW (team) ∥ AUDIT (mathematician team) ─────────────────────
phase('Review+Audit')
const REVIEW_SCHEMA = { type: 'object', properties: { concern: { type: 'string' },
  findings: { type: 'array', items: { type: 'object', properties: {
    severity: { type: 'string', enum: ['blocker', 'major', 'minor', 'nit'] }, where: { type: 'string' }, issue: { type: 'string' }, fix: { type: 'string' } },
    required: ['severity', 'issue'] } }, overall: { type: 'string' } }, required: ['findings'] }
const AUDIT_SCHEMA = { type: 'object', properties: { slug: { type: 'string' }, formal_name: { type: 'string' },
  faithful: { type: 'boolean' }, selected_proposition_matches: { type: 'boolean' },
  confidence: { type: 'string', enum: ['high', 'medium', 'low'] }, issues: { type: 'array', items: { type: 'string' } },
  suggested_fix: { type: 'string' }, verdict: { type: 'string' } }, required: ['slug', 'faithful', 'selected_proposition_matches', 'issues'] }
const CONCERNS = ['rocq-idiom-naming-and-base-reuse', 'well-typedness-and-compile-risk', 'non-triviality-and-vacuity-guards']
const reviewerThunks = CONCERNS.map((c) => () =>
  agent(`Rocq code reviewer, concern '${c}'. Review milestone-${M.phase} file. For 'base-reuse' ${M.base_ready
    ? 'flag any cross-area primitive redefined instead of imported from graph-theory-base' : 'this is PRE-G3: verify core primitives are imported directly and cross-area defs are comment-marked for the future base move'}.` +
    ` Also flag any top-level Parameter/Axiom (must be none).\n\n\`\`\`coq\n${draft.source}\n\`\`\`\n\n${API}\nReport findings on your concern; you may rocq_compile.`,
    { label: `review:${c}`, phase: 'Review+Audit', schema: REVIEW_SCHEMA, effort: 'medium' }))
const auditorThunks = rows.map((r) => () =>
  agent(`Graph theorist auditing FAITHFULNESS of one node vs its VERBATIM source.\nformal_name: ${r.formal_name}\n` +
    `VERBATIM source_text: ${r.source_text}\nSelected proposition (must be the encoded one): ${r.selected_proposition || 'primary OPG statement'}\n` +
    `Status semantics: ${r.status_semantics || '(open)'}\nrocq_idiom hint: ${r.rocq_idiom || '(n/a)'}\n\n` +
    `Flag missing hypotheses, wrong quantifier/inequality direction, rounding, vacuity, mis-encoded primitives, and crucially ` +
    `whether the node encodes the SELECTED proposition's CLASS (set selected_proposition_matches=false if e.g. Ádám is over ` +
    `arbitrary digraphs instead of tournaments).\n` +
    (M.repo === 'spectral-graph-theory'
      ? `SPECTRAL AUDIT FLAGS (check explicitly): (1) is the spectrum a MULTISET / counted with ` +
        `multiplicity, not a set? (2) is 'determined by spectrum' graph ISOMORPHISM (diso), not matrix/` +
        `graph equality? (3) exact field/domain — char_poly over int for cospectrality, an rcfType for ` +
        `eigenvalue magnitude/ordering? (4) which spectrum — ADJACENCY vs LAPLACIAN vs signless — matches ` +
        `the source? (5) does 'largest eigenvalue' mean spectral radius (max |λ|)?\n`
      : '') +
    `\n\`\`\`coq\n${draft.source}\n\`\`\`\nReturn faithful, selected_proposition_matches, issues, suggested fix, verdict.`,
    { label: `audit:${r.slug}`, phase: 'Review+Audit', schema: AUDIT_SCHEMA, effort: 'high' }))
// Preserve positional slots: filtering failures here shifts auditors into the
// reviewer slice and can turn missing evidence into a false-green result.
const ra = await parallel(reviewerThunks.concat(auditorThunks))
const reviews = ra.slice(0, CONCERNS.length)
const audits = ra.slice(CONCERNS.length)
// key audits by BOTH slug and formal_name — agents inconsistently return one or the other
const auditBySlug = {}
for (const a of audits) { if (!a) continue; if (a.slug) auditBySlug[a.slug] = a; if (a.formal_name) auditBySlug[a.formal_name] = a }
const unfaithful = audits.filter((a) => a && (a.faithful === false || a.selected_proposition_matches === false))
const missingReviews = reviews.filter((r) => !r).length
const missingAudits = rows.filter((r) => !(auditBySlug[r.slug] || auditBySlug[r.formal_name]))
log(`Reviews ${reviews.length - missingReviews}/${reviews.length}; faithfulness audits ${audits.length - missingAudits.length}/${audits.length} (${unfaithful.length} flagged unfaithful/mismatched)`)

// ── PHASE 3: CORRECT & GROUND ───────────────────────────────────────────────
phase('Correct+Ground')
const CORRECT_SCHEMA = { type: 'object', properties: { final_source: { type: 'string' }, grounding_source: { type: 'string' },
  compiles: { type: 'boolean' }, compile_blocked_reason: { type: 'string' },
  grounding_lemmas: { type: 'array', items: { type: 'object', properties: { name: { type: 'string' }, grounds: { type: 'string' }, qed: { type: 'boolean' } }, required: ['name', 'qed'] } },
  fixes_applied: { type: 'array', items: { type: 'string' } }, remaining_errors: { type: 'string' } }, required: ['final_source', 'compiles'] }
const corrected = await agent(
  `Lead Rocq expert. Apply the review + faithfulness findings to milestone ${M.phase}; make the statement file TYPE-CHECK ` +
  `and AXIOM-FREE (no top-level Parameter/Axiom), then in grounding_${M.phase}.v prove SIMPLE Qed-closed results the new ` +
  `definitions must satisfy: a SATISFIABLE witness + ≥1 textbook identity per new primitive. Use rocq_start/rocq_check to ` +
  `iterate, rocq_compile for final + Print Assumptions.${PLANAR_RULE}\n\nSTATEMENT FILE:\n\`\`\`coq\n${draft.source}\n\`\`\`\n\n` +
  `CODE-REVIEW:\n${JSON.stringify(reviews)}\n\nFAITHFULNESS:\n${JSON.stringify(audits)}\n\n${API}\n${STATUS_RULES}\n` +
  `Return corrected statement source, grounding source, compile status (+ blocked reason if planar-gated), grounding lemmas ` +
  `w/ Qed status, fixes applied, remaining errors. Be honest about what did not reach green.`,
  { label: `correct+ground:${M.phase}`, phase: 'Correct+Ground', schema: CORRECT_SCHEMA, effort: 'high' })
const verify = await agent(
  `Independent Rocq verifier. Compile the final statement + grounding files via rocq_compile and run Print Assumptions on ` +
  `every _statement node and grounding lemma. Report per file: compiles? all nodes axiom-free (closed under the global ` +
  `context, no extra axioms)? grounding Qed-closed? Quote any error verbatim.` +
  (hasPlanar ? ` ${planarSlugs.size} row(s) carry planarity as a discharged hypothesis (G2-gated) — for those an unresolved planar hypothesis is "blocked", not "fail" or "axiom".` : '') +
  `\n\nSTATEMENTS:\n\`\`\`coq\n${corrected && corrected.final_source || draft.source}\n\`\`\`\n\nGROUNDING:\n\`\`\`coq\n${corrected && corrected.grounding_source || '(none)'}\n\`\`\``,
  { label: `verify:${M.phase}`, phase: 'Correct+Ground', schema: { type: 'object', properties: {
    statements_compile: { type: 'boolean' }, grounding_compiles: { type: 'boolean' }, statements_axiom_free: { type: 'boolean' },
    grounding_axiom_free: { type: 'boolean' }, blocked: { type: 'boolean' }, errors: { type: 'string' }, summary: { type: 'string' } },
    required: ['statements_compile', 'summary'] }, effort: 'medium' })
// A row is BLOCKED only if it is a planar row pre-G2 (row-level). A genuine compile failure is
// NOT "blocked" — it surfaces as statement=partial (via sComp) and fails ready_to_land via sComp.
const anyBlocked = hasPlanar   // milestone has ≥1 G2-blocked (planar) row
log(`Correct+Ground: compile=${verify && verify.statements_compile} axiom-free=${verify && verify.statements_axiom_free} grounding=${verify && verify.grounding_compiles}${anyBlocked ? ` (${planarSlugs.size} planar-blocked)` : ''}`)

// ── PHASE 4: IMPLICATIONS / REFUTATIONS — corrected edge policy ──────────────
phase('Implications')
const IMPL_EDGE_SCHEMA = { type: 'object', properties: { source: { type: 'string' },
  edges: { type: 'array', items: { type: 'object', properties: { name: { type: 'string' }, from: { type: 'string' }, to: { type: 'string' },
    kind: { type: 'string', enum: ['implies', 'equiv', 'refutes', 'specializes'] }, citation: { type: 'string' },
    status: { type: 'string', enum: ['verified-literature', 'candidate', 'refuted-direction'] }, proved: { type: 'boolean' },
    needs_external: { type: 'string' }, note: { type: 'string' } }, required: ['name', 'from', 'to', 'kind', 'status', 'proved'] } },
  compiles: { type: 'boolean' }, notes: { type: 'string' } }, required: ['source', 'edges', 'compiles'] }
const implications = await agent(
  `Rocq expert proving implication/refutation EDGES among milestone ${M.phase}'s nodes, as Qed-closed RELATIVE theorems ` +
  `(Theorem <A>_implies_<B> : A_statement -> B_statement), provable WITHOUT resolving either.\n` +
  `EDGE POLICY (read ${PLAN} §6 for the verified/candidate tables):\n` +
  `• every edge needs exact endpoint formulations + a citation + a status; schedule ONLY 'verified-literature' edges; ` +
  `'candidate' must be re-derived first (the Qed gate decides).\n` +
  `• NEVER assert these (FALSE/withdrawn): Reed⟹Borodin–Kostochka (refuted Δ=9,ω=8), list-total⟹Behzad, ` +
  `list-Hadwiger⟹Hadwiger (wrong-as-formulated), Caccetta–Häggkvist⟹Seymour-2nd-nbhd. A genuinely false edge must FAIL ` +
  `to compile — never force it.\n• cited-but-unformalized results → explicit external_<x>_statement hypothesis, never Admitted.\n` +
  `• refuted records (manifest status disproved, e.g. Hedetniemi) → a separate ~statement, not a global negation.\n\n` +
  `STATEMENT FILE (final):\n\`\`\`coq\n${corrected && corrected.final_source || draft.source}\n\`\`\`\n\n${API}\n` +
  `Write implications_${M.phase}.v, prove what you can via rocq_compile, return source + each edge with citation/status/proved. ` +
  `An unproved edge stays status='candidate', proved=false.\n` +
  `MANDATORY: for EVERY edge (verified/candidate/refuted-direction), also emit a machine-readable ` +
  `annotation line that meta/build_edge_graph.py extracts — prose alone is NOT enough:\n` +
  `  (*@EDGE from=<A_statement> to=<B_statement> kind=<implies|equiv|refutes|specializes> ` +
  `status=<verified|candidate|refuted-direction> proved=<true|false> cite="..." note="..." *)\n` +
  `from/to MUST be the exact _statement Definition names. A verified edge MUST also have a real ` +
  `Theorem <A>_implies_<B> (Qed) in the file; candidate/refuted edges are the annotation only.`,
  { label: `implications:${M.phase}`, phase: 'Implications', schema: IMPL_EDGE_SCHEMA, effort: 'high' })
const provedEdges = (implications && implications.edges || []).filter((e) => e.proved)
log(`Implications: ${implications && implications.edges ? implications.edges.length : 0} edges, ${provedEdges.length} proved`)

// ── leg state (sound): done requires compile + axiom-free + faithful + not blocked ──────────
const sComp = !!(verify && verify.statements_compile), sAx = !!(verify && verify.statements_axiom_free)
const gComp = !!(verify && verify.grounding_compiles), gAx = !!(verify && verify.grounding_axiom_free)
const gQed = !!(corrected && corrected.grounding_lemmas && corrected.grounding_lemmas.length &&
  corrected.grounding_lemmas.every((l) => l.qed))
const legs_update = rows.map((r) => {
  const a = auditBySlug[r.slug] || auditBySlug[r.formal_name]
  const faithful = !!(a && a.faithful !== false && a.selected_proposition_matches !== false)
  const rowEdges = provedEdges.filter((e) => e.from === r.formal_name || e.to === r.formal_name)
  const rowBlocked = !!(r.requires_planarity && !M.g2_ready)  // ROW-LEVEL G2 gate (planar rows only)
  return { slug: r.slug,
    statement: rowBlocked ? 'blocked' : (sComp && sAx && faithful ? 'done' : 'partial'),
    grounding: rowBlocked ? 'blocked' : (gComp && gAx && gQed ? 'done' : 'todo'),
    edges: rowEdges.length ? 'partial' : 'todo',
    correspondence: 'todo', audit_page: 'todo',
    faithful, axiom_free: sAx, blocked: rowBlocked, requires_planarity: !!r.requires_planarity }
})

// ── deterministic landing pack (#9) — paths are monorepo-relative (graph-theory-rocq/<pkg>/…) ──
// Until the G0 migration (§A.1) the toolchain still runs from the live digraph-theory path; these
// are the TARGET paths in graph-theory-rocq. `repo` (manifest) == package subdir under the monorepo.
const pkgRel = `${M.repo}/theories/conjectures/${M.phase}`
const files = { statements: `${pkgRel}.v`, grounding: `${M.repo}/theories/conjectures/grounding_${M.phase}.v`,
  implications: `${M.repo}/theories/conjectures/implications_${M.phase}.v` }
// ready_to_land needs the GLOBAL gates (G0 monorepo+package, G1 dep-graph, G3-core base) AND a
// clean green build AND no G2-blocked (planar) rows left in this milestone.
const ready_to_land = M.g0_ready && M.g1_ready && M.base_ready && !anyBlocked && sComp && sAx &&
  missingReviews === 0 && missingAudits.length === 0 && unfaithful.length === 0
const landing = { monorepo: 'graph-theory-rocq', package: M.repo, namespace: NS[M.repo],
  files,
  coqproject_add: [files.statements, files.grounding, files.implications],
  build_cmd: 'make   # root build (rocq makefile -f _CoqProject), matrix over packages',
  manifest_patch: 'apply legs_update to meta/opg_legs_state.json (match by slug); run meta/build_opg_manifest.py --write, then --check',
  ready_to_land,
  blockers: [ M.g0_ready ? null : 'G0: graph-theory-rocq monorepo / target package subdir not stood up',
    M.g1_ready ? null : 'G1: dependency-graph metric gate not cleared',
    M.base_ready ? null : 'G3-core: graph-theory-base not stood up (pre-G3 mode)',
    hasPlanar ? `G2: ${planarSlugs.size} planar row(s) blocked (fourcolor not installed): ${[...planarSlugs].join(', ')}` : null,
    missingReviews ? `${missingReviews} reviewer result(s) missing` : null,
    missingAudits.length ? `${missingAudits.length} faithfulness audit result(s) missing` : null,
    !sComp ? 'statements do not compile' : null, sComp && !sAx ? 'statements not axiom-free' : null,
    unfaithful.length ? `${unfaithful.length} faithfulness blocker(s)` : null ].filter(Boolean) }

return {
  milestone: M.phase, repo: M.repo,
  gates: { g0_ready: M.g0_ready, g1_ready: M.g1_ready, base_ready: M.base_ready, g2_ready: M.g2_ready },
  planar_rows: [...planarSlugs], any_blocked: anyBlocked,
  statements: rows.map((r) => ({ slug: r.slug, formal_name: r.formal_name, status: r.status, requires_planarity: !!r.requires_planarity })),
  new_primitives: draft.new_primitives, api_findings: draft.api_findings,
  review_findings: reviews, faithfulness_audits: audits, unfaithful_flags: unfaithful.length,
  verification: verify,
  correct_and_ground: { fixes: corrected && corrected.fixes_applied, grounding_lemmas: corrected && corrected.grounding_lemmas,
    compile_blocked_reason: corrected && corrected.compile_blocked_reason, remaining_errors: corrected && corrected.remaining_errors },
  implications: implications && implications.edges,
  legs_update, landing,
  sources: { statements: corrected && corrected.final_source || draft.source,
    grounding: corrected && corrected.grounding_source, implications: implications && implications.source },
}

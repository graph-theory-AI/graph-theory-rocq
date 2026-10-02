# Formalizing the FULL OpenProblemGarden corpus — v1 completion report + future tracks

> ## ✅ v1 COMPLETION REPORT — statement-complete corpus
>
> **The goal below is met.** All **227** OpenProblemGarden problems are attempted as axiom-free
> Rocq `Definition <name>_statement : Prop` — **none left todo**.
>
> - **212 done** (faithful, axiom-free, `Print Assumptions` clean) · **8 partial** (faithful,
>   documented proxy/conditional) · **7 blocked** (needs foundations deliberately out of scope).
> - **Release:** git tag **`opg-v1.0.1-227-attempted`** (supersedes `opg-v1.0-227-attempted`, which
>   had a since-fixed U4 encoding blocker + P9 gate-coverage gap found in external audit). The tag pins
>   the exact commit; `git rev-list -n1 opg-v1.0.1-227-attempted` gives the hash.
> - **Canonical living report:** [`meta/CORPUS_STATUS.md`](CORPUS_STATUS.md) — per-area & per-phase
>   counts, every partial/blocked row with its exact blocker, base surfaces, per-area foundation
>   modules, and the conjecture dependency graph. Regenerated + drift-checked by
>   `meta/report_corpus_status.py`.
> - **Reproduce the claim:**
>   - CI (toolchain-free): `make audit` — edge-graph + corpus-status invariants and no drift.
>   - Full acceptance (Rocq/MathComp toolchain + OPG clone): `make gate` — every LANDED milestone
>     compiles, is axiom-free, `Print Assumptions` clean, overlay leg-state justified.
>
> **Remaining tracks (no todo — these are the 7 blocked + 8 partial, tracked as follow-up issues):**
> - **8 partial → proxy upgrades**: replace each documented proxy with its exact source semantics
>   (e.g. Freudenthal Hamilton circles for the double-ray surrogates; De Bruijn–Erdős for the
>   odd-distance χ=∞; full drawing-space geometry for the metric proxies).
> - **7 blocked → serious new foundations**: real cardinal arithmetic (ℵ₁), point-set topology of
>   surfaces (Freudenthal `|G|`), spherical/great-circle geometry, arbitrary-closed-set obstacle
>   geometry, automorphism-group actions, ZFC/independence meta-tags.
> - **verified-edge expansion** (more `Qed`-closed inter-node implications) and **proof
>   applications** for the solved/disproved records.
> - **faithfulness checking** — since the corpus is statement-only, faithfulness is the crux;
>   the techniques (refutation-scan gate check, settled-case proofs, equivalent re-encodings,
>   mutation testing, blind readback, expert review) are in [`meta/FAITHFULNESS_CHECKS.md`](FAITHFULNESS_CHECKS.md).
>
> The detailed statement-first **plan (v4)** is retained below as the historical execution record.

**Goal.** State (not prove) in Rocq/MathComp **every** conjecture in the
`~/Recherche/graph-conjectures` OpenProblemGarden (OPG) corpus — **all 227 problems,
directed *and* undirected** — as axiom-free `Definition <name>_statement : Prop`, each
delivered with its grounding, its implication edges, its correspondence readback, and its
audit surface. This extends the directed-only programme of
`CONJECTURES_FORMALIZATION_PLAN.md` (v2, ~98 digraph conjectures) to the whole website.

**Status:** v4 (2026-06-26). Source of truth: **`docs/opg_corpus_manifest.json`** — the
**validated 227-row manifest** (per-row phase/repo/formal_name/tier/status/legs + provenance;
counts reconcile to 142 core / 85 deferred). *Whole OPG corpus, combinatorial core first*
(milestone **M-CORE**); the hard analytic tail is deferred (milestone **M-CORPUS**, §3.1).

> **v4 revision log — execution-readiness fixes (review of 2026-06-26):**
> **(1)** ledger now reconciles via the tier-respecting manifest (was 137≠142); phase/repo are
> the worklist keys, not the 140 fragmented clusters. **(2)** two completion milestones M-CORE /
> M-CORPUS + a precise definition of "audit page" (§3.1, §3 leg 5). **(3)** edge spine corrected:
> **Reed⊭Borodin–Kostochka** removed (Δ=9,ω=8 counterexample), **Ádám is open** (tournament case)
> not disproved; every edge now carries formulation+citation+status, `Qed` is the gate (§6).
> **(4)** canonical-definition ownership resolved: a thin shared **`graph-theory-base`** owns
> cross-area primitives + an acyclic import DAG (§A). **(5)** planarity is a heavyweight
> **fourcolor** dependency, gated by a spike (G2); core minors are unaffected. **(6)** provenance
> + status semantics now in every manifest row. **(7)** baseline metrics corrected (23 grounding
> files; edge-count regenerate-and-gate, §1).
>
> **Methodology unchanged from v2** — statements are axiom-free `Prop`s; edges are `Qed`-closed
> relative theorems; cited externals are hypotheses in `external.v`. *New in v3/v4:* breadth
> (undirected graph theory) + heavy reuse of `coq-graph-theory`'s undirected layer.

---

## 0. What changed from v2 → v4

| | v2 (digraph-only) | v4 (this plan) |
|---|---|---|
| Corpus | ~98 directed conjectures (OPG digraph + arXiv) | **all 227 OPG problems** (directed + undirected), validated manifest |
| Primary reuse | digraph-theory core (ω̄, dipath, strong, …) | **+ core `coq-graph-theory`**: ω/α/χ/clique/colouring, **core** minors/treewidth, matching/Menger/König, `dom.v` (planarity is a *separate, gated* fourcolor dep, §5b/R1) |
| Tiering | P0–P12 spine + P13/P14 deferred | **142 core / 85 deferred** (manifest, reconciling) |
| Packaging | one library (`digraph-theory`) | **one monorepo `graph-theory-rocq`, multi-package** over a shared `graph-theory-base` (math-comp model; digraph absorbed via subtree) — §A |

The directed corpus is **already largely done** (12 OPG rows formalized; see §1): the v4 work
is mostly the **undirected/topological/extremal/algebraic remainder** plus 20 new directed
statements (P9).

**Architecture decision (2026-06-26):** we do **not** grow `digraph-theory` into a
monolith. We build a **federation of modular `<area>-theory` libraries** — one durable
Rocq/MathComp library per area of graph theory, each of which **states** its area's
conjectures now and is **extended with their proofs later**. `digraph-theory` is the
existing template member (it states AACL 5.10 and *proves* it at k=3,4,5). See §A.

---

## A. Architecture — a federation of `<area>-theory` libraries

**Principle.** One library per area of graph theory, each a *full theory library* (not a
statements-only catalog): `conjectures/` holds the open problems as axiom-free nodes;
`applications/` is where their **proofs land over time**. This is precisely the
`digraph-theory` shape — we generalize that one library into a family, so the naming and
organization say "graph-theory libraries," not "a conjecture dump."

**Per-package layout** (each subdir under `graph-theory-rocq/`) — the `digraph-theory` template,
so proofs always have a home:

```
<area>-theory/
  theories/
    foundations/   prelude + interop.v   (the ONE file importing coq-graph-theory / digraph-theory)
    core/          the area's structures & primitives (list-assignment, hom, deck, hyperedge, …)
    invariants/    derived parameters (list-χ, χ-index, crossing-number predicate, …)
    constructions/ area builders (line-graph, total-graph, tensor/cartesian product, …)
    conjectures/   *_statement nodes (axiom-free) + grounding + within-area implication edges
    applications/  PROVED conjectures / resolved cases   ◄── the "extend with proofs" home
  docs/ scripts/ blueprint/   per-repo audit site + oracle (generated by the shared tooling)
```

A conjecture starts as a `conjectures/<c>.v` node; when it (or a case) is proved, the proof
lands in `applications/` and the node graduates to a `Theorem` — no restructuring, exactly
as `digraph-theory` did for k=3,4,5 and Cheng–Keevash δ=2,3.

**Naming & organization (adapted as requested):**
- **One monorepo, many packages — `graph-theory-rocq`** (decided 2026-06-26; the **math-comp
  model**: `math-comp/math-comp` is one repo shipping `coq-mathcomp-{ssreflect,algebra,…}`).
  Each area is a **subdirectory + its own dual opam package** (`rocq-<area>-theory` /
  `coq-<area>-theory`) with its own logical namespace (`From Chromatic Require Import …`),
  independently installable and proof-extensible — but base/atlas/blueprint and the planning
  artifacts live at the root, and cross-area edges are in-tree (no submodules). Drops the
  `*-conjectures` naming — a `*-theory` package *contains* conjectures but is a library.
- **GitHub org `llm4rocq`, repo `graph-theory-rocq`** — the public auditor moves to
  `llm4rocq.github.io/graph-theory-rocq` (with a redirect from the old digraph-theory site).
  The existing `digraph-theory` is **absorbed via `git subtree`** into `graph-theory-rocq/digraph/`,
  preserving history (see §A.1 migration runbook).

**The monorepo layout + the canonical-definition import DAG** (acyclic; the shared Rocq
library `graph-theory-base` *owns* every cross-area primitive; area packages never depend on
each other):

Subdir names equal the manifest `repo` values (so the workflow's `<repo>/theories/…` landing
paths are correct without a mapping). **✅ STOOD UP & PUSHED (gate G0 done) — https://github.com/LLM4Rocq/graph-theory-rocq (see §A.1).**

```
graph-theory-rocq/                         ONE git repo (llm4rocq/graph-theory-rocq)
  base/             coq-graph-theory-base — SINGLE owner of cross-cutting defs: the undirected
       │            interop façade; graph homomorphism `hom`; products (tensor/cartesian/lex);
       │            list-assignment + list-χ; line-graph + total-graph; Δ. One definition each,
       ▼            so cross-area `_implies_` edges type-check. Depends on coq-graph-theory + mathcomp.
  digraph-theory/   the absorbed standalone repo (directed; namespace Digraph; history preserved)
  chromatic-theory/ hamiltonicity-theory/ homomorphism-theory/ cycle-theory/ minor-theory/
  packing-theory/ reconstruction-theory/ hypergraph-theory/ topological-graph-theory/
  graph-theory-misc/      — area packages: depend ONLY on base (+ digraph-theory if directed),
       │                    NEVER on a sibling → the area layer is an antichain, no cycles.
       ▼                    Each owns its area-specific primitives (deck, hyperedge, cycle-space…).
  extremal-graph-theory/ infinite-graph-theory/ spectral-graph-theory/   — parked (deferred tail)
  atlas/            cross-area `_implies_` edges + the federated dependency graph (the only
       │            multi-area consumer; depends on the area packages it links)
  blueprint/        shared DEV-TOOLING (NOT a Rocq lib): closure gate, correspondence auditor,
       │            axiom audit, federated dep-graph + site generator (factored from digraph-theory/scripts/)
  meta/             OPG_FULL_FORMALIZATION_PLAN.md, opg_corpus_manifest.json, build_opg_manifest.py,
                    milestone_rows.py, area_milestone_pipeline.workflow.js
  Makefile · .gitignore · .github/workflows/   one root build, recurse/matrix over packages
```

**Definition-ownership table** (a primitive lives in exactly one place; `unlocks` = repos using it):

| Primitive | Owner | Used by |
|---|---|---|
| undirected interop (ω/α/χ/clique/minor/treewidth) | `graph-theory-base` | all area packages |
| graph homomorphism `hom`, graph core | `graph-theory-base` | homomorphism, chromatic, digraph (oriented-col) |
| graph products (tensor / cartesian / lex) | `graph-theory-base` | homomorphism (Hedetniemi), hamiltonicity (prisms), chromatic |
| list-assignment + list-χ / choosability | `graph-theory-base` | chromatic (U4/U5), minor (list-Hadwiger) |
| line-graph + total-graph, χ-index, degree/Δ | `graph-theory-base` | chromatic (U5), cycle (line-graph↔matching) |
| planarity façade (needs `coq-graph-theory-planar`+`fourcolor`) | `graph-theory-base` *(gated, §5b)* | topological, chromatic (planar-col) |
| area-specific (deck, hyperedge, cycle-space, immersion, dichromatic, …) | the owning `<area>-theory` | that area (+ atlas edges) |

**The library family** (core areas first; `~core` = statements to ship; each grows proofs):

| Package (`rocq-…`; subdir) | Namespace | Area | Phases (§5) | ~core | parked deferred |
|---|---|---|---|---:|---|
| **digraph-theory** *(exists)* | `Digraph` | Directed graphs & tournaments | **P9** | 32 (12 done) | — |
| **chromatic-theory** | `Chromatic` | Colouring (vertex/list/edge/total/χ-bound) | U1,U4,U5,U8 | 32 | — |
| **packing-theory** | `Packing` | Packing/covering duality, connectivity, trees, domination | U9,U13-dom | 15 | — |
| **cycle-theory** | `Cycle` | Cycle covers, decompositions, snarks (+flows) | U6,U10 | 14 | D1 flows (15) |
| **graph-theory-misc** | `GTMisc` | Labeling, pebbling, games, routing, book-thickness | U13-misc | 12 | D7 (5) |
| **homomorphism-theory** | `Hom` | Homomorphisms, cores, products, powers | U3 | 10 | — |
| **hamiltonicity-theory** | `Hamilton` | Hamiltonicity & related connectivity | U2 | 9 | — |
| **minor-theory** | `Minor` | Minors, immersion, Hadwiger-type | U7 | 6 | — |
| **topological-graph-theory** | `Topological` | Planarity, surfaces, crossing | U13-planar | 4 | D3 (10), D6 (4) |
| **hypergraph-theory** | `Hypergraph` | Hypergraphs & set systems | U12 | 4 | — |
| **reconstruction-theory** | `Reconstruction` | Reconstruction / deck | U11 | 4 | — |
| **extremal-graph-theory** *(parked)* | `Extremal` | Density / Turán / asymptotic | — | 0 | D2 (32) |
| **infinite-graph-theory** *(parked)* | `Infinite` | Infinite graphs / ends | — | 0 | D4 (14) |
| **spectral-graph-theory** *(parked)* | `Spectral` | Algebraic / spectral | — | 0 | D5 (5) |

> Counts are the manifest's package×tier totals (Σ core = 142, Σ deferred = 85; the manifest's
> `repo` field = the package id / subdir). Each *parked* package is created real (README + opam +
> namespace) so the monorepo is complete; its statements/proofs land only on opt-in (§5b).
> `graph-theory-base` (the shared owner of
> cross-area primitives, §A diagram) is not a conjecture repo and holds 0 statements.

**Tooling is shared, not copied.** The signature features — the machine-checked
**statement-closure dictionary gate**, the **correspondence auditor**, the **axiom audit**,
and the **federated conjecture dependency graph** — live in the root **`blueprint/`** dir,
parameterized over which area packages to include. The public auditor is **monorepo-wide**: one
page per result across all areas, one cross-area dependency graph. **digraph's only change** is
adopting that shared tooling instead of its private copy — its `Digraph` namespace and proofs are
untouched; it becomes the reference template every new area package is patterned on.

**Monorepo, multi-package** (the math-comp model — supersedes v4's brief multi-repo lean): each
area is a subdirectory shipping its own opam package, independently installable and
proof-extensible (exactly how `coq-mathcomp-ssreflect` etc. work), but base/atlas/blueprint and
the planning artifacts are in-tree and cross-area refactors/edges are atomic. This restores the
shared-tooling simplicity while keeping "each package extended later with proofs."

### A.1 Migration runbook — absorb `digraph-theory` (status: G0 mechanics DONE 2026-06-26)

One-time, deliberate (do NOT ad-hoc `mv` the live tree — its opam switch is linked to its path
`_opam -> ~/.opam/digraph`, the Rocq MCP resolves the switch from there; a bare move breaks the
toolchain). The absorb was done **non-destructively**: the standalone `digraph-theory` repo, its
opam switch, and the MCP are all untouched (the subtree merge *copies* history into the monorepo).

- **✅ 1. Monorepo stood up** — `git init graph-theory-rocq` + root `README`/`Makefile`/`.gitignore`
  + `base/ atlas/ blueprint/ meta/` + the 13 area-package dirs (manifest-driven READMEs/namespaces).
- **✅ 2. digraph absorbed with history** — `git subtree` binary is absent here, so used the
  equivalent `merge -s ours --allow-unrelated-histories` + `read-tree --prefix=digraph-theory/`;
  the planning commit and digraph's full history are reachable in the monorepo (48 commits).
- **✅ 3. Planning artifacts relocated to `meta/`** (plan, manifest, classification, builder, loader,
  workflow); `build_opg_manifest.py`/`milestone_rows.py` repointed to `meta/` + the corpus, and the
  builder **reproduces `meta/opg_corpus_manifest.json` byte-identically** from the new location.
- **⏳ 3b. (deferred) Extract the *existing* shared tooling** (`digraph-theory/scripts/{statement_closure,
  build_correspondence,…}.py`) → `blueprint/` — a refactor of digraph's build, left for a G0-followup.
- **⏳ 4. (deferred CUTOVER) Relink the opam switch** to the monorepo root + repoint `ROCQ_WORKSPACE`/MCP
  and the workflow's `REPO` constant. Until then the **toolchain still runs from the standalone
  `digraph-theory` path** (intentional — keeps the working switch/MCP).
- **⏳ 5–6. (deferred CUTOVER)** Dual `rocq-/coq-<area>-theory` opam packages + one CI matrix; deploy the
  auditor to `llm4rocq.github.io/graph-theory-rocq` with a redirect; retire/archive the standalone repo.

The manifest's `repo` values are the **package** ids (= subdir names) under `graph-theory-rocq/`.

---

## 1. Baseline — what already exists (we extend, not restart)

`theories/conjectures/` today (all `Print Assumptions`-clean):

- **48** statement nodes (`*_statement : Prop`) — clique-cluster (5.10/5.9/5.8),
  Caccetta–Häggkvist (+triangle), Seymour 2nd-neighbourhood, long-cycles-in-diregular,
  Jackson-Hamilton, Bang-Jensen–Yeo SAD, WC3/CL1, Bermond–Thomassen, Hoàng–Reed, Woodall,
  Linial–Berge, heroes (1605 conj 2–5, avec/tvec cores), majority-/oriented-colouring,
  mono-reachability, path-FAS family, unvd, twin-width 3.12/3.13/3.16, two-extremal 9.2, …
- **23** `grounding_*.v` faithfulness/non-vacuity files (verified count).
- **237** correspondence readback entries (`docs/correspondence/curated.json`).
- The **statement-audit site + PDF** with the CI-gated dictionary-closure check
  (`PLAN_WEB.md`): every statement-constant must resolve to a documented def-block.
- Two conjectures proved at small parameters: AACL Conj 5.10 (k∈{3,4,5}), Cheng–Keevash
  Conj 1 (δ∈{2,3}).

> **Implication-edge count must be regenerated and gated before tooling extraction.** The
> source declares **48** `_implies_/_equiv_` theorems, but the committed
> `docs/dependency_graph.json` holds **34** edges and the extractor currently detects **45** —
> three different numbers (helper lemmas matching the pattern, multi-target theorems, and
> extractor filtering all diverge). **Action:** make `build_dependency_graph.py` deterministic,
> regenerate, and add a CI gate asserting (declared edges) = (committed graph edges) before
> `graph-theory-blueprint` is factored out. Do **not** quote a single edge number until then.

So **P1–P12 of the directed spine have representatives**; v3 adds the undirected breadth
and closes the directed gaps.

---

## 2. The corpus, classified (227 problems)

| Topic (OPG 2nd-level) | core | deferred | total |
|---|---:|---:|---:|
| Coloring | 44 | 21 | 65 |
| Graph Theory (general) | 22 | 18 | 40 |
| Basic Graph Theory | 32 | 7 | 39 |
| Directed Graphs | 27 | 0 | 27 |
| Topological Graph Theory | 4 | 14 | 18 |
| Infinite Graphs | 0 | 11 | 11 |
| Extremal Graph Theory | 5 | 4 | 9 |
| Algebraic Graph Theory | 3 | 5 | 8 |
| Hypergraphs | 4 | 1 | 5 |
| Probabilistic Graph Theory | 0 | 3 | 3 |
| Graph Algorithms | 1 | 1 | 2 |
| **TOTAL** | **142** | **85** | **227** |

**Status (227):** 209 open · 14 partial · 3 solved · 1 disproved. **Formalizability buckets:**
`needs-primitive` 108, `needs-asymptotics` 41, `needs-planarity` 25, `needs-flow` 13,
`infinite` 13, `clean` 12, `bounded` 7, `needs-computation-model` 6, `hard-structural` 2.

### 2.1 The validated manifest is the source of truth

`docs/opg_corpus_manifest.json` is the **227-row, reconciling** worklist — *not* the
fragmented classification. Each row carries: `slug`, `title`, `phase` (U1–U13/P9/D1–D7),
`repo`, `formal_name` (the planned `_statement` constant), `tier`, `status` +
`status_semantics`, the five **completion legs** (`statement`/`grounding`/`edges`/
`correspondence`/`audit_page` ∈ {todo, partial, done}), and full **provenance**
(`canonical_url`, verbatim `source_text`, the exact historical `source_propositions`, and the
source commits `graph-conjectures@f6901fb`, `problems.json@27aec7f`). Reproducible faithfulness
audits — especially for the 14 partial / 3 solved / 1 disproved — read the exact selected
proposition from this file, not a paraphrase.

**Reconciliation (validated, tier-respecting → counts cannot drift):** every row is assigned
exactly one phase whose tier matches the row's tier, so the phase counts sum *by construction*.

| Tier | per-phase counts | Σ |
|---|---|---:|
| **core (142)** | U1 9 · U2 9 · U3 10 · U4 11 · U5 9 · U6 11 · U7 6 · U8 3 · U9 13 · U10 3 · U11 4 · U12 4 · U13 18 · **P9 32** | **142** |
| **deferred (85)** | D1 15 · D2 32 · D3 10 · D4 14 · D5 5 · D6 4 · D7 5 | **85** |

Of the 142 core, **12 are already formalized** in digraph-theory (legs `done`); the other 130
are the new work, with P9 = 32 directed (12 done + 20 new). **To get a repo's worklist, filter
the manifest by `repo` (or a phase by `phase`)** — superseding v3's broken "filter by cluster"
(the 140 raw cluster tags do not map 1:1 to phases; `phase`/`repo` are the authoritative keys).
The earlier `opg_full_classification.json` is retained as the raw classifier output.

---

## 3. Definition of "done" per conjecture — the five legs

Each in-scope conjecture is finished only when **all five** legs exist (the established
contract; legs 1–3 are `Qed`/type-checked content, 4–5 are the audit surface):

1. **Statement node** — `Definition <name>_statement : Prop := …`, axiom-free, faithful,
   with a non-triviality guard where needed (cf. `splitting_min_outdegree_statement`'s
   proper-bipartition clause in `classic_core.v`). Undirected statements quantify over
   `G : sgraph` (graph-theory); directed over `diGraphType`/`orientedDigraph`/`tournament`.
2. **Grounding** (`grounding_<cluster>.v`) — small `Qed`-closed witnesses that each new
   primitive is faithful: a **textbook identity** it must satisfy, a **satisfiable**
   instance (the conclusion holds somewhere), and a **discriminating refutation** (it fails
   where it should). Cf. `grounding_classic_core.v`.
3. **Implication edges** — every literature-asserted "A ⟹ B / special case / weakening"
   between two stated nodes as `Theorem <A>_implies_<B> : A_statement -> B_statement. Qed.`
   Cited but-unformalized results are carried as hypotheses declared in `external.v`
   (never `Admitted`). **Status discipline:** state the *exact* historical proposition from
   the manifest's `source_propositions`. A conjecture refuted for one class but open for
   another is stated as the **open** proposition; the settled variant is recorded *separately*
   (e.g. Ádám: node = the open *tournament* statement; a separate `Theorem adam_multidigraph_false`
   records the disproved multidigraph variant). **`solved`/`disproved` records are still stated
   as a `Definition <name>_statement`** like every other node (the goal is statement-only); a
   *proof* (for solved, e.g. EFL) or *refutation* (for disproved, e.g. Hedetniemi/Shitov) is
   **optional `applications/` work, NOT required for M-CORE** — it never expands the core scope.
4. **Correspondence readback** — one `curated.json` entry `{title, informal, decoded}`
   (CI gate: `build_correspondence.py --check`).
5. **Audit surface + dictionary closure** — **two tiers (this is what "audit page" means):**
   (a) *every* in-scope statement gets a **catalog entry** (auto-generated one-liner: name,
   kind, GitHub link) **and** a closure check — each statement-constant resolves to a
   dictionary def-block so `statement_closure.py` stays green, and `Print Assumptions` is clean;
   (b) *marquee* results additionally get a **full blueprint page** (the 6-part PLAN_WEB
   template). "Audit page for each of the 227" = the catalog-entry+closure tier for all;
   the full-page tier is marquee-only.

Plus, per phase: add files to `_CoqProject`; tiny sanity `Example`s on small instances;
cross-check values against a Python oracle where one exists in `scripts/`.

### 3.1 Two completion milestones (the goal is staged, not all-or-nothing)

The goal "all 227 + audit surface for each" is reached in **two explicit milestones**, so
"done" is unambiguous:

- **M-CORE — "142-core complete":** all 142 core rows have legs 1–4 done + the catalog/closure
  tier of leg 5, axiom-free, CI-green, across the active `<area>-theory` repos. Marquee blueprint
  pages for the ~25 flagship results. **This is the primary deliverable of the active programme.**
- **M-CORPUS — "227-corpus complete":** the 85 deferred rows additionally stated (their tier's
  infrastructure built — reals/flows/infinite/…), each with catalog/closure. Reached only as the
  deferred phases D1–D7 are opted into; until then the deferred rows sit at legs `todo` in the
  manifest with their `defer_reason`. **"227-corpus complete" is explicitly *not* required for
  M-CORE**, and the manifest's `legs`/`tier` fields track exactly which milestone each row counts
  toward.

---

## 4. New primitives & their reuse basis (ROI map)

Ranked by **core** problems unlocked. The headline: most "new" undirected primitives are
**thin wrappers over `coq-graph-theory`** — the expensive machinery (clique/χ, minors,
treewidth, matching, planarity) already exists.

| unlocks | effort | primitive | builds on |
|---:|---|---|---|
| 14 | medium | **cycle-double-cover / cycle-space** (binary cycle space over GF(2), faithful covers) | graph-theory cycles + eulerian notions |
| 12 | small | **hamiltonian cycle/path** (+ unique-ham, hamilton-decomposition) | graph-theory paths/connectivity; mirrors digraph `dicycle` |
| 11 | medium | **list-chromatic / choosability** (+ partial-list, online-choice, list-index) | generalise graph-theory `colouring`/`χ` |
| 11 | medium | **chromatic-index** via line-graph + **total-graph** | apply existing `χ` to a constructed graph |
| 11 | medium | **graph-homomorphism / core** (+ tensor, cartesian, power) | `sgraph` morphisms; finType product constructions |
| 11 | tiny | **average-degree / k-degenerate / girth** helpers | `deg` + `bigop \sum` + existing girth |
| 8 | medium | **arc-strong-connectivity + out/in-branching + spanning-strong-subdigraph** (directed) | extend digraph `strongb`/`N_out`/`dipath` |
| 7 | medium | **uniform-hypergraph** (finType incidence) + r-partite cover/matching | new finType of hyperedges; reuse matching |
| 7 | tiny | **clean χ predicates** (double-critical, valency-variety, (0,2)-graph) | directly over `ω`/`χ`/`Δ`/`clique` |
| 7 | small | **planar derived** (graph-square, degenerate/acyclic colouring, union-of-2-planar, plane-triangulation) | graph-theory **`-planar`** layer |
| 6 | small | **min-max packing/covering** (triangle-packing/transversal, t-join/t-cut, weak-saturation) | matching/König + set partitions |
| 6 | small | **immersion + apex-graph** | reuse minors/treewidth |
| 5 | medium | **reconstruction deck** (vertex/edge/switching deck = multiset of iso-classes) | `sgraph` iso + mathcomp multiset |
| 3 | small | **perfect-matching-cover / odd-edge-cut / Petersen edge-hom** (snarks) | matching + cubic-bridgeless |

**Infrastructure prerequisite (do first):** in `graph-theory-base`, re-export the **core**
undirected graph-theory layer — `sgraph` morphisms, `clique`/`ω`/`α`/`χ`, **core** `minor`,
`treewidth`, `dom` (all already installed) — behind one interop file. This **unblocks U2–U12 and
U7**. **Planarity is NOT activated here:** the `-planar` module needs the separate
`coq-graph-theory-planar`+`coq-fourcolor` packages and is added to `graph-theory-base` only after
the fourcolor spike **G2** passes (§5b/R1) — G2 gates **every `requires_planarity` row wherever it
appears** (17 core across P9/U2/U3/U4/U7/U9/U13 + 8 deferred), not whole phases.

---

## 5. The phased roadmap

Core-first by fame:cost. **Counts are the reconciling manifest counts (§2.1)** — each row's
`phase`/`repo` is authoritative in `docs/opg_corpus_manifest.json`. Each phase ends with green
CI + a tagged checkpoint and grows the implications/correspondence/closure artifacts
monotonically (§3).

> Each phase below **ships into its §A `<area>-theory` repo** (e.g. U1/U4/U5/U8 →
> `chromatic-theory`, U2 → `hamiltonicity-theory`, U6/U10 → `cycle-theory`, P9 →
> `digraph-theory`) as `conjectures/` nodes; proofs later land in that repo's `applications/`.
> The phase = a unit of work; the repo = where its files live and grow.

### 5a. CORE — undirected (U1–U13) + directed gap-closure (P9)

| id | phase | stmts | new primitives | marquee | effort |
|---|---|---:|---|---|---|
| **U1** | Clean χ-number bounds | 9 | double-critical, valency-variety, (0,2)-graph | **Reed ω/Δ/χ**, Borodin–Kostochka, EFL | small |
| **U2** | Hamiltonicity | 9 | hamiltonian cycle/path, unique-ham, ham-decomp, cartesian-product | Barnette, **Cayley-graph ham**, vertex-transitive (Lovász), prisms | small |
| **U3** | Homomorphisms, cores, products | 10 | graph-hom, core, tensor/cartesian, power, endomorphism-count | **Hedetniemi**, pentagon/weak-pentagon, cores-of-SRGs | medium |
| **U4** | List colouring / choosability | 11 | list-χ, partial-list, online-choice, list-index | edge-list-colouring conj, **list-Hadwiger**, strong colourability | medium |
| **U5** | Edge & total colouring | 9 | χ-index (line-graph), total-graph, strong-χ-index, acyclic-edge | **Goldberg**, Behzad/Total-Colouring, Seymour r-graph | medium |
| **U6** | Cycle covers & decompositions | 11 | cycle-double-cover, cycle-space, eulerian decomposition, path-decomp | **Cycle Double Cover**, strong-5-CDC, (m,n)-covers, faithful covers | medium |
| **U7** | Minors, immersion, Hadwiger-type | 6 | immersion, apex, average-degree-forces-minor | **K₆-minor**, seagull, Jörgensen, coloring+immersion | small (uses **core** minors — no planar/fourcolor) |
| **U8** | χ-boundedness (binding fn) | 3 | χ-bounded, induced-iso, vertex-minor/local-comp | Forb(induced-tree)-χ-bounded, vertex-minor-closed-χ-bounded | small |
| **U9** | Packing/covering duality + connectivity/trees | 13 | triangle-packing/transversal, t-join/t-cut, graph-packing, weak-saturation, induced-path-removal, matching-cut | **Tuza**, Bollobás–Eldridge–Catlin, Kriesell, Lovász path-removal | medium |
| **U10** | Matchings, snarks, Petersen colouring | 3 | perfect-matching-cover, odd-edge-cut, Petersen edge-hom, oddness/2-factor | **Berge–Fulkerson**, Petersen colouring | small |
| **U11** | Reconstruction (deck) | 4 | vertex/edge/switching deck, iso-multiset | **Reconstruction (Ulam)**, edge-reconstruction, switching, Graham | medium |
| **U12** | Hypergraphs & set systems | 4 | uniform-hypergraph, union-closed-family, r-partite cover/matching, k-forest | **Frankl union-closed**, **Ryser**, Turán-hypergraph | medium |
| **U13** | Planar colouring / domination / finite misc | 18 | graph-square, degenerate/acyclic colouring, union-of-2-planar, plane-triangulation, graceful-labeling, graphic-sequence, pebbling, game-value, routing, book-thickness | degenerate-planar-colouring, **Graceful Tree**, domination-in-cubic, pebbling, Beneš/shuffle-exchange | large (planar items **gated on the fourcolor spike, §5b**) |
| **P9** | Directed gap-closure (continue P-numbering) | 32 (12 done + 20 new) | arc-strong-connectivity, out/in-branching, spanning-strong-subdigraph, digraph-subdivision, disjoint-dicycle-packing, feedback-edge-set, arc-colouring | the remaining directed OPG/arXiv items; all reuse `strongb`/`outdeg`/`dipath` | large |

**Core total = 142 statements** (manifest §2.1; counts above sum exactly). Highest-ROI single
primitives: choosability (U4), χ-index-via-line-graph (U5), hom/core+products (U3),
CDC/cycle-space (U6), hamiltonicity predicate (U2). **U7 uses the *core* graph-theory minor
machinery (`core/minor.vo`, `core/treewidth.vo` — already installed); only U13's planar items
need the `coq-graph-theory-planar`/`fourcolor` spike (§5b).**

### 5b. DEFERRED tail (D1–D7) — state the predicate, schedule last

Each needs heavy new infrastructure absent from both libraries; **marked deferred** per the
scope decision. Stated math-predicate-only when reached.

| id | phase | stmts | needs | postponed marquee |
|---|---|---:|---|---|
| **D1** | Nowhere-zero flows & tensions | 15 | ℤₖ-flow / flow-polynomial algebra (undirected via orientation) | **5-flow**, 3-/4-flow, Bouchet 6-flow, Jaeger modular-orientation |
| **D2** | Density & asymptotic | 32 | mathcomp-analysis: Landau o/Ω/Θ, cⁿ, densities, thresholds | **Sidorenko**, **Erdős–Hajnal**, multicolour-EH, Shannon capacity |
| **D3** | Crossing & geometry | 10 | Euclidean drawings / crossing-number as real minimum | crossing-number of Kₙ / K_{m,n}, universal point sets, obstacle number |
| **D4** | Infinite graphs & ends | 14 | drop finiteness; ends/rays/Freudenthal; infinite arc-transitivity | unfriendly partitions, self-minor, (ℵ₀,ℵ₁)-graphs, odd-distance graph |
| **D5** | Algebraic / spectral | 5 | adjacency/Laplacian spectrum (linear algebra over reals), SRG | spectrum-determines-graph, triangle-free SRG (57-Moore is *core*, → U7) |
| **D6** | Surface topology | 4 | higher-genus embeddings, faces, non-orientable surfaces, curvature | circular embedding, Grünbaum, non-orientable obstructions |
| **D7** | Complexity & algorithms | 5 | math predicate only (existence of algorithm w/ ratio bound); no cost model | PTAS-FAS (solved), graph-hom algorithm, approximation ratios |

**Deferred total = 85** (manifest §2.1; D1 15·D2 32·D3 10·D4 14·D5 5·D6 4·D7 5). D2 is the
asymptotics catch-all for the 32 deferred rows with `phase_basis: formalizability` (no sharper
cluster keyword) — confirm each before D2 is opened.

> **The planarity spike (Risk R1; ROW-LEVEL gate G2 — applies to the manifest's `requires_planarity`
> rows, not whole phases/packages).** 17 *core* rows need planarity, spread across **P9, U2, U3, U4,
> U7, U9, U13** (e.g. Barnette (U2), planar-prism Hamiltonicity, partitioning-planar-digraphs (P9),
> acyclic-list-colouring-of-planar (U4), Jones (U9), oriented-chromatic-of-planar) — plus 8 deferred
> (D3/D6). `coq-graph-theory-planar` is a *separate* opam package depending on **`coq-fourcolor`**
> (the Four-Colour-Theorem dev — large, long compile); the current switch has neither. **Before any
> `requires_planarity` row lands:** run the G2 spike (`opam install coq-graph-theory-planar`, time a
> build, confirm the face/surface API). Until then those rows compile only with planarity as a
> *discharged Section hypothesis* and sit at leg `blocked`; their non-planar siblings in the same
> phase proceed. *Core minors/treewidth are unaffected.* The finite **57-regular Moore graph** is
> core and rides U7, independent of fourcolor.

---

## 6. Implication-edge spine — corrected, cited, status-tagged

**Policy (every edge must carry):** exact endpoint formulations, a citation, and a status ∈
{**verified-literature**, **candidate** (unverified — must be checked before stating),
**refuted-direction** (do not state)}. **The machine-check is the safeguard:** an edge enters
the spine only when its `Theorem A_statement -> B_statement` actually closes with `Qed`; a false
edge simply will not compile (e.g. Reed⟹B-K below would fail). No edge number is claimed here.

**Corrections to the v3 list (the review caught two real errors):**
- ❌ **Reed ⟹ Borodin–Kostochka is FALSE** (refuted-direction; removed from U1's action). At
  Δ=9, ω=8 Reed permits χ ≤ ⌈(Δ+1)/2 + ω/2⌉ = ⌈5+4⌉ = 9, while B–K demands χ ≤ max{Δ−1,ω} = 8.
  Reed and B–K both *sandwich* χ in [ω, Δ+1] but **neither implies the other**; record them as
  independent nodes (a candidate *common-strengthening* edge may exist, not a direct one).
- ⚠ **Ádám is OPEN, not disproved.** Only *multidigraph* counterexamples are known; the
  **tournament** case is open (manifest `status: open`, encoded over `T : tournament`,
  problems.json:1323). Node = the open tournament proposition; the disproved multidigraph
  variant is a *separate* proved `Theorem ~ adam_multidigraph_statement` — never a global `~`.
- ⚠ **Two v3 "verified" edges were also wrong-as-formulated and are removed** (below):
  *list-total ⟹ Behzad* (knowing χ″_ℓ = χ″ does **not** yield the χ″ ≤ Δ+2 bound — Behzad is a
  separate claim), and *list-Hadwiger ⟹ Hadwiger* (the recorded statement gives only
  c·t-list-colourability, not (t−1)-colourability). They move to *candidate*, pending an exact
  formulation under which an edge actually holds.

**Verified-literature edges** (textbook-standard; safe to schedule):

| edge | exact endpoints | citation |
|---|---|---|
| Petersen-colouring ⟹ Berge–Fulkerson | a Petersen edge-colouring exists ⟹ ∃ six perfect matchings covering every edge exactly twice | Jaeger 1985 |
| Petersen-colouring ⟹ Cycle Double Cover | Petersen-colouring exists ⟹ ∃ family of cycles covering each edge exactly twice | Jaeger 1985 |
| Berge–Fulkerson ⟹ CDC (cubic bridgeless) | 6-PM-cover ⟹ CDC | Jaeger (folklore) |
| strong-k-CDC ⟹ CDC | k-CDC (k cycles) is a CDC | specialization |
| circular/strong-embedding ⟹ CDC | face boundaries of a strong embedding form a CDC | folklore |
| 4-flow ⟺ 3-edge-colouring (cubic) *(D1)* | bridgeless cubic G: nowhere-zero 4-flow ⟺ 3-edge-colourable | Tutte |

**Candidate edges** (plausible but UNVERIFIED — pin exact formulations + citation, then let the
Qed gate decide): pentagon ⟹ weak-pentagon; vertex-minor-closed-χ-bounded ⟹
forbidden-induced-tree-χ-bounded; edge-list-colouring (LCC) ↔ Goldberg region; Tuza
triangle-packing/transversal ⟹ fractional relaxation (and relation to Jones); prism-hamiltonicity
⟺ hamilton-decomposition-of-prism; strong-χ-index ≥ χ-index (trivial monotone relation, state as a
lemma not a conjecture-edge); **list-total ↔ Total-Colouring** and **list-Hadwiger ↔ Hadwiger**
(demoted from "verified" — only hold under a *different* endpoint formulation than the manifest's;
re-derive the exact statements first). **Directed edges** stay inside `digraph-theory` (its
existing, already `Qed`-closed edges); do **not** assert new shaky CH⟹Seymour-type edges — CH
does *not* imply Seymour's second-neighbourhood.

---

## 7. Sequencing & first actions

**Recommended order:** `template+tooling → chromatic:U1 → hamiltonicity:U2 → digraph:P9 →
homomorphism:U3 → chromatic:U4 → chromatic:U5 → cycle:U6 → minor:U7 → chromatic:U8 →
packing:U9 → cycle:U10 → reconstruction:U11 → hypergraph:U12 → topological:U13`, then the
deferred tail D1–D7 only on opt-in.

Rationale: extract the shared template + tooling once, then U1+U2 are the cheapest famous
undirected wins; P9 is cheap (reuses the directed base) and finishes the directed member;
U3–U6 are the high-ROI colouring/hom/cycle layers; U7–U12 the famous structural areas; U13
the large finite catch-all.

**Gates** — two scopes (the earlier "clear all first" framing was wrong):

*GLOBAL — before ANY package lands:*
- **G0 — stand up `graph-theory-rocq`.** Create the monorepo and **absorb `digraph-theory` via
  `git subtree`** into `digraph/`, relinking the opam switch + repointing paths (§A.1 runbook).
  Move shared tooling to `blueprint/`, planning artifacts to `meta/`. (Also: the *target package
  subdir* must exist before that package's milestone can land.)
- **G1 — dependency-graph metric. ✅ DONE (2026-06-26), federation-wide.** `meta/build_edge_graph.py`
  extracts edges across all packages — `(*@EDGE …*)` annotations (candidate/refuted-direction) +
  `_implies_`/`_equiv_` theorems (verified, must be backed by a Theorem) — into a deterministic,
  sorted `meta/dependency_graph.json`; `--check` is the CI drift gate (wired into `make gate`). The
  legacy digraph-theory 48/34 discrepancy is reported in a `legacy` block, not used to drive the
  format. Current federation graph: 3 edges (1 candidate, 2 refuted-direction, 0 verified).
- **G3-core — base ownership. ✅ STARTED (2026-06-26).** `base/` = `coq-graph-theory-base`
  (namespace `GTBase`) re-exports the undirected interop and **owns** the first cross-area
  primitives validated by U1: `Delta` (Δ), `common_nbr`, `regular`, `girth_geq`, `ceil_div`.
  `chromatic-theory/U1` is retargeted onto it (compiles axiom-free; `check_milestone U1` → 9/9).
  *Remaining (added as their milestones need them):* hom, products, list-χ, line/total-graph.

*ROW-LEVEL — before a row with `requires_planarity` (17 core rows, spread across **P9, U2, U3,
U4, U7, U9, U13** — NOT just topological):*
- **G2 — planar/fourcolor spike.** `opam install coq-graph-theory-planar` (pulls `coq-fourcolor`)
  in a scratch switch; time the build; confirm the face/surface API. Then **G3-planar:** add the
  planarity façade to `base/`. Until G2 clears, every `requires_planarity` row compiles only with
  planarity as a *discharged Section hypothesis* and lands at leg `blocked` — regardless of phase.
  *Core minors/treewidth (most of U7) need none of this; only the planar rows do.*

**First three concrete actions** (after the GLOBAL gates G0/G1/G3-core):
1. **Settle the monorepo skeleton.** With `graph-theory-rocq` stood up (G0), `digraph/` absorbed,
   `blueprint/` holding the shared tooling (closure gate, correspondence builder, axiom audit,
   federated dep-graph + site generator), `base/` (G3) and `meta/` (plan + manifest + scripts)
   in place: one root build + CI matrix over packages; `digraph/` is the reference pattern every
   area package follows (foundations/core/invariants/constructions/conjectures/applications).
2. **Create `chromatic-theory` from the template + ship U1 end-to-end** — `conjectures/chromatic_bounds.v`
   with Reed, Borodin–Kostochka, double-critical, valency-variety, (0,2)-graph nodes (over
   `graph-theory-base`'s χ/ω/Δ) + grounding + correspondence/closure entries + blueprint pages.
   **No Reed⟹B-K edge** (refuted, §6) — record Reed and B-K as *independent* nodes; the only U1
   edge work is verifying whether any genuine common-strengthening edge exists.
   *(Proves the whole pipeline: base + template + tooling + one area + the federated auditor.)*
3. **Create `hamiltonicity-theory` + ship U2** — the hamiltonicity predicate (mirroring
   digraph `dicycle`) + Barnette/Cayley/vertex-transitive/prism nodes + grounding (a satisfied
   small instance + a non-hamiltonian refutation).

Each phase = one `theories/conjectures/<cluster>.v` (+ `grounding_<cluster>.v`) **inside its
`<area>-theory` package** (subdir of `graph-theory-rocq`), a milestone tag, green CI, `Print
Assumptions`-clean; proofs later go to that package's `applications/`. Cross-area edges go in the
**`atlas/`** package.

### 7.1 The per-milestone QA workflow (the driver)

Each milestone is executed by a **multi-agent pipeline** (`docs/area_milestone_pipeline.workflow.js`,
**v3**). It is a *Workflow-tool* script (run only via `Workflow({scriptPath, args})`; the runtime
injects `agent/phase/parallel/log/args` — not a standalone Node module). The JS sandbox has no
filesystem access, so rows are loaded **deterministically out-of-band**:
`python3 scripts/milestone_rows.py <phase> <repo>` filters + validates the manifest and emits the
canonical rows; you pass them as `args.rows` (with `phase`, `repo`, `base_ready`). The driver
**requires phase + repo** (phases like U13 span 3 repos → one repo per run) and refuses to guess.
"Achieve the plan" = run it down the (phase,repo) cells, reading results between runs. The pipeline
mirrors the five-leg deliverable (§3) with built-in QA and honours the **G2/G3 gates**:

1. **Implement** — a Rocq engineer drafts `conjectures/<phase>.v`: each row's node under its exact
   `formal_name`, **carrier type chosen per the row's `rocq_idiom`** (`sgraph` undirected,
   `tournament`/`orientedDigraph` directed, hyperedge type for hypergraphs, … — *not* a blanket
   `forall G : sgraph`). With `base_ready` it reuses cross-area primitives from **`graph-theory-base`**;
   in **pre-G3 mode** (base absent) it imports core primitives directly and marks what will move to base.
2. **Review ∥ Audit** *(parallel teams)* — a **code-review team** (idiom/naming + **base-reuse**,
   well-typedness, non-triviality/vacuity) runs concurrently with a **mathematician faithfulness-audit
   team** (one auditor per statement, comparing the `Prop` to the row's **verbatim `source_text`** and
   checking the encoded class matches the manifest's **`selected_proposition`** — e.g. Ádám over
   tournaments, not arbitrary digraphs).
3. **Correct & Ground** *(Rocq-expert team)* — apply findings, drive to a green axiom-free compile
   (no top-level `Parameter`/`Axiom`), prove **simple grounding** results (witness + textbook
   identities Δ(Kₙ)=n−1, χ(Kₙ)=n), `Print Assumptions`-verified. **Planarity-gated milestones (G2)**
   carry planarity as a *discharged Section hypothesis* (never a top-level `Parameter`, which would
   contaminate the axiom audit) and report `compile_blocked` — leg state `blocked`, not `done`.
4. **Implications / refutations** *(final step)* — prove **only verified-literature edges** (§6),
   each with citation+status; **never** the refuted/withdrawn ones (Reed⟹B-K, list-total⟹Behzad,
   list-Hadwiger⟹Hadwiger, CH⟹Seymour) — a false edge must fail to compile. Cited results → explicit
   `external` hypotheses; refuted records (Hedetniemi) → a separate `~`-theorem.

The driver runs against the live opam switch `digraph` (Rocq 9.1.1 + coq-graph-theory), so the
correct/ground/implication steps are **really compiled**, not just drafted. Outputs: the three
`.v` sources, a QA report, a **sound `legs_update`** (a row is `statement: done` only if it
compiles **and** is axiom-free **and** passed faithfulness **and** isn't blocked — else
`partial`/`blocked`; grounding likewise needs every lemma `Qed`), and a deterministic **landing
pack** (target file paths, `_CoqProject` additions, build command, manifest-patch instructions,
and `ready_to_land` — which is `false` unless **`g0_ready` ∧ `g1_ready` ∧ `base_ready` ∧ ¬anyBlocked
∧ compiles ∧ axiom-free ∧ faithful**, where `anyBlocked` includes any unresolved `requires_planarity`
row). **Run-readiness:** until the GLOBAL gates (G0 monorepo + target package subdir, G1 dep-graph,
G3-core base) clear, the driver is a *pre-G0 dry-run QA harness* (drafts/reviews/audits/grounds
against core graph-theory, no base, no landing); it becomes the green-and-land driver once those
gates pass — and individual `requires_planarity` rows stay `blocked` until G2.

---

## 8. Scale & honest caveats

- **This is a multi-month programme**: ~142 core statements × the five-leg deliverable,
  plus ~85 deferred predicates later. The win is **amortization** — one new primitive +
  its grounding serves a whole cluster (the ROI table is the budgeting tool). Treat each
  U-phase as an independently shippable release.
- **No silent truncation:** the deferred 85 are *not dropped* — they are stated as
  predicates when their infra lands. The plan tracks them explicitly (§5b).

---

## 9. Risks & open decisions

- **R1 — planar ⇒ fourcolor (heavyweight, ROW-LEVEL gate G2).** `coq-graph-theory-planar` is a
  *separate* package depending on **`coq-fourcolor`**; the switch has neither and the project depends
  only on core graph-theory. **Spike (G2) before any `requires_planarity` row lands** — 17 core rows
  across P9/U2/U3/U4/U7/U9/U13 (+ 8 deferred), not whole phases. *Non-planar minor/treewidth rows
  (most of U7) are unaffected; U7's **2 planar rows** are G2-gated like every other planar row.*
- **R2 — dictionary growth.** The audit closure dictionary goes from **23** def-blocks to ~80+;
  extend `defblocks.json` + closure gate **per phase**, or CI reddens (by design).
- **R3 — edge type-compatibility + canonical defs.** Undirected statements are over `sgraph`,
  directed over `diGraphType` — cross-type edges are rare. The single-owner rule is enforced by
  **`graph-theory-base`** (§A ownership table): one `hom`, one list-χ, one product, etc., so
  cross-area `_implies_` edges in `graph-theory-atlas` type-check rather than facing two encodings.
- **R4 — false edges.** Literature "X implies Y" claims are *unverified until `Qed`* (§6). The
  Reed⟹B-K and Ádám errors show the risk; the compile gate + per-statement faithfulness audit
  are the controls. Candidate edges are never quoted as facts.
- **D-NS — naming/identity. ✅ RESOLVED (2026-06-26): a federation of `<area>-theory`
  libraries (§A)**, each stating its conjectures now and gaining proofs later (the
  `digraph-theory` shape), not a growing `digraph-theory` and not `*-conjectures` catalogs.
- **D-REPO — repo structure. ✅ RE-RESOLVED (2026-06-26): one MONOREPO, multi-package** —
  `graph-theory-rocq`, the **math-comp model** (`coq-mathcomp-*` are packages of one repo):
  area subdirs ship independent, proof-extensible opam packages, while `base/atlas/blueprint/meta`
  and cross-area edges are in-tree. (Supersedes the earlier multi-repo lean — the shared base +
  cross-area edges made separate repos awkward; mathcomp shows monorepo ≠ giving up per-package
  versioning.) `digraph-theory` is **absorbed via `git subtree`** into `digraph/` (§A.1 runbook).
- **D-ORG — umbrella. ✅ RESOLVED: `llm4rocq` org, repo `graph-theory-rocq`** — auditor at
  `llm4rocq.github.io/graph-theory-rocq` with a redirect from the old digraph-theory site.
  (Name `graph-theory-rocq` chosen over `mathcomp-graph` to avoid implying official math-comp status,
  matching how the base `coq-graph-theory` stays unbranded.)
- **D-GRAN — area granularity (tunable knob).** §A proposes ~11 active + 3 parked area packages.
  Coarser (fold `homomorphism` into `chromatic`; `minor`+`packing`) or finer (split vertex- vs
  edge-colouring) both work — re-route by editing the manifest's `phase`/`repo` (= package) fields
  (the reconciliation re-validates automatically). *Recommend the §A cut.*
- **D-TAIL — deferred opt-in.** The parked packages (`extremal-`/`spectral-`/`infinite-graph-theory`,
  flows inside `cycle-theory`) stay empty until requested; D1 (flows) and D2 (asymptotics) are
  the most-requested famous ones if the tail is reopened.

---

## 10. Companion artifacts

- **`docs/opg_corpus_manifest.json`** — ⭐ the **validated 227-row manifest** (source of truth):
  per-row `phase`/`repo`/`formal_name`/`tier`/`status`+`status_semantics`/completion `legs` +
  full provenance (`canonical_url`, verbatim `source_text`, exact `source_propositions`, source
  commits). Counts reconcile (142 core / 85 deferred / 227). Re-route by editing `phase`/`repo`.
- **`meta/build_opg_manifest.py`** — the deterministic generator/gate: reads
  `meta/opg_full_classification.json` plus the commit- and hash-validated `graph-conjectures`
  corpus, checks or writes `meta/opg_corpus_manifest.json` **byte-identically**, and asserts every invariant (227 unique
  valid Rocq identifiers, 142/85 reconciliation, no empty propositions, exact non-open semantics,
  no unresolved routing). Run `python3 meta/build_opg_manifest.py --check` to re-verify or pass
  `--write` explicitly to refresh; CI checks the pinned upstream snapshot without writing.
- **`docs/opg_full_classification.json`** — the raw 16-classifier output the manifest is built
  from (bucket, reuse/new-primitive tags, Rocq idiom). Superseded as worklist by the manifest.
- **`docs/area_milestone_pipeline.workflow.js`** — the per-milestone QA driver (§7.1, v3;
  Workflow-tool script, not standalone Node). **`scripts/milestone_rows.py <phase> <repo>`** — the
  deterministic, validating row-loader that feeds it `args.rows` (the driver's JS sandbox can't read
  the manifest).
- **`docs/CONJECTURES_FORMALIZATION_PLAN.md`** (v2) — the directed-only predecessor; its
  P-phases remain the directed spine, continued here as P9.
- **`docs/PLAN_WEB.md`** — the audit-site/closure contract every new statement must satisfy.
- Source corpus: `graph-conjectures/data/problems.json` @ `27aec7f` (227 OPG records).

> **Home of these artifacts.** This plan + the manifest + the build/loader scripts + the workflow
> currently live in `digraph-theory/docs/` and `…/scripts/` (the established planning home). On
> standing up the monorepo (G0), they move to **`graph-theory-rocq/meta/`** as the repo-wide
> roadmap; `digraph/` keeps only its own directed-area plans. The manifest's `repo` field doubles
> as the **package** id (= subdir under `graph-theory-rocq/`).

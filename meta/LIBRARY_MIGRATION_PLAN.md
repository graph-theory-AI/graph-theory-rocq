# Reusable Graph Library Migration Plan

> Status: M0 implemented 2026-07-22; M1 edge-vocabulary implementation completed
> 2026-07-23 and reworked 2026-10-02 onto upstream `E(G)` and `GTBase.common`,
> with transparent compatibility aliases retained for one cycle. Since 2026-10-02
> the migration has priority: statement waves X230+ wait until section 15 is done.
>
> Scope: migrate reusable vocabulary out of conjecture files without changing
> the meaning, status, provenance, or accepted assumptions of any conjecture.
>
> Related plans: `meta/EXPANSION_PLAN.md`, `meta/P1_HARDENING.md`.

## 1. Objective

Turn the current statement corpus into a reusable MathComp-style graph library
while preserving the corpus as an independently auditable catalogue of
conjectures.

The target is not to eliminate every helper from `conjectures/`. Paper-specific
objects and one-off encodings belong near their statements. The target is to
eliminate repeated or generally useful graph vocabulary from those files and to
give each promoted primitive a stable owner, specification, lemma API, fidelity
verdict, and grounding tests.

This migration is compatibility-first. No helper is replaced merely because two
definitions have similar names. Each replacement requires a Rocq proof of
definitional equality, extensional equality, or logical equivalence.

## 2. Current Baseline

The 2026-07-22 inventory found approximately:

| Measure | Count |
|---|---:|
| Definitions in conjecture files | 3,077 |
| Statement definitions | 629 |
| Non-statement helper definitions | 2,448 |
| `xNN_`-prefixed helper definitions | 912 |

Repeated exact suffixes show immediate consolidation candidates, but are only a
discovery signal:

| Helper suffix | Occurrences | Initial owner candidate | Risk |
|---|---:|---|---|
| `edge_set` | 27 | `GTBase` | low |
| `path_vertices` | 9 | upstream or `GTBase` | low-medium |
| `induced_free` | 9 | upstream or `GTBase` | medium |
| `stable_set` | 7 | upstream adapter or `GTBase` | low |
| `min_degree_at_least` | 7 | `GTBase` | low |
| `uniform` | 6 | hypergraph foundation | medium |
| `tree_decomposition` | 4 | minor-theory foundation | high |
| `proper_colouring` | 4 | upstream adapter or chromatic foundation | low-medium |
| `matching` | 4 | packing or hypergraph foundation by representation | medium |

The clearest pilot is simple-graph edges. `x25_edge_set`, `x64_edge_set`, and
`x142_edge_set` duplicate an operation already exported as
`GTBase.graph_edge_set`. Their missing explicit `x != y` guard is implied by
simple-graph irreflexivity, but that fact must be proved before replacement.

## 3. Non-Negotiable Safety Invariants

Every migration change must preserve all of the following:

1. Every existing `formal_name` remains defined at the same import path.
2. Every migrated statement has a machine-checked old/new equivalence theorem,
   unless the replacement is definitionally equal and that fact is checked.
   The theorem must compare against a frozen copy of the original body, not an
   alias that has already been redirected to the canonical definition.
3. Manifest row status, leg status, provenance, and faithfulness verdict do not
   change as a side effect of library extraction.
4. `Print Assumptions` remains clean for statements, compatibility theorems, and
   foundation grounding lemmas.
5. No foundation module imports a conjecture module.
6. Package dependency direction remains acyclic.
7. A `BROKEN` primitive cannot become public library API. A `LIGHTWEIGHT`
   primitive must retain an explicit limitation in its name and documentation
   and must not be reexported as the default notion.
8. Degenerate cases are specified and tested: empty graphs, singleton graphs,
   zero parameters, truncated subtraction, empty palettes, and disconnected
   inputs where relevant.
9. No bulk semantic rewrite is accepted without an independent reader and
   machine-checked comparison artifacts.
10. `make gate`, `make audit`, mutation tests, and affected probes remain green.

If equivalence cannot be proved, the definitions are not merged. They are
classified as distinct variants or the affected row is re-audited.

## 4. Target Module Architecture

| Layer | Responsibility | May import |
|---|---|---|
| upstream `GraphTheory` | Existing graph structures and proven general theory | MathComp |
| `GTBase` focused modules | Cross-area finite graph primitives and upstream adapters | upstream, MathComp |
| area `foundations/` | Reusable vocabulary specific to one mathematical area | `GTBase`, upstream |
| area `core/`, `invariants/`, `constructions/` | Proven reusable theory over foundations | same-area foundations, `GTBase` |
| `conjectures/` | Named statements and genuinely paper-specific private vocabulary | reusable layers only |
| `grounding_*.v` | Witnesses, counterexamples, and helper sanity results | statements and reusable layers |
| non-reexported `migration/` | Frozen legacy bodies and permanent old/new certificates | reusable layers and the corresponding statement module |
| `applications/` | Derived results and cross-statement theorems | reusable layers and statements as needed |

`base/theories/base.v` remains the stable reexport surface, not the owner of
every implementation. New cross-area modules should be focused, for example:

| Proposed module | Candidate contents |
|---|---|
| upstream `E(G)` + `base/theories/common.v` | edge sets (no adapter module; see M1 record) |
| `base/theories/induced_subgraph.v` | induced restrictions and induced-free predicates, if absent upstream |
| `base/theories/walks_paths.v` | adapters and common finite path/cycle predicates, if absent upstream |
| `chromatic-theory/theories/foundations/colouring.v` | proper colouring adapters and colouring variants |
| `chromatic-theory/theories/foundations/recolouring.v` | recolouring steps, walks, and reconfiguration graphs |
| `packing-theory/theories/foundations/matching.v` | simple-graph matchings and factors |
| `hypergraph-theory/theories/foundations/hypergraph.v` | uniformity, degrees, matchings, and restrictions |
| `minor-theory/theories/foundations/decomposition.v` | tree/path decompositions and width predicates |

These filenames are proposals. The upstream audit in Phase M0 decides whether a
new module is needed or an adapter around an existing definition is sufficient.

## 5. Ownership Rules

Use the following decision order for every helper:

1. Reuse an upstream `GraphTheory` definition when it has the required semantics.
2. Add a thin `GTBase` adapter when upstream has the right object but its interface
   needs MathComp-friendly notation, reflection, or a corpus-wide compatibility
   lemma.
3. Place a primitive in `GTBase` when it is used by at least two area packages and
   is not naturally owned by one of them.
4. Place a primitive in an area foundation when it is reused by multiple
   statements or reusable results in that area.
5. Keep a helper in a conjecture module only when it encodes a paper-specific
   object, exceptional family, numerical window, or one-off composition.

Conjecture-local helpers that remain should be technically private where
possible, using a module or `Local Definition`. A globally exported `xNN_` name
is a temporary compatibility surface, not a final public API.

## 6. Public Primitive Quality Bar

A promoted primitive is not complete until it has:

| Requirement | Evidence |
|---|---|
| Descriptive stable name | no wave prefix and no paper-specific name unless mathematically standard |
| Explicit semantic specification | doc comment including all degenerate cases |
| Computational interface where appropriate | boolean predicate over finite data |
| Propositional interface where useful | reflection lemma, normally named with a `P` suffix |
| Extensional behavior | equality, membership, monotonicity, or isomorphism lemmas as appropriate |
| Grounding | small positive and negative examples proved in Rocq |
| Fidelity verdict | module contract in `meta/foundation_fidelity.json` or explicitly owned primitive verdicts in `meta/foundation_fidelity/<family>.json` |
| Compatibility results | equality or `<->` lemmas for each migrated local variant |
| Dependency review | no conjecture import and no new package cycle |
| API review | independent reader confirms that names and types match the intended mathematics |

Definitions should use MathComp finite structures such as `finType`, `{set T}`,
`pred T`, finite functions, and big operators. New notations must be scoped.
Opaque wrappers should not replace useful computation without a documented
reason.

## 7. Migration Registry

Use one machine-readable `meta/library_primitives/<family>.json` before the first
rewrite. Each family owns its document; the shared loader validates and combines
them. See `meta/library_primitives/README.md` for the storage envelope and fidelity
fragment ownership rules. The aggregate `meta/library_primitives.json` is obsolete.
Each entry should contain:

```json
{
  "canonical_name": "GraphTheory.sgraph.sg_edge_set",
  "owner": "base",
  "status": "proposed",
  "upstream_candidate": null,
  "fidelity": "FAITHFUL",
  "source_definitions": [
    "Packing.conjectures.X25.x25_edge_set",
    "Chromatic.conjectures.X64.x64_edge_set"
  ],
  "relation": "extensional-equality",
  "compatibility_theorems": [],
  "legacy_snapshot": "Packing.migration.X25_edge_set.Legacy.x25_edge_set",
  "consumers_remaining": 2,
  "reviewed_by": null
}
```

Allowed states are `proposed`, `auditing`, `canonical`, `migrating`,
`deprecated`, and `complete`. The registry checker must verify that every named
declaration and compatibility theorem exists and that `consumers_remaining`
matches repository usage.

The inventory generator must use parsed declaration names and types where
possible. Normalized suffix matching alone is insufficient because equal names
can hide different semantics and different names can encode the same concept.

## 8. Phased Execution

### M0 - Inventory, upstream audit, and debt freeze

Implementation record: `meta/LIBRARY_MIGRATION_M0.md`.

Deliverables:

- Generate the complete helper inventory, excluding statement and grounding
  certificate declarations.
- Group candidates using name normalization, unfolded type shape, dependency
  graph, and body similarity.
- Search upstream `GraphTheory` before assigning a new owner.
- Seed `meta/library_primitives/` with one document per top duplicate family.
- Extend the X211+ policy so a new non-statement helper must be either registered
  as reusable or explicitly marked paper-specific in wave metadata.
- Add a warning-only legacy duplicate report to `make audit` and a hard check for
  new waves.

Exit criteria:

- Every new helper has an ownership classification.
- No X211+ wave can introduce an unclassified helper.
- The initial edge, path, colouring, matching, and decomposition families are
  represented in the registry.

### M1 - Pilot: simple edge vocabulary

Implementation record: `meta/LIBRARY_MIGRATION_M1.md`.

Start with the lowest-risk, highest-duplication family.

Deliverables:

- Audit upstream support for finite simple edges, incidence, edge deletion, and
  edge counts.
- Select or create the canonical API in a focused `GTBase` module.
- Freeze the original helper bodies in non-reexported migration certificate
  modules before changing any consumer.
- Prove compatibility for `x25_edge_set`, `x64_edge_set`, `x142_edge_set`, and
  `GTBase.graph_edge_set`.
- Migrate X25, X64, and X142 while preserving old/new statement equivalence.
- Migrate the remaining exact edge-set variants in small area-scoped batches.
- Keep deprecated aliases for one migration cycle when other tracked files still
  import them.

Required pilot proofs include:

- adjacency implies distinct endpoints;
- membership characterization for two-element edge sets;
- deletion removes exactly one undirected edge;
- incidence agrees with endpoint membership;
- empty, singleton, `K2`, and triangle grounding cases.

Exit criteria:

- All 27 edge-set candidates are classified.
- Every equivalent variant uses the canonical API or a temporary proved alias.
- Every non-equivalent variant has a documented semantic distinction.
- The full gate and all affected grounding files pass.

### M2 - Low-risk common predicates

Migrate families whose representations already agree and whose definitions are
mostly set comprehensions or numeric wrappers:

1. edge counts and incident-edge sets;
2. stable sets and anticomplete pairs;
3. minimum/maximum degree predicates;
4. triangle-free and clique-count wrappers;
5. graph complements and elementary deletion operations.

Each family is a separate reviewable change. Do not combine unrelated families
into one mechanical rewrite.

Exit criteria:

- No exact duplicate remains for a completed family.
- Existing statements have equivalence certificates.
- Canonical APIs include positive and negative small-model tests.

### M3 - Structural graph objects

Migrate the higher-risk families only after agreeing on representation and
invariants:

1. paths, path vertices, internal vertices, and path endpoints;
2. cycles, induced cycles, holes, and cycle edge sets;
3. induced subgraphs and induced-free classes;
4. simple-graph matchings, perfect matchings, and factors;
5. tree/path decompositions and width predicates;
6. minor, shallow-minor, and model predicates.

These families often differ on repeated vertices, empty sequences, path length,
inducedness, bag coverage, or connectedness. Compatibility may therefore be
conditional rather than unconditional. The canonical API must make such guards
explicit.

Exit criteria:

- Each representation has a written invariant and constructor/eliminator lemmas.
- Conditional compatibility theorems expose every required guard.
- Any row whose old encoding omitted a load-bearing guard is re-audited instead
  of silently migrated.

### M4 - Area foundation extraction

Build reusable area layers from recurring local vocabulary:

| Area | First extraction targets |
|---|---|
| chromatic | proper/list/fractional/clustered variants, recolouring graphs, criticality |
| packing | path decompositions, matchings, factors, transversals |
| hypergraph | uniformity, degree/codegree, deletion, matching, covering |
| minor | decompositions, width, models, shallow minors, separators |
| topological | drawing/embedding adapters that respect the fidelity registry |
| extremal | density, induced saturation, common extremal wrappers |
| infinite | rays, double rays, ends, and cardinal guards when foundations mature |

An area foundation may be promoted into `GTBase` later only after a second area
needs it. This prevents `GTBase` from becoming a collection of unrelated
paper-level definitions.

Exit criteria:

- Every high-reuse area has a documented public import module.
- Conjecture files consume area APIs rather than importing sibling conjectures
  for reusable vocabulary.
- Foundation fidelity and grounding coverage are complete for promoted APIs.

### M5 - Compatibility cleanup and release surface

Deliverables:

- Remove deprecated `xNN_` aliases only when repository-wide usage is zero.
- Keep frozen legacy bodies and permanent compatibility theorems in
  non-reexported migration certificate modules. They are audit records, not
  public library alternatives, and are excluded from reusable-helper debt
  counts.
- Generate an API index with module ownership, declarations, fidelity status,
  and principal lemmas.
- Add small downstream example files that import only public modules.
- Document the supported import surface and semantic-versioning policy.

Exit criteria:

- A downstream development can use the graph library without importing any
  `conjectures/` module.
- Public modules compile independently of the corpus manifests.
- No deprecated alias remains without a tracked consumer and removal milestone.

## 9. Per-Family Migration Protocol

Every concept family follows this sequence:

1. **Discover:** enumerate definitions, consumers, grounding lemmas, and source
   statements.
2. **Compare:** unfold bodies and classify each pair as definitionally equal,
   extensionally equal, conditionally equivalent, intentionally distinct, or
   defective.
3. **Specify:** write the canonical mathematical contract and all corner cases
   before choosing an implementation.
4. **Audit upstream:** reuse or adapt existing `GraphTheory` material where
   faithful.
5. **Implement:** add the smallest public primitive and its basic lemma API.
6. **Ground:** prove positive and negative examples and computational sanity.
7. **Freeze:** copy each original body into a private `Legacy` module in a
   non-reexported migration certificate file and record its source hash.
8. **Bridge:** prove compatibility theorems from every frozen legacy body.
9. **Re-encode:** rewrite statements and prove old/new statement equivalence.
10. **Independently review:** a reader checks the unfolded definitions, guards,
   quantifier order, and source text.
11. **Gate:** run targeted builds, assumptions checks, probes, mutation tests,
    manifest checks, and the full gate.
12. **Deprecate:** retain aliases while consumers remain; remove them in a later
    change after registry confirmation.

Steps 7 through 10 cannot be replaced by testing a few examples. Examples support
the proof and catch bad specifications, but the compatibility theorem is the
semantic migration certificate.

## 10. Change and Review Boundaries

A normal migration change should contain one concept family and one of these
stages:

- canonical API plus grounding;
- compatibility lemmas;
- a bounded consumer rewrite batch;
- alias cleanup after consumers reach zero.

The API author and semantic reviewer must be different people or agents. A
change affecting more than five statement definitions requires per-row
equivalence results and a generated migration report; it cannot rely on one
aggregate theorem or textual diff review.

Avoid mixing foundation extraction with source-statement corrections. If the
comparison exposes a faithfulness defect, stop that row, record the defect, and
handle it through the existing re-audit process before resuming migration.

## 11. CI and Gate Changes

Add the following checks incrementally during M0 and M1:

| Check | Legacy behavior | X211+ behavior |
|---|---|---|
| unclassified helper | warning | reject |
| duplicate canonical primitive | warning | reject |
| foundation imports conjecture | reject | reject |
| missing fidelity entry | reject for public primitive | reject |
| missing foundation grounding | reject | reject |
| missing migration equivalence | reject when registry says `migrating` | reject |
| stale consumer count | reject | reject |
| deprecated alias use | warning | reject for new files |

The changed-milestone CI mapper must include a reverse dependency map from a
foundation declaration to all statements using it. A foundation change runs all
affected milestone checks, not only files changed textually.

For public API changes, CI must additionally compile a small downstream import
test that does not depend on conjecture modules.

## 12. Compatibility and Versioning Policy

- Statement `formal_name`s are permanent corpus identifiers.
- Public foundation names are stable after reaching `canonical` status.
- Proposed names may change while the registry state is `proposed` or
  `auditing`.
- Deprecated aliases remain for at least one completed migration batch and until
  all tracked consumers are zero.
- A semantic correction is not a deprecation. It requires a faithfulness audit,
  manifest note, and explicit old/new relationship.
- Reexports from `GTBase.base` are added only after the focused module API is
  reviewed and grounded.

## 13. Main Risks and Controls

| Risk | Control |
|---|---|
| Similar names hide different definitions | require proved equality or equivalence |
| A defective local helper becomes global | fidelity audit and grounding before promotion |
| Rewrites alter conjecture meaning | old/new statement equivalence plus independent source review |
| `GTBase` becomes monolithic | focused modules and rule-of-two ownership |
| Dependency cycles appear | foundation-to-conjecture import ban and dependency gate |
| Alias cleanup breaks hidden consumers | registry consumer count plus repository-wide compile |
| Expansion creates debt faster than migration removes it | hard helper classification for X211+ |
| Shared changes have a large blast radius | reverse-dependency CI and small migration batches |
| Boolean and Prop APIs drift apart | reflection lemmas and paired grounding tests |

## 14. Success Measures

The migration is successful when:

- new waves introduce zero unclassified reusable helpers;
- completed concept families have zero unproved duplicate implementations;
- every promoted primitive has a fidelity verdict and grounding evidence;
- every migrated statement has a clean semantic migration certificate;
- public downstream examples import no conjecture modules;
- the count of local helpers declines without forcing paper-specific vocabulary
  into shared modules;
- edge and implication proofs increasingly use shared lemmas rather than
  unfolding wave-local encodings;
- all corpus gates remain green throughout the migration.

Raw helper-count reduction is a secondary metric. The primary metric is that
each remaining local helper is deliberately local and each shared concept has
one audited, reusable API.

## 15. Execution Order to Completion (updated 2026-10-02)

Statement waves X230 and later are paused until the batches below are done; the
goal is a usable Rocq graph library with one audited definition per concept.
M0 and M1 are complete: the 31 edge-set definitions unfold to upstream `E(G)`
(#12), with their aliases kept until batch E.

Live scope, regenerated at every integration:

```sh
python3 meta/library_inventory.py --check --max-groups 400
```

Baseline on 2026-10-02 (main 5fa5b1d): 185 definition families repeat by name
(533 definitions) and 43 further groups share a body under different names
(127 definitions). Name-based families are a discovery signal only; the
comparison step of section 9 decides each pair. Duplicates are concentrated in
`conjectures/`: the library layers (`base/`, area `foundations/`, `atlas/`)
repeat only a few proof-internal names.

### Batch A - M2 cross-area predicates (home: GTBase)

| Families (normalized names) | Home |
|---|---|
| `induced_free`, `induced_H_free`, `H_free` | `GTBase.common.induced_free` |
| `delete_edges`, `delete_edges_rel`, `delete_edge_graph`, `delete_edge_rel` | `GTBase.common.del_edge_set` |
| `subgraph_of` | `GTBase.common.has_subgraph` |
| `complement_rel`, `complement_graph`, `complement` | new `GTBase` complement primitive |
| `edge_count`, `edges_between`, `cut_size`, `degree_in`, `subgraph_degree` | `GTBase.common`, over `E(G)` |
| `min_degree_at_least`, `min_degree_geq`, `min_degree`, `cubic`, `subcubic` | `GTBase.base`, next to `Delta` and `regular` |
| `triangle_free`, `clique_count`, `omega`, `maximal_clique`, `is_triangle`, `tri_edges` | `GTBase.base.triangle_free` and `GTBase.common` |
| `stable_set`, `anticomplete`, `anticomplete_between`, `complete_between` | upstream `GraphTheory.dom.stable` if faithful, else `GTBase` |
| `ball`, `set_ball`, `radius_at_most` | `GTBase.base.ball` |
| `hypercube`, `petersen`, `line_graph`, `cayley_graph`, `path_graph`, `complete_multipartite`, `disjoint_union`, `disjoint_union_rel`, `diamond`, `diamond_rel`, `theta` | `GTBase.base` (`line_graph`, `cycle_graph` exist) or a new constructions module |
| `poly_eval`, `weight`, `vertices_of_seq` | a small `GTBase` utility module |

### Batch B - M3 paths and cycles (home: new `base/theories/walks_paths.v`)

`path_vertices`, `path_internal`, `consecutive_in_path`, `consecutive_in_cycle`,
`xy_path`, `genuine_path`, `is_path`, `path_edges`, `path_edge_set`, `path_rel`,
`path_index_graph`/`path_tree`, `cycle`/`genuine_cycle`/`is_cycle`,
`cycle_edges`, `cycle_vertices`, `cycle_edge_seq`, `longest_cycle`,
`has_cycle_length`, `no_cycle_length_between`, `eulerian`, `spanning_tree`,
`tree`, `induced_path`, `induced_path_between`, `induced_cycle`,
`has_induced_cycle`, `hole`, `chordal`, `separates_xy`,
`pairwise_distant_paths`, `has_k_distant_xy_paths`, `walk_uses`.

Adapt upstream `Path`/`upath`/`ucycle` where faithful. Repeated vertices, empty
and one-vertex sequences, path length and inducedness are where compatibility
becomes conditional; the M3 rules apply.

### Batch C - M3 matchings, colourings, decompositions and minors (home: area foundations)

| Families | Home |
|---|---|
| `matching` (split by representation), `perfect_matching`, `edge_partition`, `edge_family` | packing foundations; `GTBase.common.perfect_matching` |
| `proper_colouring`, `proper_3_colouring`, `proper_three_colouring`, `proper_edge_colouring`, `bipartition`, `monochromatic`, `chi_bounded` | chromatic foundations |
| `hereditary_class`, `iso_closed`, `proper_minor_closed_class`, `perfect_graph` | `GTBase` (classes used across areas) |
| `tree_decomposition`, `pathwidth_at_most` | minor foundations (`width_params`), reconciled with `atlas` tree decompositions |
| `minor_model`, `shallow_minor_model`, `model_vertex`, `induced_subdivision`, `induced_subdivision_model`, `contains_induced_long_subdivision`, `unavoidable`, `grad_at_most` | minor foundations |

A primitive moves from an area foundation to `GTBase` only when a second area needs it.

### Batch D - M4 remaining area vocabulary

| Area | Families |
|---|---|
| chromatic | `colour_graph`, `edge_colour_rel`, `linear_forest_colour`, `kempe_step`, `star_edge_colouring`, `strong_edge_colourable`, `bfold_colouring`, `orientation_of`, `proper_orientation`, `proper_orientation_bound`, `output_colour` |
| hypergraph | `uniform`, `uniform_hypergraph`, `r_partite_uniform`, `image_edge`, `monochromatic_copy`, `forces_mono`, `edge`, `regular` |
| extremal | `ramsey_number`, `arrows`, `hom_count`, `degree_class_size`, `palette_on` |
| topological | surface wrappers (`embeddable_*`, `embedded_*`) onto `GTBase.surface`; `faces`; `linear_arboricity`, `linear_arboricity_at_most` |
| misc / cops | `cop_move`, `cop_position`, `cop_number_at_most`, `cops_win_in`, `robber_move`, `captured` onto graph-theory-misc `foundations/cops` |
| digraph | `indeg`, `loopless`, `oriented*`, `is_tournament`, `transitive_tournament` (vs `GTBase.common`), `weakly_connected`, `out_cut`/`outcut`, `dijoin`, `urel`, `underlying`, `no_sources` |
| complexity | `in_np`, `np_complete`, `problem`, `instance`, `enc_instance` onto `GTBase.complexity` |
| reconstruction, spectral | `same_deck`, `switching_reconstructible`, `strongly_regular` |

### Batch E - M5 release surface

1. Remove deprecated aliases whose repository-wide usage is zero, starting with the
   31 edge-set aliases; frozen `Legacy` bodies stay in `migration/` certificates.
2. Generate an API index: module, declaration, fidelity verdict, principal lemmas.
3. Add `examples/` files that import only public modules, compiled by the gate.
4. Document the supported import surface and the semantic-versioning policy.
5. Provide opam metadata for `GTBase` and every area foundation layer, so a
   downstream project can install the library without the corpus.

### Conventions for parallel work

- One family per change, following section 9 end to end.
- Certificates live in `<area>/theories/migration/<family>.v`, one file per family
  per area, so parallel families never edit the same certificate file.
- Each family owns `meta/library_primitives/<family>.json` with the standard
  fields and, when needed, its own explicit fidelity fragment. Shared module
  contracts remain unchanged; `meta/check_library_migration.py` must pass.
- Generated files (`meta/library_helper_inventory.json`, `meta/CORPUS_STATUS.md`,
  `meta/dependency_graph.json`) are regenerated by the integrator after each merge,
  never merged by hand.
- Step 10 (independent review) is done by someone other than the implementer,
  before integration.
- A legacy encoding found defective is re-audited as a statement change, with its
  own record; it is never repaired silently inside a migration.

### Definition of done

The section 14 measures and the M5 exit criteria hold, and
`meta/library_inventory.py` reports no repeated reusable family without a registry
entry: every remaining local helper is classified paper-specific or compatibility
alias. Statement waves then resume under the no-new-unclassified-helper rule.

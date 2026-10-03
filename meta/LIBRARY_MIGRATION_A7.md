# Library Migration A7: Undirected Edge Count

> Batch A, family A7 (normalized `edge_count`), implemented 2026-10-03 on top of the reviewed C7
> history pin `ae0e605` (C7 bipartition plus its A6 history, which already contains this worker's A6
> `6b0bc78`). Registry document `meta/library_primitives/edge-count.json`, status `deprecated` (the
> seven names stay as transparent aliases for one cycle). Fidelity fragment
> `meta/foundation_fidelity/edge-count.json` enrolls `edge_count` (FAITHFUL). `reviewed_by` stays unset
> until the independent step-10 review and the coordinator's statement check are recorded.
>
> Compact report `meta/migration_reports/edge_count.md`, regenerated from
> `meta/migration_reports/edge_count.spec.json` (baseline `ae0e605`, the real parent).

## Sources

| Definition | Old body | Relation to `edge_count G` |
|---|---|---|
| `Chromatic.conjectures.XE1.xe1_edge_count` | `#|xe1_edge_set G|` (M1 alias of `sg_edge_set`) | conversion |
| `Extremal.conjectures.X76.x76_edge_count` | `#|x76_edge_set G|` (M1 alias) | conversion |
| `Extremal.conjectures.X78.x78_edge_count` | `#|x78_edge_set G|` (M1 alias) | conversion |
| `Extremal.conjectures.D2ram.edge_count` | `#|E(G)|` | conversion |
| `Cycle.conjectures.X5.x5_edge_count` | `#|[set p : G * G | (p.1 -- p.2) && (enum_rank p.1 < enum_rank p.2)%N]|` | `edge_count_rank` |
| `Extremal.conjectures.X4.x4_edge_count` | same rank-oriented selector | `edge_count_rank` |
| `Extremal.conjectures.D2tur.edge_count` | `#|[set p : G * G | oedge p]|` (base `oedge` is that selector) | `edge_count_rank` |

All seven have type `sgraph -> nat`. The new canonical is `GTBase.common.edge_count G := #|E(G)|`, the
name and place the plan's table gives. Four helpers count unordered edges and convert. The other three
count adjacent ORDERED pairs taken in enumeration-rank order; `edge_count_rank` proves the equality
unconditionally through the finite bijection `p |-> [set p.1; p.2]`. It is injective because adjacent
vertices are distinct and the rank order fixes the orientation, and onto because each edge has exactly
one rank-increasing orientation. `base.v`'s `oedge` stays where it is: `common.v` does not import
`base.v`, so the bridge states the selector explicitly.

Not migrated:
- D2tur's `oedges` counts both orientations, twice the edge count (`grounding_D2tur.oedges_double`); a
  different quantity.
- Cut sizes and X88's within-colour counts count particular edge subsets.
- `GTBase.finite_graph.fg_edge_count` (`#|fg_edges G|`, the doubleton comprehension of adjacent
  distinct pairs) is the same count, but it is a public base definition outside this family's
  seven-definition conjecture inventory. It is unchanged and reported to the coordinator.

## Canonical API and grounding (GTBase.common)

`edge_count_rank` is the rank-oriented bridge. Grounding: `edge_count_Kn` (`C(n, 2)`, upstream
`card_edge_Kn`), `edge_count_K0_K1`, `edge_count_K2`, `edge_count_K3`, and `edge_count_diso`
(isomorphism invariance, upstream `diso_card_edge`). The public client `base/theories/examples/edge_count.v`
imports `GTBase.base` only. It covers:
- the count as `#|E(G)|` and the rank bridge;
- isomorphism invariance;
- positivity from one edge;
- `K_0`, `K_1`, `K_2`, `K_3` and `K_n`;
- that the count of `K_3` is not its six ordered adjacent pairs.

Proof consumers, all with unchanged theorem statements:
- `grounding_D2ram.edge_count_complete1` is now `GTBase.common.edge_count_Kn 1`.
- `grounding_D2tur.oedges_double` rewrites the count back to the oriented selector through
  `edge_count_rank`.
- `grounding_D2tur.edge_count_K0` is `edge_count_Kn 0`.
- `grounding_D2tur.is_turan_number_empty` empties the selector through `edge_count_rank`.
- `grounding_D2ram.common_graph_complete1` is unchanged.

## Rows and certificates

The report tool's discovery gives 35 statements and 10 intermediate chains, all frozen verbatim at
`ae0e605` in `{chromatic,cycle,extremal}-theory/theories/migration/edge_count.v`:

| Area | Frozen modules | Statements |
|---|---|---|
| chromatic | `Legacy.xe1_edge_count` (no corpus row reaches it) | 0 |
| cycle | `Legacy`, `X5Legacy` | 1 |
| extremal | `Legacy` (X4/X76/X78 counts), `D2ramLegacy` (count, `common_graph`, row), `D2turLegacy` (count, `is_turan_number`, two rows), `X4Legacy` (`turan_number`, four rows), `X76Legacy`, `X78Legacy`, `X88Legacy`, `X96Legacy`, `XE1Legacy` (five chains, eight rows), `XE2Legacy` (two chains, fifteen rows) | 34 |

The ten chains:
- D2ram's `common_graph` and D2tur's `is_turan_number`;
- X4's `turan_number`;
- XE1's `size_ramsey` and `size_ramsey_number`, `every_k_set_sparse`, `turan_number_for_graph` and
  `min_turan_over_size_edges`;
- XE2's `saturated_planar` and `incident_chord_extremal`.

Their Turan and Ramsey minimality clauses are frozen whole. D2ram and D2tur both name their helper
`edge_count`, the canonical's short name, so their frozen copies sit in their own modules and every
reference is qualified.

Helper certificates are `nat` equalities: `by []` for the four converting counts, and
`GTBase.common.edge_count_rank G` for the three rank selectors. Chain and statement certificates
unfold both sides, rewrite the frozen helpers and chains by their certificates under the binders
(Corelib `Setoid`/`Morphisms`, local `Proper` instances for `and3`/`and4`, no axiom), and close by
`reflexivity`, so a needed rewrite that does not happen leaves the proof unfinished.
`erdos_915_statement_original_compat` is the one structural proof, as in B8's own #915 Original.
B2's internal-disjointness certificate is an equivalence, not a conversion, so it is applied to the
destructured conjunct, and the count hypothesis is transported by its equation. Per-row theorems are
`XnnLegacy.<formal_name> <-> <formal_name>`. Quantifiers, Turan/Ramsey minimality, edge-count
equations and inequalities, positivity and natural-subtraction guards, statuses and documented
limitations are untouched.

## Complete Originals

Earlier families froze 20 of these rows or chains while keeping the live A7 count; those 34 frozen
declarations are documented in this family's spec. The complete rows compose every family's frozen
copy through module aliases (`M1`, `A2`, `B2`, `A5`, `A6`, `B4`, `C7`; aliased, not imported, because
their module names coincide with this file's):

| Original | Composes |
|---|---|
| `X76Original` (count and row), `X78Original` (count and row) | pre-M1 COUNTS: bodies at `061154c` over M1's frozen `Legacy.edge_set`; X78 also A5's frozen `x78_subgraph_of`. The rows are not pre-M1: the unmigrated cut sizes `x76_cut_size`/`x78_cut_size` (the planned A9 family) still count over the live M1 aliases |
| `X4Original.c5_edge_count_above_turan_statement` | B4's frozen `X4Legacy.c5_edge_count` |
| `X96Original` | A5's frozen `x59_subgraph_of` |
| `XE1Original`: `turan_number_for_graph`, `min_turan_over_size_edges`, #545, #548, #566, #567, #568, #766 | A5's frozen `xe1_subgraph_of`, A6's complete `XE1Original.graph_ramsey_number`, B4's frozen `h5_graph` (#567) |
| `XE2Original`: `incident_chord_extremal`, #570, #1018, #1019, #1080, #22, #803, #613, #742, #915, #767 | A2's frozen bipartite-plus-degree and diameter-critical (#613, #742), B2's frozen internal disjointness (#915), A5's frozen containment, A6's complete Ramsey chain (#570), B4's frozen incident-chord predicate (#767), C7's frozen `xe2_bipartition_sizes` (#1080) |

The Originals are labelled by their actual frozen baseline and the M1 dependencies they keep. A `Print All
Dependencies` probe at `526ad18` checked this (`evidence/A7-edge_count/dependency_closures_526ad18.out`):
- the X76/X78 counts are pre-M1 (`061154c`), but the X76/X78 rows reach the live `x76_edge_set`/`x78_edge_set`
  through the cut sizes;
- XE1 #567 (the `9e03072` text) reaches the live `x4_edge_set` through B4's frozen `XE1Legacy.h5_graph`;
- XE2 #613 and #742 (the `9e03072` texts) reach the live `x4_edge_set` through A2's frozen `XE2Legacy` predicates;
- the other 15 Original rows (`9e03072` texts) and the five Original chains reach no M1 alias.

So no row in the first three cases is claimed to be pre-M1. Each Original is certified by `<name>_original_compat`,
proved from the earlier families' certificates and this family's. The 13
reused frozen declarations are recorded as `historical` objects in the spec. C7's #1080 Originals and
A6's five Ramsey rows thus gain a complete pre-A5/A6/C7/A7 form.

Each earlier family's spec records A7's per-row copies that still call its live helpers (26
reciprocal notes: C7 1, A6 5, B4 3, A2 2, B2 1, A5 14). Those families' compact summaries are
regenerated, and no older frozen body is edited.

## Issues preserved, not repaired

- D2ram's prose says PARTIAL for the common-graphs row, while its OPG manifest and leg ledger record
  statement=done and grounding=done. Its body (finite eventual inequality with factor 1, threshold
  `N`, symmetric colouring, nonempty-`H` guard), prose and statuses are unchanged; the discrepancy is
  reported to the coordinator for a later re-audit.
- XE2 #915's stronger conjunction (internal and edge disjointness) and X88's formal name (which
  mentions a clique count while the statement compares edit distance) are unchanged.

## B8 history (follow-up commit)

B8 (`e377dcb`, path edges) and A7 each froze XE2 #915 while keeping the other family's live helper:
- B8's `XE2Legacy`/`XE2Original.erdos_915_statement` call the live `x4_edge_count`;
- A7's `XE2Legacy`/`XE2Original.erdos_915_statement` call the live `xe2_paths_edge_disjoint`.

The follow-up commit sits on a private baseline that merges A7 `526ad18` with B8 `e377dcb` (not for
integration). It adds `Extremal.migration.edge_count.XE2PathEdgesOriginal.erdos_915_statement`. This is
the `9e03072` row over this family's frozen `Legacy.x4_edge_count`, B2's frozen
`XE2Legacy.paths_internally_disjoint` and B8's frozen `XE2Legacy.paths_edge_disjoint` (aliased `B8`, not
imported), so it is complete before B2, A7 and B8. `erdos_915_statement_path_edges_original_compat` proves it
structurally:
- the count hypothesis is transported by its equation;
- B2's and B8's conjuncts are transported by their certificates.

The four partial snapshots are documented reciprocally: B8's two in this spec, A7's two in B8's. No earlier
frozen body or theorem signature changes. B8's frozen predicate is a `historical` object in the spec.

## Public count `fg_edge_count` (follow-up commit)

`GTBase.finite_graph.fg_edge_count` (`#|fg_edges G|`) is the same `sgraph -> nat` count. It is now an
enrolled repository source of this family, pinned at `ae0e605` (path `base/theories/finite_graph.v`, blob
`b31dd5d`, declaration hash `4bbe5388...`).
- Public API changes in `finite_graph.v`:
  - it requires `GTBase.common` without Import (no cycle: `common` imports no GTBase module);
  - `fg_edge_count` now unfolds to `GTBase.common.edge_count G`;
  - `fg_edges` is unchanged;
  - `fg_edgesE : fg_edges G = E(G)` is proved there, adapted from C1's certificate lemma of the same name
    (the explicit `x != y` guard is implied by irreflexivity), with no migration module imported;
  - `card_fg_edges : #|fg_edges G| = GTBase.common.edge_count G` is stated without the deprecated alias,
    so it adds no consumer of it.
- The frozen copy is `GTBase.migration.edge_count.Legacy.fg_edge_count`, a new base-level certificate
  file, with `fg_edge_count_compat` (`card_fg_edges`).
- Fidelity: the existing global `GTBase.finite_graph` verdict (FAITHFUL) stays; the meaning is unchanged.

The report tool's discovery, with public nodes, gives the complete closure: five rows through ten
intermediate predicates, all frozen at `ae0e605` over the frozen public count.

| Area | Frozen modules | Rows |
|---|---|---|
| extremal (`migration/edge_count.v`, additive suffix) | `X143Legacy` (`edge_density_num`, `forcing_graph`), `X180Legacy` (`average_degree_logarithmic`), `X207Legacy` (`density_at_least`, `rodl_delta_works`, `polynomial_rodl_delta`) | X143 forcing-graph characterisation, X180 log-degree multitasker, X207 polynomial Rodl |
| misc (new `migration/edge_count.v`) | `X128Legacy` (`grad_at_most`, `expansion_bounded`), `X139Legacy` (`grad_at_most`, `polynomial_expansion_class`) | X128 cheap balanced separators, X139 polynomial expansion |

Chain and row certificates rewrite the count by `fg_edge_count_compat` under the binders, with no `try`.
X143 also unfolds `x143_density_converges` and `eventually`, because the density function is passed as an
argument. Density, expansion and arithmetic guards, quantifier order, the BLOCKED status of X180 and every
other status are unchanged.

History: C1 froze the X180 row (`Extremal.migration.matching.X180Legacy`) but kept the live
`x180_average_degree_logarithmic`, which reaches the public count. `X180Original.log_degree_multitasker_exists_statement`
is the complete `9e03072` row, over C1's frozen `X180Legacy.multitasker_capacity_positive` (aliased `C1`) and
this family's frozen average-degree chain, certified structurally. The two snapshots are documented reciprocally,
and C1's compact summary is regenerated. The family's direct consumer count stays 11: the public source has no
remaining same-file consumer.

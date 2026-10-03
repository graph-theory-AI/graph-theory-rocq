# Library Migration A19: Triangle Vertex Sets and Raw Pairs

Batch A family A19, on the fixed A18 pin `748b76a` (no private union). Registry
`meta/library_primitives/triangle-set.json`; spec, hashes and per-row certificates:
`meta/migration_reports/triangles.{spec.json,md}`; API contracts are in the Rocq doc comments.

- **Contract.** `GTBase.triangles` gives thin names over upstream `clique`/`cliqueb` and MathComp sets. No clique
  predicate and no packing or transversal abstraction is added.
  - `triangle_set T`: Boolean, cardinality first.
  - `triangle T`: Prop, clique first. `triangleP` reflects between the two, and `triangle_card_firstE` gives the
    cardinality-first order.
  - `raw_pairs T`: every two-element subset of a supplied set, adjacent or not. Raw pairs are graph edges only
    under an explicit clique guard (`raw_pairs_cliqueE`).
  - Conversions: U9's and X5's triangles become `triangle`, X4's Boolean becomes `triangle_set` (so A17's
    `x4_triangle_set_compat` stays a conversion), and the three raw two-subset copies become `raw_pairs`.
  - X69's cardinality-first Prop is an iff, not a conversion.
- **API.** The reflection and the cardinality-first order; raw-pair membership and count `'C(#|T|, 2)`; no raw pair
  below two vertices; the clique-guarded edge bridge; a triangle's three raw pairs and its three distinct adjacent
  vertices.
- **Client.** The public client shows:
  - `K_3` is a triangle, and its raw pairs are its edges; the whole `K_4` is not a triangle;
  - small sets have no raw pair, while a nonadjacent pair still has one;
  - three edgeless vertices have three raw pairs but form no triangle.
- **Rows.** Frozen verbatim at `748b76a`: the seven sources and the eleven chains.
  - X69: the distance chain.
  - X4: at-most-one-edge, hits-every, and the attained `alpha1`/`tau1`.
  - XE1: the seven-set chain, the clique property and the greatest guarantee.
  - XE2 and X5: the edge-disjoint packings.
  - X5: the genuine-edge transversal.

  Also frozen: the seven current rows (X69 Havel; X4 #621; XE1 #128 and #813; XE2 #1009; U9, keeping its
  unrestricted transversal `S`; X5 #167). Every bound, attained extremum, quantifier order, natural
  subtraction/division, small-order vacuity and leg state is unchanged.
- **Complete rows.** Eleven whole-row iffs in all. The complete bridges reuse M1's and A7's certificates:
  - X4 #621 and X5 #167 (texts at the pre-M1 `061154c`) over M1's frozen edge sets;
  - XE1 #128 and XE2 #1009 (texts at A7's `ae0e605`) over A7's frozen edge count.

  X5 and XE2 reuse the frozen packing chains.
- **History.** A7's #128 and #1009 copies still name the live triangle family; they stay byte-for-byte and are
  documented in the spec. A19's per-row copies keep A7's live edge count (documented in A7's spec) and M1's live edge
  aliases. A17's frozen triangle-set support is unchanged.
- **Proof consumers.** The five `grounding_U9` lemmas, the `vocabulary_packing` bridges, A17's
  `x4_triangle_set_compat` and A7's two row certificates all keep their types.
- **Distinct.** These stay separate: the edge-filtered `xe1_clique_edge_set`, the graph-level `x211_has_triangle`,
  the compound `xe2_triangles_plus_hamilton_cycle`, and A15's whole-graph `triangle_free`.
- **Reproduction.** Build the packages. Run `python3 meta/migration_report.py triangles --check --kernel` and the
  milestones Chromatic X69, Extremal X4/XE1/XE2 and Packing U9/X5. Kernel probes are in
  `coordination/evidence/A19-triangles/`.

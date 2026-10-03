# C24: whole-graph matching (completing C1's deferred class)

C24 starts from the fixed C23 commit `a77d0b06239d7a78dd6cc0a209939ad935ac669b`. It completes
the `whole-graph-predicate` class of the existing C1 `matching` family. The owner stays upstream
`GraphTheory.connectivity.matching`, and the family baseline stays
`9e030727db115917ae077ac07a8fc6aa68661f73`. The whole `path_fas.v` file is byte-identical
between that baseline and the C23 pin.

## The public view

`Digraph.conjectures.path_fas.matching` now unfolds to the new public
`GTBase.matching_graphs.matching_graph G := @matching G E(G)`. This specializes the upstream owner
to the whole edge set; it is not a second definition. It is a predicate on the entire finite
simple graph:

- isolated vertices, the empty graph and K1 are allowed;
- there is no connectedness, perfectness, nonemptiness or positive-degree guard;
- it is not an edge-family, multigraph, hypergraph, colouring or matching-cut predicate.

The public API proves:

| Lemma | Content |
|---|---|
| `matching_graphE` | exact unfolding |
| `matching_graph_uniq_nb` | unique neighbour |
| `matching_graph_deg`, `deg_matching_graph`, `matching_graph_degP` | at most one neighbour, both directions |
| `deg_le1_irred` | an irredundant path in a graph of degree at most 1 is one edge |
| `deg_le1_forest`, `matching_graph_forest` | forest projections |
| `matching_graph_forestP` | equivalence with "forest of maximum degree at most one" |

The forest argument reuses the reasoning of `grounding_degreewidth_c3` without importing a
conjecture file. That module's own lemmas are unchanged. The bridge `path_fas.matchingP` reads
the view back as the original conjunction, since `sdeg x` is the size of `N(x)`. Only the two
proofs that destructured that conjunction now enter through it:
`implications2.matching_linear_forest` and `grounding_edges.matching_linear_forest'`. All theorem
types are unchanged.

## The certificate

`digraph-theory/theories/migration/matching.v` freezes, at the C23 pin:

- the raw local predicate (forest and `sdeg x <= 1`), not the alias;
- the `has_matchingFAS` chain, with the same witness F, `is_FAS` and the loop-guarded
  `farc_graph`;
- the complete non-corpus `matchingFAS_iff_dw1_statement`, with the exact `Delta_star` minimum
  and bound 1.

Each has an iff certificate. It is not the corpus complexity conjecture, and its documentation
and the corpus statuses are unchanged.

## Spec and registry

In the spec, the C1 baseline, its 20 frozen mappings, 9 whole statements and all old certificates
and review facts are retained. Three mappings with explicit commit a77d0b0 are appended, giving
23 mappings and 10 whole statements. Only the resolved `path_fas.matching` distinct-variant entry
is removed.

In the registry:

- the class is now `migrated-alias`, with its own pending review binding;
- the new certificates and API are registered;
- the new fidelity fragment enrolls `GTBase.matching_graphs.matching_graph`;
- `consumers_remaining` goes from 13 to 14, the extra consumer being the new bridge.

The hypergraph X6 and X15alone classes stay deferred and excluded. `U9.is_matching_edges` is a
separate follow-up.

## Clients and regeneration

The public-only client `base/theories/examples/matching_graphs.v` covers:

- **matching graphs:** the empty graph, edgeless graphs, K1, K2, and one edge beside an isolated
  vertex;
- **not matching graphs:** the path with two adjacent edges, and K3;
- **forest projection:** every matching graph is a forest.

Regenerate the compact report through the pinned wrapper with
`python3 meta/migration_report.py matching --write`; request full details with
`--details /tmp/matching-details`. Normal Digraph X2 is root-coordinated. Implementer evidence is
in coordination `evidence/C24-by-lancelot/`.

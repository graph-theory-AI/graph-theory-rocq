# Migration report: regularity

Inputs: `meta/migration_reports/regularity.spec.json` and `meta/library_primitives/regularity.json`.
Regenerate: `python3 meta/migration_report.py regularity --write`.
Full evidence: `python3 meta/migration_report.py regularity --details /tmp/migration-details`.

- Canonical: `Hypergraph.foundations.hypergraph_regularity.hg_regular`.
- Baseline: `7e030f252c859c5334185673b10b69971cab9402`.
- Scope: 2 helpers, 2 statements, 9 frozen objects, 17 recorded references.
- Source checks: 79/79 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Hypergraph.conjectures.X73.regular_tripartite_hypergraph_matching_lower_bound_statement` / studies:std_aharoni_charbit_howard_conjecture_on_matchings_i | `Hypergraph.migration.regularity.regular_tripartite_hypergraph_matching_lower_bound_statement_compat` |
| `Infinite.conjectures.D4inf3.infinite_uniquely_hamiltonian_graphs_statement` / opg:infinite_uniquely_hamiltonian_graphs | `Infinite.migration.regularity.infinite_uniquely_hamiltonian_graphs_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py regularity --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `hypergraph-theory/theories/migration/partite_uniform.v#X73PartiteLegacy.regular_tripartite_hypergraph_matching_lower_bound_statement`, `hypergraph-theory/theories/migration/matching.v#X73MatchingLegacy.regular_tripartite_hypergraph_matching_lower_bound_statement`, `chromatic-theory/theories/migration/delete_edge.v#X64Legacy.finite_bridgeless_cubic_two_homogeneous_exceptions_statement`, `chromatic-theory/theories/migration/delete_edge.v#X64Original.finite_bridgeless_cubic_two_homogeneous_exceptions_statement`, `chromatic-theory/theories/migration/delete_edges.v#X7Legacy.six_regular_four_one_graph_statement`, `chromatic-theory/theories/migration/edge_colourings.v#X213Legacy.one_factorization_conjecture_statement`, `chromatic-theory/theories/migration/induced_free.v#X43Legacy.statement`, `chromatic-theory/theories/migration/proper_colouring.v#X63Legacy.cubic_two_homogeneous_four_colour_statement`, `chromatic-theory/theories/migration/proper_colouring.v#X64Original.finite_bridgeless_cubic_two_homogeneous_exceptions_statement`, `chromatic-theory/theories/migration/simple_edges.v#X64Legacy.statement`, `cycle-theory/theories/migration/genuine_cycle.v#X212Legacy.bondy_linear_cycle_cubic_statement`, `graph-theory-misc/theories/migration/incidence_degree.v#X37Legacy.regular_graph_spanning_subgraph_degree_class_balance_statement`, `graph-theory-misc/theories/migration/subgraph_of.v#XE2Legacy.erdos_715_statement`, `hamiltonicity-theory/theories/migration/cycle_edges.v#U2Legacy.decomposing_the_prism_of_a_3_connected_cubic_planar_statement`, `hamiltonicity-theory/theories/migration/cycle_edges.v#U2Legacy.uniquely_hamiltonian_graphs_statement`, `hamiltonicity-theory/theories/migration/cycle_edges.v#X211Legacy.cantoni_planar_cubic_three_hamilton_cycles_statement`, `homomorphism-theory/theories/migration/bipartition.v#U3Legacy.weak_pentagon_statement`, `cycle-theory/theories/migration/edge_colour_class.v#X212Legacy.linear_arboricity_regular_statement`.

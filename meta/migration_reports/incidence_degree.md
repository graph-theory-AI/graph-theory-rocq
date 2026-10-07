# Migration report: incidence-degree

Inputs: `meta/migration_reports/incidence_degree.spec.json` and `meta/library_primitives/incidence-degree.json`.
Regenerate: `python3 meta/migration_report.py incidence_degree --write`.
Full evidence: `python3 meta/migration_report.py incidence_degree --details /tmp/migration-details`.

- Canonical: `GTBase.incidence.incidence_degree`.
- Baseline: `a54026d37a8b40d53340be71be783ac5d5fe3635`.
- Scope: 9 helpers, 10 statements, 33 frozen objects, 126 recorded references.
- Source checks: 286/286 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Extremal.conjectures.X36.alon_friedland_kalai_divisible_subgraph_statement` / studies:std_alon_friedland_kalai_conjecture | `Extremal.migration.incidence_degree.alon_friedland_kalai_divisible_subgraph_statement_compat` |
| `Extremal.conjectures.X84.odd_cycle_free_turan2_unique_cycle_extremal_statement` / studies:std_arman_gunderson_tsaturian_conjecture_maximum_cyc | `Extremal.migration.incidence_degree.odd_cycle_free_turan2_unique_cycle_extremal_statement_compat` |
| `Extremal.conjectures.X85.arman_tsaturian_average_degree_cycle_count_statement` / studies:std_arman_tsaturian_conjecture_on_the_number_of_cycl | `Extremal.migration.incidence_degree.arman_tsaturian_average_degree_cycle_count_statement_compat` |
| `GTMisc.conjectures.X37.regular_graph_spanning_subgraph_degree_class_balance_statement` / arxiv:2108.02685#00 | `GTMisc.migration.incidence_degree.regular_graph_spanning_subgraph_degree_class_balance_statement_compat` |
| `GTMisc.conjectures.X38.min_degree_spanning_subgraph_small_degree_multiplicity_statement` / arxiv:2108.02685#01 | `GTMisc.migration.incidence_degree.min_degree_spanning_subgraph_small_degree_multiplicity_statement_compat` |
| `Hypergraph.conjectures.X6.critical_three_uniform_min_degree_seven_statement` / erdos:834 | `Hypergraph.migration.incidence_degree.critical_three_uniform_min_degree_seven_statement_compat` |
| `Hypergraph.conjectures.XE2.erdos_833_statement` / erdos:833 | `Hypergraph.migration.incidence_degree.erdos_833_statement_compat` |
| `Hypergraph.conjectures.X73.regular_tripartite_hypergraph_matching_lower_bound_statement` / studies:std_aharoni_charbit_howard_conjecture_on_matchings_i | `Hypergraph.migration.incidence_degree.regular_tripartite_hypergraph_matching_lower_bound_statement_compat` |
| `Hypergraph.conjectures.X108.three_uniform_degenerate_hypergraph_ramsey_linear_statement` / studies:std_burr_erd_s_conjecture_for_3_uniform_hypergraphs | `Hypergraph.migration.incidence_degree.three_uniform_degenerate_hypergraph_ramsey_linear_statement_compat` |
| `Hypergraph.conjectures.X225.kpartite_hypergraph_turan_exponent_dmax_statement` / arxiv:2401.00359#01 | `Hypergraph.migration.incidence_degree.kpartite_hypergraph_turan_exponent_dmax_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py incidence_degree --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Hypergraph.foundations.hypergraph.hg_restrict`, `Hypergraph.foundations.hypergraph.hg_skeleton`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `graph-theory-misc/theories/migration/min_degree_at_least.v#X38Legacy.min_degree_spanning_subgraph_small_degree_multiplicity_statement`, `extremal-graph-theory/theories/migration/cycle_lengths.v#X84EdgeLegacy.cycle_edge_set`, `hypergraph-theory/theories/migration/uniform_hypergraph.v#X6UniformLegacy.critical_three_uniform_min_degree_seven_statement`, `hypergraph-theory/theories/migration/uniform_hypergraph.v#XE2UniformLegacy.erdos_833_statement`, `hypergraph-theory/theories/migration/uniform_hypergraph.v#X108UniformLegacy.three_uniform_degenerate_hypergraph_ramsey_linear_statement`, `hypergraph-theory/theories/migration/uniform_hypergraph.v#X225UniformLegacy.kpartite_hypergraph_turan_exponent_dmax_statement`, `hypergraph-theory/theories/migration/partite_uniform.v#X73PartiteLegacy.regular_tripartite_hypergraph_matching_lower_bound_statement`, `hypergraph-theory/theories/migration/partite_uniform.v#X225PartiteLegacy.kpartite_hypergraph_turan_exponent_dmax_statement`, `hypergraph-theory/theories/migration/image_edge.v#X108ImageLegacy.three_uniform_degenerate_hypergraph_ramsey_linear_statement`, `hypergraph-theory/theories/migration/monochromatic_copy.v#X108CopyLegacy.three_uniform_degenerate_hypergraph_ramsey_linear_statement`, `hypergraph-theory/theories/migration/forces_mono.v#X108ForcingLegacy.three_uniform_degenerate_hypergraph_ramsey_linear_statement`, `hypergraph-theory/theories/migration/matching.v#X73MatchingLegacy.regular_tripartite_hypergraph_matching_lower_bound_statement`, `hypergraph-theory/theories/migration/regularity.v#X73RegularLegacy.regular_tripartite_hypergraph_matching_lower_bound_statement`, `hypergraph-theory/theories/migration/regularity.v#Legacy.x73_regular`.

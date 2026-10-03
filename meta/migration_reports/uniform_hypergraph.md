# Migration report: uniform-hypergraph

Inputs: `meta/migration_reports/uniform_hypergraph.spec.json` and `meta/library_primitives/uniform-hypergraph.json`.
Regenerate: `python3 meta/migration_report.py uniform_hypergraph --write`.
Full evidence: `python3 meta/migration_report.py uniform_hypergraph --details /tmp/migration-details`.

- Canonical: `GTBase.hypergraph_uniformity.uniform_family`.
- Baseline: `3be65eed7084abfae36dee74f7117b598325bc4c`.
- Scope: 11 helpers, 20 statements, 44 frozen objects, 142 recorded references.
- Source checks: 442/442 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Hypergraph.conjectures.U12.are_critical_k_forests_tight_statement` / opg:are_critical_k_forests_tight | `Hypergraph.migration.uniform_hypergraph.are_critical_k_forests_tight_statement_compat` |
| `Hypergraph.conjectures.U12.turans_problem_for_hypergraphs_statement` / opg:turans_problem_for_hypergraphs | `Hypergraph.migration.uniform_hypergraph.turans_problem_for_hypergraphs_statement_compat` |
| `Hypergraph.conjectures.X104.brown_erdos_sos_three_uniform_statement` / studies:std_brown_erd_s_s_s_conjecture | `Hypergraph.migration.uniform_hypergraph.brown_erdos_sos_three_uniform_statement_compat` |
| `Hypergraph.conjectures.X108.three_uniform_degenerate_hypergraph_ramsey_linear_statement` / studies:std_burr_erd_s_conjecture_for_3_uniform_hypergraphs | `Hypergraph.migration.uniform_hypergraph.three_uniform_degenerate_hypergraph_ramsey_linear_statement_compat` |
| `Hypergraph.conjectures.X119.conlon_fox_sudakov_three_uniform_ramsey_tower_statement` / studies:std_conlon_fox_sudakov_problem_on_3_uniform_hypergra | `Hypergraph.migration.uniform_hypergraph.conlon_fox_sudakov_three_uniform_ramsey_tower_statement_compat` |
| `Hypergraph.conjectures.X137.erdos_rado_sunflower_statement` / studies:std_erd_s_rado_sunflower_conjecture | `Hypergraph.migration.uniform_hypergraph.erdos_rado_sunflower_statement_compat` |
| `Hypergraph.conjectures.X209.hypergraph_cut_excess_theta_sqrt_statement` / arxiv:1803.08462#00 | `Hypergraph.migration.uniform_hypergraph.hypergraph_cut_excess_theta_sqrt_statement_compat` |
| `Hypergraph.conjectures.X217.hypergraph_cop_number_sqrt_n_over_k_statement` / arxiv:2307.15512#00 | `Hypergraph.migration.uniform_hypergraph.hypergraph_cop_number_sqrt_n_over_k_statement_compat` |
| `Hypergraph.conjectures.X225.kpartite_hypergraph_turan_exponent_dmax_statement` / arxiv:2401.00359#01 | `Hypergraph.migration.uniform_hypergraph.kpartite_hypergraph_turan_exponent_dmax_statement_compat` |
| `Hypergraph.conjectures.X225.latin_square_hypergraph_turan_exponent_statement` / arxiv:2401.00359#02 | `Hypergraph.migration.uniform_hypergraph.latin_square_hypergraph_turan_exponent_statement_compat` |
| `Hypergraph.conjectures.X6.critical_three_uniform_min_degree_seven_statement` / erdos:834 | `Hypergraph.migration.uniform_hypergraph.critical_three_uniform_min_degree_seven_statement_compat` |
| `Hypergraph.conjectures.X6.erdos_matching_extremal_formula_statement` / erdos:1020 | `Hypergraph.migration.uniform_hypergraph.erdos_matching_extremal_formula_statement_compat` |
| `Hypergraph.conjectures.X6.three_uniform_hypergraph_dense_small_configuration_statement` / erdos:794 | `Hypergraph.migration.uniform_hypergraph.three_uniform_hypergraph_dense_small_configuration_statement_compat` |
| `Hypergraph.conjectures.XE1.erdos_719_statement` / erdos:719 | `Hypergraph.migration.uniform_hypergraph.erdos_719_statement_compat` |
| `Hypergraph.conjectures.XE1.erdos_836_statement` / erdos:836 | `Hypergraph.migration.uniform_hypergraph.erdos_836_statement_compat` |
| `Hypergraph.conjectures.XE2.erdos_775_statement` / erdos:775 | `Hypergraph.migration.uniform_hypergraph.erdos_775_statement_compat` |
| `Hypergraph.conjectures.XE2.erdos_832_statement` / erdos:832 | `Hypergraph.migration.uniform_hypergraph.erdos_832_statement_compat` |
| `Hypergraph.conjectures.XE2.erdos_833_statement` / erdos:833 | `Hypergraph.migration.uniform_hypergraph.erdos_833_statement_compat` |
| `Extremal.conjectures.D2str.simultaneous_partition_of_hypergraphs_statement` / opg:simultaneous_partition_of_hypergraphs | `Extremal.migration.uniform_hypergraph.simultaneous_partition_of_hypergraphs_statement_compat` |
| `Chromatic.conjectures.U5.a_generalization_of_vizings_theorem_statement` / opg:a_generalization_of_vizings_theorem | `Chromatic.migration.uniform_hypergraph.a_generalization_of_vizings_theorem_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py uniform_hypergraph --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `hypergraph-theory/theories/migration/cut_size.v#X209Legacy.is_min_scaled_excess`, `hypergraph-theory/theories/migration/incidence_degree.v#X6Legacy.critical_three_uniform_min_degree_seven_statement`, `hypergraph-theory/theories/migration/incidence_degree.v#XE2Legacy.erdos_833_statement`, `hypergraph-theory/theories/migration/incidence_degree.v#X108Legacy.three_uniform_degenerate_hypergraph_ramsey_linear_statement`, `hypergraph-theory/theories/migration/incidence_degree.v#X225Legacy.kpartite_hypergraph_turan_exponent_dmax_statement`, `hypergraph-theory/theories/migration/partite_uniform.v#X225PartiteLegacy.kpartite_hypergraph_turan_exponent_dmax_statement`.

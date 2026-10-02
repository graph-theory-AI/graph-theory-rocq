# Migration report: path-vertices

Inputs: `meta/migration_reports/path_vertices.spec.json` and `meta/library_primitives/path-vertices.json`.
Regenerate: `python3 meta/migration_report.py path_vertices --write`.
Full evidence: `python3 meta/migration_report.py path_vertices --details /tmp/migration-details`.

- Canonical: `GTBase.walks_paths.seq_vertices`.
- Baseline: `9e030727db115917ae077ac07a8fc6aa68661f73`.
- Scope: 9 helpers, 14 statements, 52 frozen objects, 125 recorded references.
- Source checks: 428/428 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X3.stable_cover_unique_induced_path_statement` / arxiv:1702.01094#01 | `Chromatic.migration.path_vertices.stable_cover_unique_induced_path_statement_compat` |
| `Digraph.conjectures.X2.mader_delta0_transitive_tournament_statement` / arxiv:1610.00876#00 | `Digraph.migration.path_vertices.mader_delta0_transitive_tournament_statement_compat` |
| `Digraph.conjectures.X2.oriented_trees_delta_plus_maderian_statement` / arxiv:1610.00876#01 | `Digraph.migration.path_vertices.oriented_trees_delta_plus_maderian_statement_compat` |
| `Digraph.conjectures.X2.delta_plus_maderian_disjoint_union_statement` / arxiv:1610.00876#02 | `Digraph.migration.path_vertices.delta_plus_maderian_disjoint_union_statement_compat` |
| `Digraph.conjectures.X52.oriented_tree_mader_chi_linear_bound_statement` / arxiv:1610.00876#03 | `Digraph.migration.path_vertices.oriented_tree_mader_chi_linear_bound_statement_compat` |
| `Digraph.conjectures.X90.f_subdivision_complexity_dichotomy_statement` / studies:std_bang_jensen_et_al_conjecture_f_subdivision_compl | `Digraph.migration.path_vertices.f_subdivision_complexity_dichotomy_statement_compat` |
| `GTMisc.conjectures.X39.coarse_menger_ball_separator_statement` / studies:std_coarse_menger_conjecture_georgakopoulos_papasogl | `GTMisc.migration.path_vertices.coarse_menger_ball_separator_statement_compat` |
| `GTMisc.conjectures.X40.coarse_menger_distance_two_separator_statement` / arxiv:2508.14332#00 | `GTMisc.migration.path_vertices.coarse_menger_distance_two_separator_statement_compat` |
| `GTMisc.conjectures.X113.coarse_erdos_posa_cycles_forest_statement` / studies:std_chudnovsky_seymour_coarse_erd_s_p_sa_conjecture | `GTMisc.migration.path_vertices.coarse_erdos_posa_cycles_forest_statement_compat` |
| `GTMisc.conjectures.X116.coarse_menger_paths_bounded_separator_statement` / studies:std_coarse_menger_conjecture | `GTMisc.migration.path_vertices.coarse_menger_paths_bounded_separator_statement_compat` |
| `GTMisc.conjectures.X146.geelen_coarse_gallai_A_paths_statement` / studies:std_geelen_s_coarse_gallai_conjecture | `GTMisc.migration.path_vertices.geelen_coarse_gallai_A_paths_statement_compat` |
| `Minor.conjectures.X11.induced_menger_anticomplete_paths_statement` / arxiv:2512.17232#00 | `Minor.migration.path_vertices.induced_menger_anticomplete_paths_statement_compat` |
| `Minor.conjectures.X67.theta_triangle_free_bounded_degree_treewidth_statement` / arxiv:2001.01607#01 | `Minor.migration.path_vertices.theta_triangle_free_bounded_degree_treewidth_statement_compat` |
| `Packing.conjectures.X26.bounded_degree_distant_induced_menger_statement` / arxiv:2309.07905#00 | `Packing.migration.path_vertices.bounded_degree_distant_induced_menger_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py path_vertices --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Chromatic.conjectures.XE1.xe1_vertices_of_seq`, `Cycle.conjectures.X5.x5_vertices_of_seq`, `Cycle.conjectures.X10.x10_cycle_vertices`, `Cycle.conjectures.X212.x212_cycle_vertices`, `Chromatic.conjectures.X153.x153_cycle_vertices`, `Digraph.conjectures.X19.x19_cycle_vertices`.

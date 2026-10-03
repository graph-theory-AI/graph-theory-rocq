# Migration report: tree-decomposition

Inputs: `meta/migration_reports/tree_decomposition.spec.json` and `meta/library_primitives/tree-decomposition.json`.
Regenerate: `python3 meta/migration_report.py tree_decomposition --write`.
Full evidence: `python3 meta/migration_report.py tree_decomposition --details /tmp/migration-details`.

- Canonical: `GTBase.bag_decompositions.bag_decomposition`.
- Baseline: `58d6d6090cfe12c200bc4ab64f86858074098294`.
- Scope: 4 helpers, 11 statements, 64 frozen objects, 122 recorded references.
- Source checks: 444/444 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X126.dujmovic_thue_choice_number_pathwidth_statement` / studies:std_dujmovi_et_al_question_thue_choice_number_bounde | `Chromatic.migration.bag_decompositions.dujmovic_thue_choice_number_pathwidth_statement_compat` |
| `Chromatic.conjectures.X189.spaghetti_tree_path_decomposition_chi_bound_statement` / arxiv:1703.07871#00 | `Chromatic.migration.bag_decompositions.spaghetti_tree_path_decomposition_chi_bound_statement_compat` |
| `GTMisc.conjectures.X102.bounded_tree_independence_forbidden_family_statement` / studies:std_bounded_tree_independence_number_conjecture_dall | `GTMisc.migration.bag_decompositions.bounded_tree_independence_forbidden_family_statement_compat` |
| `GTMisc.conjectures.X169.token_sliding_chordal_clique_tree_degree_polytime_statement` / arxiv:1605.00442#00 | `GTMisc.migration.bag_decompositions.token_sliding_chordal_clique_tree_degree_polytime_statement_compat` |
| `Minor.conjectures.X121.dallard_milanic_storgel_tw_omega_tree_alpha_statement` / studies:std_dallard_milani_torgel_conjecture | `Minor.migration.bag_decompositions.dallard_milanic_storgel_tw_omega_tree_alpha_statement_compat` |
| `Minor.conjectures.X127.dujmovic_joret_morin_norin_wood_two_tree_width_chi_statement` / studies:std_dujmovi_joret_morin_norin_wood_question_2_tree_w | `Minor.migration.bag_decompositions.dujmovic_joret_morin_norin_wood_two_tree_width_chi_statement_compat` |
| `Minor.conjectures.X201.treewidth_vertex_disjoint_subgraphs_log_bound_statement` / arxiv:1710.06282#01 | `Minor.migration.bag_decompositions.treewidth_vertex_disjoint_subgraphs_log_bound_statement_compat` |
| `Minor.conjectures.X27.bounded_degree_even_hole_free_bounded_treewidth_statement` / arxiv:2008.05504#00 | `Minor.migration.bag_decompositions.bounded_degree_even_hole_free_bounded_treewidth_statement_compat` |
| `Minor.conjectures.X42.even_hole_k4_diamond_free_bounded_treewidth_statement` / arxiv:2001.01607#00 | `Minor.migration.bag_decompositions.even_hole_k4_diamond_free_bounded_treewidth_statement_compat` |
| `Minor.conjectures.X67.theta_triangle_free_bounded_degree_treewidth_statement` / arxiv:2001.01607#01 | `Minor.migration.bag_decompositions.theta_triangle_free_bounded_degree_treewidth_statement_compat` |
| `Minor.conjectures.X95.subgraph_indexed_tree_decomposition_pathwidth_bound_statement` / studies:std_blanco_cook_hatzel_hilaire_illingworth_mccarty_q | `Minor.migration.bag_decompositions.subgraph_indexed_tree_decomposition_pathwidth_bound_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py tree_decomposition --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Chromatic.conjectures.X189.x189_rooted_spaghetti_index`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `chromatic-theory/theories/migration/path_tree.v#X126Legacy.pathwidth_at_most`, `chromatic-theory/theories/migration/path_tree.v#X189Legacy.spaghetti_path_decompositions_width`, `chromatic-theory/theories/migration/simple_path.v#X126Legacy.dujmovic_thue_choice_number_pathwidth_statement`, `graph-theory-misc/theories/migration/induced_free.v#X102Legacy.free_class_tree_alpha_bounded`, `graph-theory-misc/theories/migration/simple_edges.v#X102Legacy.statement`, `minor-theory/theories/migration/consecutive_in_cycle.v#X27Legacy.bounded_degree_even_hole_free_bounded_treewidth_statement`, `minor-theory/theories/migration/consecutive_in_cycle.v#X42Legacy.even_hole_k4_diamond_free_bounded_treewidth_statement`, `minor-theory/theories/migration/consecutive_in_cycle.v#X42Original.even_hole_k4_diamond_free_bounded_treewidth_statement`, `minor-theory/theories/migration/consecutive_in_path.v#X67Legacy.statement`, `minor-theory/theories/migration/consecutive_in_path.v#X67Original.statement`, `minor-theory/theories/migration/induced_free.v#X42Legacy.statement`, `minor-theory/theories/migration/path_tree.v#X95Legacy.pathwidth_at_most`, `minor-theory/theories/migration/path_tree.v#X95Legacy.subgraph_indexed_tree_decomposition_pathwidth_bound_statement`, `minor-theory/theories/migration/path_vertices.v#X67Legacy.statement`, `chromatic-theory/theories/migration/pathwidth.v#Legacy.x126_pathwidth_at_most`, `minor-theory/theories/migration/pathwidth.v#Legacy.x95_pathwidth_at_most`, `minor-theory/theories/migration/pathwidth.v#Legacy.subgraph_indexed_tree_decomposition_pathwidth_bound_statement`.

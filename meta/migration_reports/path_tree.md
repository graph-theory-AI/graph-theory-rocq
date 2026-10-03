# Migration report: path-tree

Inputs: `meta/migration_reports/path_tree.spec.json` and `meta/library_primitives/path-tree.json`.
Regenerate: `python3 meta/migration_report.py path_tree --write`.
Full evidence: `python3 meta/migration_report.py path_tree --details /tmp/migration-details`.

- Canonical: `GTBase.path_trees.path_tree`.
- Baseline: `e377dcbcf549c044b7b2a4321831792c1c78f375`.
- Scope: 4 helpers, 4 statements, 12 frozen objects, 42 recorded references.
- Source checks: 123/123 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X126.dujmovic_thue_choice_number_pathwidth_statement` / studies:std_dujmovi_et_al_question_thue_choice_number_bounde | `Chromatic.migration.path_tree.dujmovic_thue_choice_number_pathwidth_statement_compat` |
| `Chromatic.conjectures.X189.spaghetti_tree_path_decomposition_chi_bound_statement` / arxiv:1703.07871#00 | `Chromatic.migration.path_tree.spaghetti_tree_path_decomposition_chi_bound_statement_compat` |
| `Extremal.conjectures.X105.non_star_non_path_tree_inducibility_bounded_away_statement` / studies:std_bubeck_linial_problem_4_tree_inducibility_bounde | `Extremal.migration.path_tree.non_star_non_path_tree_inducibility_bounded_away_statement_compat` |
| `Minor.conjectures.X95.subgraph_indexed_tree_decomposition_pathwidth_bound_statement` / studies:std_blanco_cook_hatzel_hilaire_illingworth_mccarty_q | `Minor.migration.path_tree.subgraph_indexed_tree_decomposition_pathwidth_bound_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py path_tree --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Hom.conjectures.U3.path_graph`, `Packing.conjectures.X18.x18_path_graph`, `Packing.conjectures.X226.x226_path_graph`, `Digraph.conjectures.path_fas.linear_forest`, `GTMisc.conjectures.X74.x74_induced_linear_forest`, `Cycle.conjectures.X212.x212_linear_forest_colour`, `Chromatic.conjectures.X34.x34_linear_forest_colour`, `Topological.conjectures.X23.x23_linear_forest_colour`, `Extremal.conjectures.X105.x105_star_tree`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `chromatic-theory/theories/migration/simple_path.v#X126Legacy.dujmovic_thue_choice_number_pathwidth_statement`, `chromatic-theory/theories/migration/bag_decompositions.v#X126Legacy.pathwidth_at_most`, `chromatic-theory/theories/migration/bag_decompositions.v#X189Legacy.spaghetti_path_decompositions_width`, `minor-theory/theories/migration/bag_decompositions.v#Legacy.x95_pathwidth_at_most`, `chromatic-theory/theories/migration/pathwidth.v#Legacy.x126_pathwidth_at_most`, `minor-theory/theories/migration/pathwidth.v#Legacy.x95_pathwidth_at_most`.

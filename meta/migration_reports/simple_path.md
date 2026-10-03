# Migration report: simple-path

Inputs: `meta/migration_reports/simple_path.spec.json` and `meta/library_primitives/simple-path.json`.
Regenerate: `python3 meta/migration_report.py simple_path --write`.
Full evidence: `python3 meta/migration_report.py simple_path --details /tmp/migration-details`.

- Canonical: `GTBase.walks_paths.seq_simple_path`.
- Baseline: `95cba2c0a2a75104de2c8d0c29ee952da419b9c1`.
- Scope: 4 helpers, 5 statements, 23 frozen objects, 53 recorded references.
- Source checks: 180/180 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X126.dujmovic_thue_choice_number_pathwidth_statement` / studies:std_dujmovi_et_al_question_thue_choice_number_bounde | `Chromatic.migration.simple_path.dujmovic_thue_choice_number_pathwidth_statement_compat` |
| `GTMisc.conjectures.X14.andersen_rainbow_path_statement` / studies:std_andersen_s_conjecture | `GTMisc.migration.simple_path.andersen_rainbow_path_statement_compat` |
| `GTMisc.conjectures.X62.rainbow_paths_linear_edge_cover_statement` / arxiv:2301.08707#01 | `GTMisc.migration.simple_path.rainbow_paths_linear_edge_cover_statement_compat` |
| `Topological.conjectures.X23.planar_bounded_nonrepetitive_chromatic_statement` / studies:std_alon_grytczuk_ha_uszczak_riordan_conjecture | `Topological.migration.simple_path.planar_bounded_nonrepetitive_chromatic_statement_compat` |
| `Packing.conjectures.X178.gallai_odd_semiclique_path_decomposition_statement` / arxiv:1609.06257#00 | `Packing.migration.simple_path.gallai_odd_semiclique_path_decomposition_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py simple_path --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Packing.conjectures.U9.spath`, `Extremal.conjectures.XE2.xe2_path_in_graph`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `graph-theory-misc/theories/migration/edge_colourings.v#X14Legacy.andersen_rainbow_path_statement`, `graph-theory-misc/theories/migration/edge_colourings.v#X62Legacy.rainbow_paths_linear_edge_cover_statement`, `graph-theory-misc/theories/migration/path_edges.v#X14Legacy.rainbow_path`, `packing-theory/theories/migration/path_edges.v#X178Legacy.path_decomposition_at_most`, `chromatic-theory/theories/migration/path_tree.v#X126Legacy.dujmovic_thue_choice_number_pathwidth_statement`, `chromatic-theory/theories/migration/bag_decompositions.v#X126Legacy.dujmovic_thue_choice_number_pathwidth_statement`, `chromatic-theory/theories/migration/pathwidth.v#Legacy.dujmovic_thue_choice_number_pathwidth_statement`.

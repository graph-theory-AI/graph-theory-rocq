# Migration report: pathwidth

Inputs: `meta/migration_reports/pathwidth.spec.json` and `meta/library_primitives/pathwidth.json`.
Regenerate: `python3 meta/migration_report.py pathwidth --write`.
Full evidence: `python3 meta/migration_report.py pathwidth --details /tmp/migration-details`.

- Canonical: `GTBase.pathwidth.pathwidth_at_most`.
- Baseline: `cdb9e10161e6566b9a812b0931488acb6338be9f`.
- Scope: 2 helpers, 2 statements, 17 frozen objects, 23 recorded references.
- Source checks: 116/116 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X126.dujmovic_thue_choice_number_pathwidth_statement` / studies:std_dujmovi_et_al_question_thue_choice_number_bounde | `Chromatic.migration.pathwidth.dujmovic_thue_choice_number_pathwidth_statement_compat` |
| `Minor.conjectures.X95.subgraph_indexed_tree_decomposition_pathwidth_bound_statement` / studies:std_blanco_cook_hatzel_hilaire_illingworth_mccarty_q | `Minor.migration.pathwidth.subgraph_indexed_tree_decomposition_pathwidth_bound_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py pathwidth --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Minor.conjectures.X95.x95_subgraph_indexed_tree_decomposition_width_at_most`, `Minor.foundations.width_params.tw_le`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `chromatic-theory/theories/migration/simple_path.v#X126Legacy.dujmovic_thue_choice_number_pathwidth_statement`.

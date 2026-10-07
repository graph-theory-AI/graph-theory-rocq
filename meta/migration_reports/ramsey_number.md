# Migration report: ramsey-number

Inputs: `meta/migration_reports/ramsey_number.spec.json` and `meta/library_primitives/ramsey-number.json`.
Regenerate: `python3 meta/migration_report.py ramsey_number --write`.
Full evidence: `python3 meta/migration_report.py ramsey_number --details /tmp/migration-details`.

- Canonical: `Hypergraph.foundations.hypergraph_ramsey.hg_ramsey_number`.
- Baseline: `eae6c3ae123de43cad5ac0675ee25ab3f48c7b10`.
- Scope: 2 helpers, 2 statements, 19 frozen objects, 25 recorded references.
- Source checks: 123/123 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Hypergraph.conjectures.X117.conlon_fox_rodl_hedgehog_ramsey_statement` / studies:std_conlon_fox_r_dl_question_on_hedgehog_ramsey_numb | `Hypergraph.migration.ramsey_number.conlon_fox_rodl_hedgehog_ramsey_statement_compat` |
| `Hypergraph.conjectures.X119.conlon_fox_sudakov_three_uniform_ramsey_tower_statement` / studies:std_conlon_fox_sudakov_problem_on_3_uniform_hypergra | `Hypergraph.migration.ramsey_number.conlon_fox_sudakov_three_uniform_ramsey_tower_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py ramsey_number --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Extremal.conjectures.X195.x195_ramsey_number`, `Extremal.conjectures.X215.x215_ramsey_number`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `hypergraph-theory/theories/migration/uniform_hypergraph.v#X119UniformLegacy.conlon_fox_sudakov_three_uniform_ramsey_tower_statement`.

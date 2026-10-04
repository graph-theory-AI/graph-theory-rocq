# Migration report: petersen

Inputs: `meta/migration_reports/petersen.spec.json` and `meta/library_primitives/petersen.json`.
Regenerate: `python3 meta/migration_report.py petersen --write`.
Full evidence: `python3 meta/migration_report.py petersen --details /tmp/migration-details`.

- Canonical: `GTBase.petersen.petersen_ord`.
- Baseline: `ba3c7488b171091c9121dd8ea0ab2f73c3d294bf`.
- Scope: 7 helpers, 3 statements, 20 frozen objects, 127 recorded references.
- Source checks: 241/241 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Cycle.conjectures.D1.four_flow_statement` / opg:4_flow_conjecture | `Cycle.migration.petersen.four_flow_statement_compat` |
| `Cycle.conjectures.U10.petersen_coloring_statement` / opg:petersen_coloring_conjecture | `Cycle.migration.petersen.petersen_coloring_statement_compat` |
| `Cycle.conjectures.implications_U10.external_petersen_BF_cover_statement` / no corpus row | `Cycle.migration.petersen.external_petersen_BF_cover_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py petersen --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `cycle-theory/theories/migration/mregular.v#U10Legacy.petersen_coloring_statement`.

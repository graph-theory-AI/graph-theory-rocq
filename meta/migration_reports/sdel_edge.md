# Migration report: single-edge-deletion-u11

Inputs: `meta/migration_reports/sdel_edge.spec.json` and `meta/library_primitives/single-edge-deletion-u11.json`.
Regenerate: `python3 meta/migration_report.py sdel_edge --write`.
Full evidence: `python3 meta/migration_report.py sdel_edge --details /tmp/migration-details`.

- Canonical: `GTBase.common.del_edge_set`.
- Baseline: `9e030727db115917ae077ac07a8fc6aa68661f73`.
- Scope: 2 helpers, 2 statements, 9 frozen objects, 52 recorded references.
- Source checks: 96/96 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Reconstruction.conjectures.U11.edge_reconstruction_statement` / opg:edge_reconstruction_conjecture | `Reconstruction.migration.sdel_edge.edge_reconstruction_statement_compat` |
| `Reconstruction.conjectures.implications_U11.external_whitney_line_inversion_statement` / no corpus row | `Reconstruction.migration.sdel_edge.external_whitney_line_inversion_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py sdel_edge --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `reconstruction-theory/theories/migration/simple_line_graphs.v#KellyLegacy.whitney_line_inversion_premise`, `reconstruction-theory/theories/migration/simple_line_graphs.v#ImplicationsU11Legacy.external_whitney_line_inversion_statement`.

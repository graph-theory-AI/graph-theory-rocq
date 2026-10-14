# Migration report: deletion-decks

Inputs: `meta/migration_reports/deletion_decks.spec.json` and `meta/library_primitives/deletion-decks.json`.
Regenerate: `python3 meta/migration_report.py deletion_decks --write`.
Full evidence: `python3 meta/migration_report.py deletion_decks --details /tmp/migration-details`.

- Canonical: `Reconstruction.foundations.decks.same_deck`.
- Baseline: `3bdfdae32824d4762ba8105367f7858a706a02e2`.
- Scope: 5 helpers, 4 statements, 22 frozen objects, 106 recorded references.
- Source checks: 194/194 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Reconstruction.conjectures.U11.reconstruction_statement` / opg:reconstruction_conjecture | `Reconstruction.migration.deletion_decks.reconstruction_statement_compat` |
| `Reconstruction.conjectures.U11.edge_reconstruction_statement` / opg:edge_reconstruction_conjecture | `Reconstruction.migration.deletion_decks.edge_reconstruction_statement_compat` |
| `Reconstruction.foundations.kelly.whitney_line_inversion_premise` / no corpus row | `Reconstruction.migration.deletion_decks.whitney_line_inversion_premise_compat` |
| `Reconstruction.conjectures.implications_U11.external_whitney_line_inversion_statement` / no corpus row | `Reconstruction.migration.deletion_decks.external_whitney_line_inversion_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py deletion_decks --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Digraph.conjectures.P9.same_deck`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `reconstruction-theory/theories/migration/simple_line_graphs.v#KellyLegacy.whitney_line_inversion_premise`, `reconstruction-theory/theories/migration/simple_line_graphs.v#ImplicationsU11Legacy.external_whitney_line_inversion_statement`.

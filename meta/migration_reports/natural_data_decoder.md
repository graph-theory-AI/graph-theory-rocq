# Migration report: natural-data-decoder

Inputs: `meta/migration_reports/natural_data_decoder.spec.json` and `meta/library_primitives/natural-data-decoder.json`.
Regenerate: `python3 meta/migration_report.py natural_data_decoder --write`.
Full evidence: `python3 meta/migration_report.py natural_data_decoder --details /tmp/migration-details`.

- Canonical: `GTBase.complexity.data_nth_nat`.
- Baseline: `3bdfdae32824d4762ba8105367f7858a706a02e2`.
- Scope: 2 helpers, 2 statements, 12 frozen objects, 32 recorded references.
- Source checks: 88/88 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X157.local_connectivity_k_colouring_polytime_statement` / arxiv:1505.01616#00 | `Chromatic.migration.natural_data_decoder.local_connectivity_k_colouring_polytime_statement_compat` |
| `Chromatic.conjectures.X164.linear_time_surface_triangle_free_three_colouring_output_statement` / arxiv:1601.01197#00 | `Chromatic.migration.natural_data_decoder.linear_time_surface_triangle_free_three_colouring_output_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py natural_data_decoder --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `chromatic-theory/theories/migration/natural_data_decoder.v#Legacy.x157_data_nth_nat`, `chromatic-theory/theories/migration/natural_data_decoder.v#Legacy.x164_data_nth_nat`, `chromatic-theory/theories/migration/internal_vertices.v#X157Legacy.polytime_colouring_or_none`, `chromatic-theory/theories/migration/surface_embeddable.v#Legacy.x164_linear_time_outputs_three_colouring`.

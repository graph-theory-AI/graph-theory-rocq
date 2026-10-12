# Migration report: fractional-chromatic

Inputs: `meta/migration_reports/fractional_chromatic.spec.json` and `meta/library_primitives/fractional-chromatic.json`.
Regenerate: `python3 meta/migration_report.py fractional_chromatic --write`.
Full evidence: `python3 meta/migration_report.py fractional_chromatic --details /tmp/migration-details`.

- Canonical: `Extremal.foundations.fractional_colouring.is_fractional_chromatic`.
- Baseline: `9e83cd855c2d29352812287ea06ea4d368d7aea4`.
- Scope: 1 helpers, 1 statements, 5 frozen objects, 38 recorded references.
- Source checks: 65/65 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Extremal.conjectures.D2chr.fractional_hadwiger_statement` / opg:fractional_hadwiger | `Extremal.migration.fractional_chromatic.fractional_hadwiger_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py fractional_chromatic --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Chromatic.conjectures.X130.x130_frac_chi_le`, `Extremal.foundations.circular_colouring.is_circular_chromatic`, `Extremal.conjectures.D2chr.is_colouring_mixing_threshold`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `extremal-graph-theory/theories/migration/fractional_clique_minor.v#D2chrLegacy.fractional_hadwiger_statement`.

# Migration report: strong-edge-colouring

Inputs: `meta/migration_reports/strong_pair_palettes.spec.json` and `meta/library_primitives/strong-edge-colouring.json`.
Regenerate: `python3 meta/migration_report.py strong_pair_palettes --write`.
Full evidence: `python3 meta/migration_report.py strong_pair_palettes --details /tmp/migration-details`.

- Canonical: `Chromatic.foundations.strong_pair_palettes.strong_pair_colourable`.
- Baseline: `5a107c3bc98e06e1914da17cf23ec6951cf91462`.
- Scope: 3 helpers, 1 statements, 4 frozen objects, 9 recorded references.
- Source checks: 52/52 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.U5.strong_edge_colouring_statement` / opg:strong_edge_colouring_conjecture | `Chromatic.migration.strong_pair_palettes.strong_edge_colouring_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py strong_pair_palettes --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Chromatic.conjectures.X43.x43_strong_edge_colourable`.

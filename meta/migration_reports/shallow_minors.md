# Migration report: internal-shallow-minor

Inputs: `meta/migration_reports/shallow_minors.spec.json` and `meta/library_primitives/internal-shallow-minor.json`.
Regenerate: `python3 meta/migration_report.py shallow_minors --write`.
Full evidence: `python3 meta/migration_report.py shallow_minors --details /tmp/migration-details`.

- Canonical: `Minor.foundations.shallow_minors.internal_shallow_minor`.
- Baseline: `311fdcb89dc12a78c62cb0ee6d2477896cbce9a7`.
- Scope: 2 helpers, 1 statements, 4 frozen objects, 9 recorded references.
- Source checks: 57/57 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Minor.conjectures.X220.polynomial_expansion_bounded_twin_width_statement` / arxiv:2006.09877#01 | `Minor.migration.shallow_minors.polynomial_expansion_bounded_twin_width_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py shallow_minors --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `GTMisc.conjectures.X128.x128_shallow_minor_model`, `GTMisc.conjectures.X139.x139_shallow_minor_model`.

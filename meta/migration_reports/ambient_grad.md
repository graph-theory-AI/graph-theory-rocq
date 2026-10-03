# Migration report: ambient-grad

Inputs: `meta/migration_reports/ambient_grad.spec.json` and `meta/library_primitives/ambient-grad.json`.
Regenerate: `python3 meta/migration_report.py ambient_grad --write`.
Full evidence: `python3 meta/migration_report.py ambient_grad --details /tmp/migration-details`.

- Canonical: `GTMisc.foundations.ambient_shallow_minors.ambient_grad_at_most`.
- Baseline: `30459e9b9eeebbdb5451c70c529bd2e5dfb64c99`.
- Scope: 2 helpers, 2 statements, 8 frozen objects, 28 recorded references.
- Source checks: 64/64 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `GTMisc.conjectures.X128.dvorak_cheap_balanced_separator_bounded_expansion_statement` / studies:std_dvo_k_conjecture_cheap_balanced_separators_with | `GTMisc.migration.ambient_grad.dvorak_cheap_balanced_separator_bounded_expansion_statement_compat` |
| `GTMisc.conjectures.X139.esperet_raymond_polynomial_expansion_scol_statement` / studies:std_esperet_raymond_conjecture_polynomial_expansion | `GTMisc.migration.ambient_grad.esperet_raymond_polynomial_expansion_scol_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py ambient_grad --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

# Migration report: ambient-shallow-minor

Inputs: `meta/migration_reports/ambient_shallow_minors.spec.json` and `meta/library_primitives/ambient-shallow-minor.json`.
Regenerate: `python3 meta/migration_report.py ambient_shallow_minors --write`.
Full evidence: `python3 meta/migration_report.py ambient_shallow_minors --details /tmp/migration-details`.

- Canonical: `GTMisc.foundations.ambient_shallow_minors.ambient_shallow_minor`.
- Baseline: `15e22500d394e76949607525a6bcafb9469b1287`.
- Scope: 4 helpers, 2 statements, 17 frozen objects, 36 recorded references.
- Source checks: 131/131 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `GTMisc.conjectures.X128.dvorak_cheap_balanced_separator_bounded_expansion_statement` / studies:std_dvo_k_conjecture_cheap_balanced_separators_with | `GTMisc.migration.ambient_shallow_minors.dvorak_cheap_balanced_separator_bounded_expansion_statement_compat` |
| `GTMisc.conjectures.X139.esperet_raymond_polynomial_expansion_scol_statement` / studies:std_esperet_raymond_conjecture_polynomial_expansion | `GTMisc.migration.ambient_shallow_minors.esperet_raymond_polynomial_expansion_scol_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py ambient_shallow_minors --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Infinite.conjectures.D4inf2.minor_model`, `Minor.conjectures.X200.x200_minor_model`, `Digraph.conjectures.two_extremal.sg_minor_rmap`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `graph-theory-misc/theories/migration/edge_count.v#X128Legacy.grad_at_most`, `graph-theory-misc/theories/migration/edge_count.v#X139Legacy.grad_at_most`, `graph-theory-misc/theories/migration/ambient_grad.v#X128Legacy.x128_grad_at_most`, `graph-theory-misc/theories/migration/ambient_grad.v#X139Legacy.x139_grad_at_most`.

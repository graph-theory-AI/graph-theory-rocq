# Migration report: hereditary-class

Inputs: `meta/migration_reports/hereditary_class.spec.json` and `meta/library_primitives/hereditary-class.json`.
Regenerate: `python3 meta/migration_report.py hereditary_class --write`.
Full evidence: `python3 meta/migration_report.py hereditary_class --details /tmp/migration-details`.

- Canonical: `GTBase.graph_classes.hereditary_class`.
- Baseline: `5f8211a10b7260fec67dad1450be6da41efeb1a9`.
- Scope: 5 helpers, 3 statements, 9 frozen objects, 18 recorded references.
- Source checks: 97/97 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X3.hereditary_chi_bounded_not_polynomial_statement` / arxiv:1910.00697#00 | `Chromatic.migration.graph_classes.hereditary_chi_bounded_not_polynomial_statement_compat` |
| `Minor.conjectures.X220.small_hereditary_class_bounded_twin_width_statement` / arxiv:2006.09877#00 | `Minor.migration.graph_classes.small_hereditary_class_bounded_twin_width_statement_compat` |
| `Packing.conjectures.X155.identifying_code_vc_dimension_approximation_dichotomy_statement` / arxiv:1407.5833#00 | `Packing.migration.graph_classes.identifying_code_vc_dimension_approximation_dichotomy_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py hereditary_class --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `GTMisc.conjectures.X87.x87_hereditary`, `Chromatic.conjectures.U8.vminor_closed`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `chromatic-theory/theories/migration/chi_bounded_classes.v#X3Legacy.hereditary_chi_bounded_not_polynomial_statement`.

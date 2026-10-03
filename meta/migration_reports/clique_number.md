# Migration report: clique-number

Inputs: `meta/migration_reports/clique_number.spec.json` and `meta/library_primitives/clique-number.json`.
Regenerate: `python3 meta/migration_report.py clique_number --write`.
Full evidence: `python3 meta/migration_report.py clique_number --details /tmp/migration-details`.

- Canonical: `GraphTheory.core.coloring.omega_mem`.
- Baseline: `76122100ec110f03f4b406d6b98c848a09aedf99`.
- Scope: 3 helpers, 2 statements, 12 frozen objects, 13 recorded references.
- Source checks: 85/85 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X124.dreier_torunczyk_merge_width_poly_chi_bounded_statement` / studies:std_dreier_toru_czyk_conjecture_merge_width_polynomi | `Chromatic.migration.clique_number.dreier_torunczyk_merge_width_poly_chi_bounded_statement_compat` |
| `Minor.conjectures.X121.dallard_milanic_storgel_tw_omega_tree_alpha_statement` / studies:std_dallard_milani_torgel_conjecture | `Minor.migration.clique_number.dallard_milanic_storgel_tw_omega_tree_alpha_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py clique_number --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `GTMisc.conjectures.U13.is_max_clique`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `chromatic-theory/theories/migration/chi_bounded_classes.v#X112Legacy.x112_chi_bounded`, `minor-theory/theories/migration/bag_decompositions.v#Legacy.dallard_milanic_storgel_tw_omega_tree_alpha_statement`.

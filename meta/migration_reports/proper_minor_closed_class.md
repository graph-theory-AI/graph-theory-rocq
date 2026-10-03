# Migration report: proper-minor-closed-class

Inputs: `meta/migration_reports/proper_minor_closed_class.spec.json` and `meta/library_primitives/proper-minor-closed-class.json`.
Regenerate: `python3 meta/migration_report.py proper_minor_closed_class --write`.
Full evidence: `python3 meta/migration_report.py proper_minor_closed_class --details /tmp/migration-details`.

- Canonical: `GTBase.minor_classes.proper_minor_closed_class`.
- Baseline: `6e1a1c4c719d42f6bea311812f06f61d9e49e9d3`.
- Scope: 2 helpers, 2 statements, 4 frozen objects, 9 recorded references.
- Source checks: 62/62 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X192.triangle_free_minor_closed_chromatic_additive_approx_statement` / arxiv:1707.03888#00 | `Chromatic.migration.minor_classes.triangle_free_minor_closed_chromatic_additive_approx_statement_compat` |
| `GTMisc.conjectures.X168.minor_closed_spanning_tree_polytope_linear_xc_statement` / arxiv:1604.07976#01 | `GTMisc.migration.minor_classes.minor_closed_spanning_tree_polytope_linear_xc_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py proper_minor_closed_class --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Chromatic.conjectures.U8.vminor_closed`, `Chromatic.conjectures.U8.proper_class`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `graph-theory-misc/theories/migration/spanning_trees.v#X168Legacy.minor_closed_spanning_tree_polytope_linear_xc_statement`.

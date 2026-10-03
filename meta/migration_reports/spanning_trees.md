# Migration report: spanning-tree

Inputs: `meta/migration_reports/spanning_trees.spec.json` and `meta/library_primitives/spanning-tree.json`.
Regenerate: `python3 meta/migration_report.py spanning_trees --write`.
Full evidence: `python3 meta/migration_report.py spanning_trees --details /tmp/migration-details`.

- Canonical: `GTBase.spanning_trees.fg_spanning_tree`.
- Baseline: `7848021c00cb71576fbe9b94693567ec01420b48`.
- Scope: 2 helpers, 2 statements, 9 frozen objects, 21 recorded references.
- Source checks: 93/93 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `GTMisc.conjectures.X167.fixed_surface_spanning_tree_polytope_linear_xc_statement` / arxiv:1604.07976#00 | `GTMisc.migration.spanning_trees.fixed_surface_spanning_tree_polytope_linear_xc_statement_compat` |
| `GTMisc.conjectures.X168.minor_closed_spanning_tree_polytope_linear_xc_statement` / arxiv:1604.07976#01 | `GTMisc.migration.spanning_trees.minor_closed_spanning_tree_polytope_linear_xc_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py spanning_trees --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Cycle.conjectures.U6.spanning_tree`, `Extremal.conjectures.XE1.xe1_tree`, `Extremal.conjectures.D2tur.tree_on`, `Digraph.conjectures.X2.oriented_tree`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `graph-theory-misc/theories/migration/minor_classes.v#Legacy.minor_closed_spanning_tree_polytope_linear_xc_statement`.

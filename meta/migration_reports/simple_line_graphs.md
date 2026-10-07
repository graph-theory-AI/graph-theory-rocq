# Migration report: simple-line-graph

Inputs: `meta/migration_reports/simple_line_graphs.spec.json` and `meta/library_primitives/simple-line-graph.json`.
Regenerate: `python3 meta/migration_report.py simple_line_graphs --write`.
Full evidence: `python3 meta/migration_report.py simple_line_graphs --details /tmp/migration-details`.

- Canonical: `GTBase.simple_line_graphs.simple_line_graph`.
- Baseline: `897a7d30a0137195d30ae803d0482b5df31c3869`.
- Scope: 7 helpers, 6 statements, 40 frozen objects, 90 recorded references.
- Source checks: 317/317 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X43.diamond_free_claw_free_cubic_strong_six_edge_colourable_statement` / arxiv:2511.02892#03 | `Chromatic.migration.simple_line_graphs.diamond_free_claw_free_cubic_strong_six_edge_colourable_statement_compat` |
| `Reconstruction.conjectures.U11.grahams_conjecture_on_tree_reconstruction_statement` / opg:grahams_conjecture_on_tree_reconstruction | `Reconstruction.migration.simple_line_graphs.grahams_conjecture_on_tree_reconstruction_statement_compat` |
| `Reconstruction.foundations.kelly.whitney_line_inversion_premise` / no corpus row | `Reconstruction.migration.simple_line_graphs.whitney_line_inversion_premise_compat` |
| `Reconstruction.conjectures.implications_U11.external_whitney_line_inversion_statement` / no corpus row | `Reconstruction.migration.simple_line_graphs.external_whitney_line_inversion_statement_compat` |
| `Minor.conjectures.X220.bounded_degree_induced_wall_or_line_wall_statement` / arxiv:2008.05504#01 | `Minor.migration.simple_line_graphs.bounded_degree_induced_wall_or_line_wall_statement_compat` |
| `Minor.conjectures.X220.four_family_free_logarithmic_treewidth_statement` / arxiv:2109.01310#00 | `Minor.migration.simple_line_graphs.four_family_free_logarithmic_treewidth_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py simple_line_graphs --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `GTBase.base.line_graph`, `GTMisc.conjectures.X102.x102_line_graph_of`, `Infinite.conjectures.D4legacy.iedge_vertex`, `Infinite.conjectures.D4legacy.iline_adj`, `Infinite.conjectures.D4legacy.iline_graph`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `chromatic-theory/theories/migration/induced_free.v#X43Legacy.statement`, `reconstruction-theory/theories/migration/sdel_edge.v#KellyLegacy.whitney_line_inversion_premise`, `reconstruction-theory/theories/migration/sdel_edge.v#ImplicationsU11Legacy.external_whitney_line_inversion_statement`, `minor-theory/theories/migration/model_support.v#X220Legacy.four_family_free_logarithmic_treewidth_statement`.

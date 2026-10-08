# Migration report: surface-embeddable

Inputs: `meta/migration_reports/surface_embeddable.spec.json` and `meta/library_primitives/surface-embeddable.json`.
Regenerate: `python3 meta/migration_report.py surface_embeddable --write`.
Full evidence: `python3 meta/migration_report.py surface_embeddable --details /tmp/migration-details`.

- Canonical: `GTBase.surface.surface_embeddable`.
- Baseline: `3bdfdae32824d4762ba8105367f7858a706a02e2`.
- Scope: 6 helpers, 7 statements, 19 frozen objects, 47 recorded references.
- Source checks: 170/170 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X150.gimbel_thomassen_triangle_free_surface_three_colourability_polytime_statement` / studies:std_gimbel_thomassen_problem_3 | `Chromatic.migration.surface_embeddable.gimbel_thomassen_triangle_free_surface_three_colourability_polytime_statement_compat` |
| `Chromatic.conjectures.X152.fixed_surface_four_colourability_polytime_statement` / arxiv:1010.2472#00 | `Chromatic.migration.surface_embeddable.fixed_surface_four_colourability_polytime_statement_compat` |
| `Chromatic.conjectures.X154.fixed_surface_four_colourability_polytime_duplicate_statement` / arxiv:1404.6356#00 | `Chromatic.migration.surface_embeddable.fixed_surface_four_colourability_polytime_duplicate_statement_compat` |
| `Chromatic.conjectures.X164.linear_time_surface_triangle_free_three_colouring_output_statement` / arxiv:1601.01197#00 | `Chromatic.migration.surface_embeddable.linear_time_surface_triangle_free_three_colouring_output_statement_compat` |
| `GTMisc.conjectures.X167.fixed_surface_spanning_tree_polytope_linear_xc_statement` / arxiv:1604.07976#00 | `GTMisc.migration.surface_embeddable.fixed_surface_spanning_tree_polytope_linear_xc_statement_compat` |
| `Topological.conjectures.X138.esperet_joret_surface_triangle_free_clustered_two_colouring_statement` / studies:std_esperet_joret_question_on_clustered_colouring_of | `Topological.migration.surface_embeddable.esperet_joret_surface_triangle_free_clustered_two_colouring_statement_compat` |
| `Chromatic.conjectures.X210.surface_conflict_colouring_sqrt_genus_statement` / arxiv:1803.10962#00 | `Chromatic.migration.surface_embeddable.surface_conflict_colouring_sqrt_genus_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py surface_embeddable --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `topological-graph-theory/theories/migration/monochromatic.v#X138Legacy.esperet_joret_surface_triangle_free_clustered_two_colouring_statement`, `graph-theory-misc/theories/migration/spanning_trees.v#X167Legacy.fixed_surface_spanning_tree_polytope_linear_xc_statement`.

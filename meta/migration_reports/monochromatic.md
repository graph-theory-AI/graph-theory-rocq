# Migration report: monochromatic

Inputs: `meta/migration_reports/monochromatic.spec.json` and `meta/library_primitives/monochromatic.json`.
Regenerate: `python3 meta/migration_report.py monochromatic --write`.
Full evidence: `python3 meta/migration_report.py monochromatic --details /tmp/migration-details`.

- Canonical: `GTBase.monochromatic.monochromatic_on`.
- Baseline: `47eed16af2f9575575a573f3b8a93860d47e72ca`.
- Scope: 3 helpers, 5 statements, 18 frozen objects, 70 recorded references.
- Source checks: 165/165 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X181.random_graph_clique_chromatic_tight_constant_statement` / arxiv:1612.06539#00 | `Chromatic.migration.monochromatic.random_graph_clique_chromatic_tight_constant_statement_compat` |
| `Chromatic.conjectures.X194.clustered_chromatic_minor_class_treedepth_bound_statement` / arxiv:1708.02370#00 | `Chromatic.migration.monochromatic.clustered_chromatic_minor_class_treedepth_bound_statement_compat` |
| `Chromatic.conjectures.X218.odd_minor_free_defective_clustered_treedepth_statement` / arxiv:2308.15721#00 | `Chromatic.migration.monochromatic.odd_minor_free_defective_clustered_treedepth_statement_compat` |
| `Topological.conjectures.X138.esperet_joret_surface_triangle_free_clustered_two_colouring_statement` / studies:std_esperet_joret_question_on_clustered_colouring_of | `Topological.migration.monochromatic.esperet_joret_surface_triangle_free_clustered_two_colouring_statement_compat` |
| `GTMisc.conjectures.U13.two_colouring_a_graph_without_a_monochromatic_maximu_statement` / opg:2_colouring_a_graph_without_a_monochromatic_maximum_clique | `GTMisc.migration.monochromatic.two_colouring_a_graph_without_a_monochromatic_maximu_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py monochromatic --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `GTMisc.conjectures.X20.x20_monochromatic_connected_set`, `Extremal.conjectures.XE2.xe2_monochromatic_path`, `Extremal.conjectures.XE1.xe1_monochromatic_copy_in_complete`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `chromatic-theory/theories/migration/maximal_cliques.v#X181Legacy.x181_clique_colourable`, `graph-theory-misc/theories/migration/induced_cycles.v#U13RowLegacy.two_colouring_a_graph_without_a_monochromatic_maximu_statement`.

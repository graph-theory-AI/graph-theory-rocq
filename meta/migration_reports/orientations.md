# Migration report: proper-orientations

Inputs: `meta/migration_reports/orientations.spec.json` and `meta/library_primitives/proper-orientations.json`.
Regenerate: `python3 meta/migration_report.py orientations --write`.
Full evidence: `python3 meta/migration_report.py orientations --details /tmp/migration-details`.

- Canonical: `GTBase.orientations.proper_orientation_bound`.
- Baseline: `e681570b9c330b5fb0831e3076f07a1bc2644e8f`.
- Scope: 8 helpers, 3 statements, 11 frozen objects, 14 recorded references.
- Source checks: 111/111 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X81.bipartite_proper_orientation_half_delta_constant_statement` / studies:std_ara_jo_cohen_de_rezende_havet_moura_conjecture_p | `Chromatic.migration.orientations.bipartite_proper_orientation_half_delta_constant_statement_compat` |
| `GTMisc.conjectures.X82.outerplanar_bounded_proper_orientation_number_statement` / studies:std_araujo_havet_linhares_sales_silva_conjecture_on | `GTMisc.migration.orientations.outerplanar_bounded_proper_orientation_number_statement_compat` |
| `GTMisc.conjectures.X101.planar_bounded_proper_orientation_number_statement` / studies:std_bounded_proper_orientation_number_of_planar_grap_436 | `GTMisc.migration.orientations.planar_bounded_proper_orientation_number_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py orientations --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Digraph.conjectures.XE2.xe2_orients_edge`, `Digraph.conjectures.XE2.xe2_uses_only_edges`, `Digraph.foundations.degree_balance.indeg`, `Chromatic.foundations.alon_tarsi.at_indegree`, `Chromatic.applications.alon_tarsi_triangle.at_spanning_orientation`.

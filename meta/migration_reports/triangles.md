# Migration report: triangle-set

Inputs: `meta/migration_reports/triangles.spec.json` and `meta/library_primitives/triangle-set.json`.
Regenerate: `python3 meta/migration_report.py triangles --write`.
Full evidence: `python3 meta/migration_report.py triangles --details /tmp/migration-details`.

- Canonical: `GTBase.triangles.triangle`.
- Baseline: `748b76ad48b537fef8e5cf78400423d661f869ee`.
- Scope: 7 helpers, 7 statements, 37 frozen objects, 72 recorded references.
- Source checks: 270/270 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X69.havel_distant_triangles_three_colourable_statement` / studies:std_havel_s_problem | `Chromatic.migration.triangles.havel_distant_triangles_three_colourable_statement_compat` |
| `Extremal.conjectures.X4.triangle_alpha_tau_bound_statement` / erdos:621 | `Extremal.migration.triangles.triangle_alpha_tau_bound_statement_compat` |
| `Extremal.conjectures.XE1.erdos_128_statement` / erdos:128 | `Extremal.migration.triangles.erdos_128_statement_compat` |
| `Extremal.conjectures.XE1.erdos_813_statement` / erdos:813 | `Extremal.migration.triangles.erdos_813_statement_compat` |
| `Extremal.conjectures.XE2.erdos_1009_statement` / erdos:1009 | `Extremal.migration.triangles.erdos_1009_statement_compat` |
| `Packing.conjectures.U9.triangle_packing_vs_triangle_edge_transversal_statement` / opg:triangle_packing_vs_triangle_edge_transversal | `Packing.migration.triangles.triangle_packing_vs_triangle_edge_transversal_statement_compat` |
| `Packing.conjectures.X5.triangle_packing_transversal_statement` / erdos:167 | `Packing.migration.triangles.triangle_packing_transversal_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py triangles --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Packing.conjectures.XE1.xe1_clique_edge_set`, `Hamilton.conjectures.X211.x211_has_triangle`, `Chromatic.conjectures.XE2.xe2_triangles_plus_hamilton_cycle`, `GTBase.base.triangle_free`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `extremal-graph-theory/theories/migration/edge_count.v#XE1Legacy.erdos_128_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE2Legacy.erdos_1009_statement`.

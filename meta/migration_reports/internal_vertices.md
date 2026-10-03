# Migration report: internal-vertices

Inputs: `meta/migration_reports/internal_vertices.spec.json` and `meta/library_primitives/internal-vertices.json`.
Regenerate: `python3 meta/migration_report.py internal_vertices --write`.
Full evidence: `python3 meta/migration_report.py internal_vertices --details /tmp/migration-details`.

- Canonical: `GTBase.walks_paths.seq_interior`.
- Baseline: `9e030727db115917ae077ac07a8fc6aa68661f73`.
- Scope: 6 helpers, 10 statements, 32 frozen objects, 102 recorded references.
- Source checks: 290/290 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X157.local_connectivity_k_colouring_polytime_statement` / arxiv:1505.01616#00 | `Chromatic.migration.internal_vertices.local_connectivity_k_colouring_polytime_statement_compat` |
| `GTMisc.conjectures.X172.metric_lines_bridges_counterexamples_finitely_generated_statement` / arxiv:1606.06011#01 | `GTMisc.migration.internal_vertices.metric_lines_bridges_counterexamples_finitely_generated_statement_compat` |
| `Minor.conjectures.X175.kt_subdivision_clique_count_asymptotic_statement` / arxiv:1606.06810#01 | `Minor.migration.internal_vertices.kt_subdivision_clique_count_asymptotic_statement_compat` |
| `Extremal.conjectures.XE2.erdos_915_statement` / erdos:915 | `Extremal.migration.internal_vertices.erdos_915_statement_compat` |
| `Digraph.conjectures.X2.mader_delta0_transitive_tournament_statement` / arxiv:1610.00876#00 | `Digraph.migration.internal_vertices.mader_delta0_transitive_tournament_statement_compat` |
| `Digraph.conjectures.X2.oriented_trees_delta_plus_maderian_statement` / arxiv:1610.00876#01 | `Digraph.migration.internal_vertices.oriented_trees_delta_plus_maderian_statement_compat` |
| `Digraph.conjectures.X2.delta_plus_maderian_disjoint_union_statement` / arxiv:1610.00876#02 | `Digraph.migration.internal_vertices.delta_plus_maderian_disjoint_union_statement_compat` |
| `Digraph.conjectures.X52.oriented_tree_mader_chi_linear_bound_statement` / arxiv:1610.00876#03 | `Digraph.migration.internal_vertices.oriented_tree_mader_chi_linear_bound_statement_compat` |
| `Digraph.conjectures.X90.f_subdivision_complexity_dichotomy_statement` / studies:std_bang_jensen_et_al_conjecture_f_subdivision_compl | `Digraph.migration.internal_vertices.f_subdivision_complexity_dichotomy_statement_compat` |
| `Minor.conjectures.X67.theta_triangle_free_bounded_degree_treewidth_statement` / arxiv:2001.01607#01 | `Minor.migration.internal_vertices.theta_triangle_free_bounded_degree_treewidth_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py internal_vertices --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Digraph.conjectures.X166.x166_internals`, `GTMisc.conjectures.X216.x216_internal`, `Extremal.conjectures.X98.x98_internal`, `GTMisc.conjectures.X114.x114_internal`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `minor-theory/theories/migration/consecutive_in_path.v#X67Legacy.theta`, `extremal-graph-theory/theories/migration/edge_count.v#XE2Legacy.erdos_915_statement`, `extremal-graph-theory/theories/migration/path_edges.v#XE2Legacy.erdos_915_statement`, `graph-theory-misc/theories/migration/path_edges.v#X172Legacy.one_bridge_replacement`.

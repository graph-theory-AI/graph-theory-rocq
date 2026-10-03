# Migration report: edge-set-deletion

Inputs: `meta/migration_reports/delete_edges.spec.json` and `meta/library_primitives/edge-set-deletion.json`.
Regenerate: `python3 meta/migration_report.py delete_edges --write`.
Full evidence: `python3 meta/migration_report.py delete_edges --details /tmp/migration-details`.

- Canonical: `GTBase.common.del_edge_set`.
- Baseline: `03742d181456af2cae63288593d5b6277687895c`.
- Scope: 7 helpers, 7 statements, 28 frozen objects, 54 recorded references.
- Source checks: 216/216 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X7.fixed_k_vertex_critical_edge_robust_statement` / arxiv:2310.12891#00 | `Chromatic.migration.delete_edges.fixed_k_vertex_critical_edge_robust_statement_compat` |
| `Chromatic.conjectures.X7.six_regular_four_one_graph_statement` / arxiv:2508.08703#00 | `Chromatic.migration.delete_edges.six_regular_four_one_graph_statement_compat` |
| `Chromatic.conjectures.XE1.erdos_944_statement` / erdos:944 | `Chromatic.migration.delete_edges.erdos_944_statement_compat` |
| `Extremal.conjectures.XE1.erdos_23_statement` / erdos:23 | `Extremal.migration.delete_edges.erdos_23_statement_compat` |
| `Extremal.conjectures.XE2.erdos_613_statement` / erdos:613 | `Extremal.migration.delete_edges.erdos_613_statement_compat` |
| `Extremal.conjectures.XE2.erdos_742_statement` / erdos:742 | `Extremal.migration.delete_edges.erdos_742_statement_compat` |
| `Extremal.conjectures.X191.dense_H_free_clique_blowup_subquadratic_error_statement` / arxiv:1706.05642#00 | `Extremal.migration.delete_edges.dense_H_free_clique_blowup_subquadratic_error_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py delete_edges --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Extremal.conjectures.XE1.xe1_triangle_free_diameter_completion_edges`.

# Migration report: perfect-graph

Inputs: `meta/migration_reports/perfect_graph.spec.json` and `meta/library_primitives/perfect-graph.json`.
Regenerate: `python3 meta/migration_report.py perfect_graph --write`.
Full evidence: `python3 meta/migration_report.py perfect_graph --details /tmp/migration-details`.

- Canonical: `GTBase.perfect_graphs.is_perfect_graph`.
- Baseline: `de78ea9701c5dae818ee4c897a6ea2956ff01c9a`.
- Scope: 2 helpers, 2 statements, 4 frozen objects, 9 recorded references.
- Source checks: 56/56 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Extremal.conjectures.D2ram.complete_bipartite_subgraphs_of_perfect_graphs_statement` / opg:complete_bipartite_subgraphs_of_perfect_graphs | `Extremal.migration.perfect_graphs.complete_bipartite_subgraphs_of_perfect_graphs_statement_compat` |
| `GTMisc.conjectures.X144.fox_pure_pair_perfect_graphs_statement` / studies:std_fox_s_pure_pair_conjecture_for_perfect_graphs | `GTMisc.migration.perfect_graphs.fox_pure_pair_perfect_graphs_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py perfect_graph --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Chromatic.conjectures.X3.x3_chi_omega_plus_bound`, `Chromatic.conjectures.X3.x3_alpha_omega_large_class`.

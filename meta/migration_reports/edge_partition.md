# Migration report: edge-partition

Inputs: `meta/migration_reports/edge_partition.spec.json` and `meta/library_primitives/edge-partition.json`.
Regenerate: `python3 meta/migration_report.py edge_partition --write`.
Full evidence: `python3 meta/migration_report.py edge_partition --details /tmp/migration-details`.

- Canonical: `Packing.foundations.edge_partitions.edge_partition`.
- Baseline: `9e030727db115917ae077ac07a8fc6aa68661f73`.
- Scope: 1 helpers, 3 statements, 7 frozen objects, 13 recorded references.
- Source checks: 80/80 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Packing.conjectures.X15.fair_matching_edge_partition_statement` / arxiv:1611.03196#02 | `Packing.migration.edge_partitions.fair_matching_edge_partition_statement_compat` |
| `Packing.conjectures.X18.knn_fair_perfect_matching_statement` / arxiv:1611.03196#01 | `Packing.migration.edge_partitions.knn_fair_perfect_matching_statement_compat` |
| `Packing.conjectures.X18.brualdi_stein_partial_transversal_statement` / studies:std_brualdi_stein_conjecture | `Packing.migration.edge_partitions.brualdi_stein_partial_transversal_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py edge_partition --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Packing.conjectures.X15alone.x15_edge_partition`, `Cycle.conjectures.U6.edge_partitionT`, `Cycle.conjectures.U6.edge_partition_of`, `Packing.conjectures.XE1.xe1_clique_edge_partition`, `Packing.conjectures.X18.x18_vertex_partition`.

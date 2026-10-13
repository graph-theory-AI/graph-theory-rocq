# Migration report: edge-copies

Inputs: `meta/migration_reports/edge_copies.spec.json` and `meta/library_primitives/edge-copies.json`.
Regenerate: `python3 meta/migration_report.py edge_copies --write`.
Full evidence: `python3 meta/migration_report.py edge_copies --details /tmp/migration-details`.

- Canonical: `GTBase.edge_copies.edge_image`.
- Baseline: `423936c66e0df86dff050496e86421193ebb1bcd`.
- Scope: 5 helpers, 3 statements, 15 frozen objects, 35 recorded references.
- Source checks: 139/139 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Packing.conjectures.X47.tree_decomposition_delta_edge_connected_statement` / arxiv:1507.08208#00 | `Packing.migration.edge_copies.tree_decomposition_delta_edge_connected_statement_compat` |
| `Packing.conjectures.X48.tree_decomposition_leaf_edge_connected_statement` / arxiv:1907.11600#00 | `Packing.migration.edge_copies.tree_decomposition_leaf_edge_connected_statement_compat` |
| `Cycle.conjectures.X212.barat_thomassen_tree_decomposition_statement` / bm:bm-011 | `Cycle.migration.edge_copies.barat_thomassen_tree_decomposition_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py edge_copies --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Packing.foundations.edge_partitions.edge_partition`, `Cycle.conjectures.U6.edge_partitionT`, `Cycle.conjectures.U6.edge_partition_of`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `packing-theory/theories/migration/min_degree_at_least.v#X47Legacy.tree_decomposition_delta_edge_connected_statement`, `packing-theory/theories/migration/min_degree_at_least.v#X48Legacy.tree_decomposition_leaf_edge_connected_statement`, `packing-theory/theories/migration/simple_cuts.v#X47Legacy.tree_decomposition_delta_edge_connected_statement`, `packing-theory/theories/migration/simple_cuts.v#X48Legacy.tree_decomposition_leaf_edge_connected_statement`, `packing-theory/theories/migration/simple_cuts.v#Original.x47_tree_decomposition_by_copies`.

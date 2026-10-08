# Migration report: simple-cuts

Inputs: `meta/migration_reports/simple_cuts.spec.json` and `meta/library_primitives/simple-cuts.json`.
Regenerate: `python3 meta/migration_report.py simple_cuts --write`.
Full evidence: `python3 meta/migration_report.py simple_cuts --details /tmp/migration-details`.

- Canonical: `GTBase.simple_cuts.cut_edges`.
- Baseline: `a69e27fedb17b9a509dc794b45f6e2aa5c8f4e9e`.
- Scope: 3 helpers, 3 statements, 18 frozen objects, 38 recorded references.
- Source checks: 156/156 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Packing.conjectures.X47.tree_decomposition_delta_edge_connected_statement` / arxiv:1507.08208#00 | `Packing.migration.simple_cuts.tree_decomposition_delta_edge_connected_statement_compat` |
| `Packing.conjectures.X48.tree_decomposition_leaf_edge_connected_statement` / arxiv:1907.11600#00 | `Packing.migration.simple_cuts.tree_decomposition_leaf_edge_connected_statement_compat` |
| `Cycle.conjectures.X212.bondy_linear_cycle_cubic_statement` / bm:bm-065 | `Cycle.migration.simple_cuts.bondy_linear_cycle_cubic_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py simple_cuts --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `GTBase.common.cut_size`, `GTBase.common.k_edge_connected`, `Cycle.conjectures.X184.x184_out_cut`, `Cycle.conjectures.X184.x184_directed_k_edge_connected`, `Cycle.conjectures.U10.is_odd_edge_cut`, `Cycle.conjectures.U10.contains_odd_edge_cut`, `Digraph.conjectures.X179.x179_out_cut`, `Digraph.conjectures.X179.x179_k_arc_strongly_connected`, `Digraph.conjectures.sad.outcut`, `Digraph.conjectures.sad.arc_strong`, `Digraph.conjectures.two_extremal.outcut`, `Digraph.conjectures.packing.dicut_size`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `packing-theory/theories/migration/min_degree_at_least.v#X47Legacy.tree_decomposition_delta_edge_connected_statement`, `packing-theory/theories/migration/min_degree_at_least.v#X48Legacy.tree_decomposition_leaf_edge_connected_statement`, `cycle-theory/theories/migration/genuine_cycle.v#X212Legacy.cyclically_edge_connected`, `cycle-theory/theories/migration/genuine_cycle.v#X212Legacy.bondy_linear_cycle_cubic_statement`, `packing-theory/theories/migration/edge_copies.v#X47Legacy.tree_decomposition_delta_edge_connected_statement`, `packing-theory/theories/migration/edge_copies.v#X48Legacy.tree_decomposition_leaf_edge_connected_statement`.

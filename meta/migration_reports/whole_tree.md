# Migration report: whole-tree

Inputs: `meta/migration_reports/whole_tree.spec.json` and `meta/library_primitives/whole-tree.json`.
Regenerate: `python3 meta/migration_report.py whole_tree --write`.
Full evidence: `python3 meta/migration_report.py whole_tree --details /tmp/migration-details`.

- Canonical: `GraphTheory.core.sgraph.is_tree`.
- Baseline: `6de6ce38ee3424aaffa2ef198285a3dea3e6ce1f`.
- Scope: 2 helpers, 7 statements, 14 frozen objects, 65 recorded references.
- Source checks: 171/171 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Extremal.conjectures.XE1.erdos_548_statement` / erdos:548 | `Extremal.migration.whole_tree.erdos_548_statement_compat` |
| `Extremal.conjectures.XE1.erdos_550_statement` / erdos:550 | `Extremal.migration.whole_tree.erdos_550_statement_compat` |
| `Extremal.conjectures.XE1.erdos_557_statement` / erdos:557 | `Extremal.migration.whole_tree.erdos_557_statement_compat` |
| `Extremal.conjectures.XE1.erdos_568_statement` / erdos:568 | `Extremal.migration.whole_tree.erdos_568_statement_compat` |
| `Extremal.conjectures.XE2.erdos_547_statement` / erdos:547 | `Extremal.migration.whole_tree.erdos_547_statement_compat` |
| `Extremal.conjectures.XE2.erdos_549_statement` / erdos:549 | `Extremal.migration.whole_tree.erdos_549_statement_compat` |
| `Packing.conjectures.XE1.erdos_743_statement` / erdos:743 | `Packing.migration.whole_tree.erdos_743_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py whole_tree --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `GTBase.spanning_trees.fg_spanning_tree`, `Cycle.foundations.spanning_trees.spanning_tree_edge_set`, `Extremal.conjectures.D2tur.tree_on`, `Packing.conjectures.U9.tree_contains_T`, `Digraph.conjectures.X2.oriented_tree`, `GTBase.path_trees.path_tree`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `extremal-graph-theory/theories/migration/subgraph_of.v#XE1Legacy.erdos_548_statement`, `extremal-graph-theory/theories/migration/subgraph_of.v#XE1Legacy.erdos_550_statement`, `extremal-graph-theory/theories/migration/subgraph_of.v#XE1Legacy.erdos_568_statement`, `extremal-graph-theory/theories/migration/subgraph_of.v#XE2Legacy.erdos_547_statement`, `extremal-graph-theory/theories/migration/subgraph_of.v#XE2Legacy.erdos_549_statement`, `extremal-graph-theory/theories/migration/complement.v#XE1Legacy.erdos_550_statement`, `extremal-graph-theory/theories/migration/complement.v#XE1Legacy.erdos_568_statement`, `extremal-graph-theory/theories/migration/complement.v#XE2Legacy.erdos_547_statement`, `extremal-graph-theory/theories/migration/complement.v#XE2Legacy.erdos_549_statement`, `extremal-graph-theory/theories/migration/complement.v#XE1Original.erdos_550_statement`, `extremal-graph-theory/theories/migration/complement.v#XE1Original.erdos_568_statement`, `extremal-graph-theory/theories/migration/complement.v#XE2Original.erdos_547_statement`, `extremal-graph-theory/theories/migration/complement.v#XE2Original.erdos_549_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE1Legacy.erdos_548_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE1Legacy.erdos_568_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE1Original.erdos_548_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE1Original.erdos_568_statement`, `extremal-graph-theory/theories/migration/bipartition.v#XE2Legacy.erdos_549_statement`, `extremal-graph-theory/theories/migration/bipartition.v#XE2Original.erdos_549_statement`, `extremal-graph-theory/theories/migration/bipartition.v#XE2ComplementOriginal.erdos_549_statement`, `extremal-graph-theory/theories/migration/min_degree_at_least.v#XE1Legacy.erdos_568_statement`, `extremal-graph-theory/theories/migration/min_degree_at_least.v#XE1Original.erdos_568_statement`.

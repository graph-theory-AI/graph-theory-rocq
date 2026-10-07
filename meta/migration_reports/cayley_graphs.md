# Migration report: cayley-graph

Inputs: `meta/migration_reports/cayley_graphs.spec.json` and `meta/library_primitives/cayley-graph.json`.
Regenerate: `python3 meta/migration_report.py cayley_graphs --write`.
Full evidence: `python3 meta/migration_report.py cayley_graphs --details /tmp/migration-details`.

- Canonical: `GTBase.cayley_graphs.undirected_cayley_graph`.
- Baseline: `5832ba9c3026f28df9d8dd9c689d115f644ce3b1`.
- Scope: 4 helpers, 2 statements, 13 frozen objects, 61 recorded references.
- Source checks: 122/122 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Extremal.conjectures.D2ram.ramsey_properties_of_cayley_graphs_statement` / opg:ramsey_properties_of_cayley_graphs | `Extremal.migration.cayley_graphs.ramsey_properties_of_cayley_graphs_statement_compat` |
| `Hamilton.conjectures.U2.hamiltonicity_of_cayley_graphs_statement` / opg:hamiltonicity_of_cayley_graphs | `Hamilton.migration.cayley_graphs.hamiltonicity_of_cayley_graphs_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py cayley_graphs --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Digraph.constructions.cayley.cayley`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `hamiltonicity-theory/theories/migration/cycle_edges.v#U2Legacy.four_connected_graphs_are_not_uniquely_hamiltonian_statement`, `hamiltonicity-theory/theories/migration/cycle_edges.v#U2Legacy.hamilton_decomposition_into_two`, `hamiltonicity-theory/theories/migration/cycle_edges.v#U2Legacy.uniquely_hamiltonian`, `hamiltonicity-theory/theories/migration/cycle_edges.v#X211Legacy.hamilton_cycle_edge_sets`.

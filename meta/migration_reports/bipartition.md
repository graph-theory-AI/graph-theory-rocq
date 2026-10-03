# Migration report: bipartition

Inputs: `meta/migration_reports/bipartition.spec.json` and `meta/library_primitives/bipartition.json`.
Regenerate: `python3 meta/migration_report.py bipartition --write`.
Full evidence: `python3 meta/migration_report.py bipartition --details /tmp/migration-details`.

- Canonical: `GraphTheory.connectivity.bipartition`.
- Baseline: `2e0fb67f54a33409311c2a36cdf1e1d5240e3577`.
- Scope: 7 helpers, 8 statements, 29 frozen objects, 47 recorded references.
- Source checks: 242/242 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X219.asymmetric_bipartite_list_colouring_statement` / arxiv:2004.07457#01 | `Chromatic.migration.bipartition.asymmetric_bipartite_list_colouring_statement_compat` |
| `Digraph.conjectures.X46.bipartite_digraph_outdegree_girth_statement` / arxiv:1809.08324#00 | `Digraph.migration.bipartition.bipartite_digraph_outdegree_girth_statement_compat` |
| `Digraph.conjectures.X53.bipartite_digraph_asymmetric_outdegree_girth_statement` / arxiv:1809.08324#01 | `Digraph.migration.bipartition.bipartite_digraph_asymmetric_outdegree_girth_statement_compat` |
| `Extremal.conjectures.X223.directed_sidorenko_bipartite_statement` / arxiv:2210.16971#00 | `Extremal.migration.bipartition.directed_sidorenko_bipartite_statement_compat` |
| `Extremal.conjectures.XE2.erdos_1080_statement` / erdos:1080 | `Extremal.migration.bipartition.erdos_1080_statement_compat` |
| `Extremal.conjectures.XE2.erdos_549_statement` / erdos:549 | `Extremal.migration.bipartition.erdos_549_statement_compat` |
| `Hom.conjectures.U3.weak_pentagon_statement` / opg:weak_pentagon_problem | `Hom.migration.bipartition.weak_pentagon_statement_compat` |
| `Packing.conjectures.U9.odd_cycle_transversal_in_triangle_free_graphs_statement` / opg:odd_cycle_transversal_in_triangle_free_graphs | `Packing.migration.bipartition.odd_cycle_transversal_in_triangle_free_graphs_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py bipartition --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Packing.conjectures.X15alone.bipartite`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `extremal-graph-theory/theories/migration/subgraph_of.v#XE2Legacy.erdos_1080_statement`, `extremal-graph-theory/theories/migration/subgraph_of.v#XE2Legacy.erdos_549_statement`, `extremal-graph-theory/theories/migration/complement.v#XE2Legacy.erdos_549_statement`, `extremal-graph-theory/theories/migration/complement.v#XE2Original.erdos_549_statement`.

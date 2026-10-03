# Migration report: minimum-degree-at-least

Inputs: `meta/migration_reports/min_degree_at_least.spec.json` and `meta/library_primitives/minimum-degree-at-least.json`.
Regenerate: `python3 meta/migration_report.py min_degree_at_least --write`.
Full evidence: `python3 meta/migration_report.py min_degree_at_least --details /tmp/migration-details`.

- Canonical: `GTBase.base.min_degree_at_least`.
- Baseline: `9abf440da80115caeffd299077976b48f4e07d74`.
- Scope: 12 helpers, 17 statements, 49 frozen objects, 136 recorded references.
- Source checks: 434/434 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X203.separation_choosability_min_degree_unbounded_statement` / arxiv:1802.03727#00 | `Chromatic.migration.min_degree_at_least.separation_choosability_min_degree_unbounded_statement_compat` |
| `Cycle.conjectures.XE2.erdos_752_statement` / erdos:752 | `Cycle.migration.min_degree_at_least.erdos_752_statement_compat` |
| `Extremal.conjectures.X13.large_girth_min_degree_bipartite_induced_statement` / arxiv:1802.03727#03 | `Extremal.migration.min_degree_at_least.large_girth_min_degree_bipartite_induced_statement_compat` |
| `Extremal.conjectures.X13.min_degree_forces_large_clique_or_bipartite_induced_statement` / arxiv:1802.03727#01 | `Extremal.migration.min_degree_at_least.min_degree_forces_large_clique_or_bipartite_induced_statement_compat` |
| `Extremal.conjectures.X30.triangle_free_min_degree_log_bipartite_induced_statement` / arxiv:1802.03727#02 | `Extremal.migration.min_degree_at_least.triangle_free_min_degree_log_bipartite_induced_statement_compat` |
| `Extremal.conjectures.XE1.erdos_85_statement` / erdos:85 | `Extremal.migration.min_degree_at_least.erdos_85_statement_compat` |
| `Extremal.conjectures.XE1.erdos_545_statement` / erdos:545 | `Extremal.migration.min_degree_at_least.erdos_545_statement_compat` |
| `Extremal.conjectures.XE1.erdos_566_statement` / erdos:566 | `Extremal.migration.min_degree_at_least.erdos_566_statement_compat` |
| `Extremal.conjectures.XE1.erdos_567_statement` / erdos:567 | `Extremal.migration.min_degree_at_least.erdos_567_statement_compat` |
| `Extremal.conjectures.XE1.erdos_568_statement` / erdos:568 | `Extremal.migration.min_degree_at_least.erdos_568_statement_compat` |
| `Extremal.conjectures.XE2.erdos_570_statement` / erdos:570 | `Extremal.migration.min_degree_at_least.erdos_570_statement_compat` |
| `GTMisc.conjectures.X38.min_degree_spanning_subgraph_small_degree_multiplicity_statement` / arxiv:2108.02685#01 | `GTMisc.migration.min_degree_at_least.min_degree_spanning_subgraph_small_degree_multiplicity_statement_compat` |
| `GTMisc.conjectures.X74.induced_linear_forest_caro_wei_bound_statement` / studies:std_akbari_amanihamedani_mousavi_nikpey_sheybani_con | `GTMisc.migration.min_degree_at_least.induced_linear_forest_caro_wei_bound_statement_compat` |
| `Hamilton.conjectures.X211.hypohamiltonian_minimum_degree_four_statement` / bm:bm-090 | `Hamilton.migration.min_degree_at_least.hypohamiltonian_minimum_degree_four_statement_compat` |
| `Hom.conjectures.X135.engbers_homomorphism_count_maximisation_statement` / studies:std_engbers_homomorphism_count_maximisation_conjectu | `Hom.migration.min_degree_at_least.engbers_homomorphism_count_maximisation_statement_compat` |
| `Packing.conjectures.X47.tree_decomposition_delta_edge_connected_statement` / arxiv:1507.08208#00 | `Packing.migration.min_degree_at_least.tree_decomposition_delta_edge_connected_statement_compat` |
| `Packing.conjectures.X48.tree_decomposition_leaf_edge_connected_statement` / arxiv:1907.11600#00 | `Packing.migration.min_degree_at_least.tree_decomposition_leaf_edge_connected_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py min_degree_at_least --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `GTMisc.conjectures.D7.mindeg_cn`, `Extremal.conjectures.X30.x30_induced_min_degree_log_at_least`, `Digraph.conjectures.X2.sg_degeneracy_at_least`, `Hypergraph.conjectures.X119.x119_no_isolated`, `Cycle.conjectures.XE2.xe2_proper_induced_subgraphs_min_degree_le2`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `extremal-graph-theory/theories/migration/complement.v#XE1Legacy.erdos_545_statement`, `extremal-graph-theory/theories/migration/complement.v#XE1Legacy.erdos_566_statement`, `extremal-graph-theory/theories/migration/complement.v#XE1Legacy.erdos_567_statement`, `extremal-graph-theory/theories/migration/complement.v#XE1Legacy.erdos_568_statement`, `extremal-graph-theory/theories/migration/complement.v#XE1Original.erdos_545_statement`, `extremal-graph-theory/theories/migration/complement.v#XE1Original.erdos_566_statement`, `extremal-graph-theory/theories/migration/complement.v#XE1Original.erdos_567_statement`, `extremal-graph-theory/theories/migration/complement.v#XE1Original.erdos_568_statement`, `extremal-graph-theory/theories/migration/complement.v#XE2Legacy.erdos_570_statement`, `extremal-graph-theory/theories/migration/complement.v#XE2Original.erdos_570_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE1Legacy.erdos_545_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE1Legacy.erdos_566_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE1Legacy.erdos_567_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE1Legacy.erdos_568_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE1Original.erdos_545_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE1Original.erdos_566_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE1Original.erdos_567_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE1Original.erdos_568_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE2Legacy.erdos_570_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE2Original.erdos_570_statement`, `extremal-graph-theory/theories/migration/consecutive_in_cycle.v#XE1Legacy.erdos_567_statement`, `extremal-graph-theory/theories/migration/subgraph_of.v#XE1Legacy.c4_forcing_min_degree`, `extremal-graph-theory/theories/migration/subgraph_of.v#XE1Legacy.erdos_545_statement`, `extremal-graph-theory/theories/migration/subgraph_of.v#XE1Legacy.erdos_566_statement`, `extremal-graph-theory/theories/migration/subgraph_of.v#XE1Legacy.erdos_567_statement`, `extremal-graph-theory/theories/migration/subgraph_of.v#XE1Legacy.erdos_568_statement`, `extremal-graph-theory/theories/migration/subgraph_of.v#XE2Legacy.erdos_570_statement`, `extremal-graph-theory/theories/migration/subgraph_of.v#XE1Original.erdos_567_statement`, `graph-theory-misc/theories/migration/incidence_degree.v#X38Legacy.min_degree_spanning_subgraph_small_degree_multiplicity_statement`, `cycle-theory/theories/migration/genuine_cycle.v#XE2Legacy.erdos_752_statement`, `extremal-graph-theory/theories/migration/hypercubes.v#XE1Legacy.erdos_567_statement`.

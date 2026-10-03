# Migration report: stable-set

Inputs: `meta/migration_reports/stable_sets.spec.json` and `meta/library_primitives/stable-set.json`.
Regenerate: `python3 meta/migration_report.py stable_sets --write`.
Full evidence: `python3 meta/migration_report.py stable_sets --details /tmp/migration-details`.

- Canonical: `GraphTheory.core.dom.stable`.
- Baseline: `96be00e5259f813eed101893330ee162b63f69e2`.
- Scope: 11 helpers, 17 statements, 65 frozen objects, 131 recorded references.
- Source checks: 496/496 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.XE2.erdos_758_statement` / erdos:758 | `Chromatic.migration.stable_sets.erdos_758_statement_compat` |
| `Chromatic.conjectures.XE2.erdos_762_statement` / erdos:762 | `Chromatic.migration.stable_sets.erdos_762_statement_compat` |
| `Chromatic.conjectures.XE2.erdos_922_statement` / erdos:922 | `Chromatic.migration.stable_sets.erdos_922_statement_compat` |
| `Chromatic.conjectures.X3.stable_cover_unique_induced_path_statement` / arxiv:1702.01094#01 | `Chromatic.migration.stable_sets.stable_cover_unique_induced_path_statement_compat` |
| `Chromatic.conjectures.X7.cochromatic_gap_three_statement` / arxiv:2408.02400#00 | `Chromatic.migration.stable_sets.cochromatic_gap_three_statement_compat` |
| `Extremal.conjectures.X56.c8_complement_c8_erdos_hajnal_statement` / arxiv:2102.04994#00 | `Extremal.migration.stable_sets.c8_complement_c8_erdos_hajnal_statement_compat` |
| `Extremal.conjectures.X97.bollobas_erdos_tuza_independent_set_hitting_statement` / studies:std_bollob_s_erd_s_tuza_conjecture_105 | `Extremal.migration.stable_sets.bollobas_erdos_tuza_independent_set_hitting_statement_compat` |
| `Extremal.conjectures.XE1.erdos_802_statement` / erdos:802 | `Extremal.migration.stable_sets.erdos_802_statement_compat` |
| `Extremal.conjectures.XE2.erdos_22_statement` / erdos:22 | `Extremal.migration.stable_sets.erdos_22_statement_compat` |
| `Extremal.conjectures.XE2.erdos_73_statement` / erdos:73 | `Extremal.migration.stable_sets.erdos_73_statement_compat` |
| `Extremal.conjectures.XE2.erdos_801_statement` / erdos:801 | `Extremal.migration.stable_sets.erdos_801_statement_compat` |
| `GTMisc.conjectures.X163.random_graphs_normal_whp_statement` / arxiv:1601.01129#01 | `GTMisc.migration.stable_sets.random_graphs_normal_whp_statement_compat` |
| `GTMisc.conjectures.X169.token_sliding_chordal_clique_tree_degree_polytime_statement` / arxiv:1605.00442#00 | `GTMisc.migration.stable_sets.token_sliding_chordal_clique_tree_degree_polytime_statement_compat` |
| `GTMisc.conjectures.X208.Pt_free_maximum_independent_set_polytime_statement` / arxiv:1803.05396#01 | `GTMisc.migration.stable_sets.Pt_free_maximum_independent_set_polytime_statement_compat` |
| `GTMisc.conjectures.X29.no_c5_c7_complement_c7_normal_graph_statement` / studies:std_normal_graph_conjecture_de_simone_k_rner | `GTMisc.migration.stable_sets.no_c5_c7_complement_c7_normal_graph_statement_compat` |
| `Packing.conjectures.X18.path_partition_independent_set_balance_statement` / arxiv:1611.03196#00 | `Packing.migration.stable_sets.path_partition_independent_set_balance_statement_compat` |
| `Packing.conjectures.XE1.erdos_151_statement` / erdos:151 | `Packing.migration.stable_sets.erdos_151_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py stable_sets --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Digraph.conjectures.X166.x166_stable_set`, `Digraph.conjectures.classic_core.stable`, `Digraph.conjectures.X2.x2_arc_stable`, `GTMisc.conjectures.XE2.xe2_independent3`, `Packing.conjectures.XE1.xe1_independent_set_count`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `chromatic-theory/theories/migration/consecutive_in_path.v#X3Legacy.statement`, `chromatic-theory/theories/migration/consecutive_in_path.v#X3Original.statement`, `chromatic-theory/theories/migration/path_vertices.v#X3Legacy.statement`, `chromatic-theory/theories/migration/subgraph_of.v#XE2Legacy.erdos_762_statement`, `extremal-graph-theory/theories/migration/complement.v#X56Legacy.c8_complement_c8_erdos_hajnal_statement`, `extremal-graph-theory/theories/migration/complement.v#X56Original.c8_complement_c8_erdos_hajnal_statement`, `extremal-graph-theory/theories/migration/induced_free.v#X56Legacy.statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE2Legacy.erdos_22_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE2Legacy.erdos_801_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE2Original.erdos_22_statement`, `extremal-graph-theory/theories/migration/subgraph_of.v#XE1Legacy.erdos_802_statement`, `extremal-graph-theory/theories/migration/subgraph_of.v#XE2Legacy.erdos_22_statement`, `graph-theory-misc/theories/migration/bag_decompositions.v#Legacy.x169_polytime_decides_TS_connectivity`, `graph-theory-misc/theories/migration/complement.v#X29Legacy.no_c5_c7_complement_c7_normal_graph_statement`, `packing-theory/theories/migration/maximal_cliques.v#XE1Legacy.erdos_151_statement`.

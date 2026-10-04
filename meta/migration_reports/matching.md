# Migration report: matching

Inputs: `meta/migration_reports/matching.spec.json` and `meta/library_primitives/matching.json`.
Regenerate: `python3 meta/migration_report.py matching --write`.
Full evidence: `python3 meta/migration_report.py matching --details /tmp/migration-details`.

- Canonical: `GraphTheory.connectivity.matching`.
- Baseline: `9e030727db115917ae077ac07a8fc6aa68661f73`.
- Scope: 7 helpers, 16 statements, 48 frozen objects, 260 recorded references.
- Source checks: 517/517 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Packing.conjectures.X15.fair_matching_edge_partition_statement` / arxiv:1611.03196#02 | `Packing.migration.matching.fair_matching_edge_partition_statement_compat` |
| `Packing.conjectures.X15.bipartite_matching_underrepresentation_statement` / arxiv:1611.03196#03 | `Packing.migration.matching.bipartite_matching_underrepresentation_statement_compat` |
| `Packing.conjectures.X15.bipartite_matching_underrepresentation_llm_statement` / no corpus row | `Packing.migration.matching.bipartite_matching_underrepresentation_llm_statement_compat` |
| `Packing.conjectures.X15.bipartite_matching_underrepresentation_llm2_statement` / no corpus row | `Packing.migration.matching.bipartite_matching_underrepresentation_llm2_statement_compat` |
| `Packing.conjectures.X15.bipartite_matching_underrepresentation_llm3_statement` / no corpus row | `Packing.migration.matching.bipartite_matching_underrepresentation_llm3_statement_compat` |
| `Packing.conjectures.X18.knn_fair_perfect_matching_statement` / arxiv:1611.03196#01 | `Packing.migration.matching.knn_fair_perfect_matching_statement_compat` |
| `Packing.conjectures.X18.brualdi_stein_partial_transversal_statement` / studies:std_brualdi_stein_conjecture | `Packing.migration.matching.brualdi_stein_partial_transversal_statement_compat` |
| `GTMisc.conjectures.X14.subcubic_matching_lower_bound_statement` / studies:std_biedl_demaine_duncan_fleischer_kobourov_subcubic | `GTMisc.migration.matching.subcubic_matching_lower_bound_statement_compat` |
| `Extremal.conjectures.X180.log_degree_multitasker_exists_statement` / arxiv:1611.02400#01 | `Extremal.migration.matching.log_degree_multitasker_exists_statement_compat` |
| `Digraph.conjectures.path_fas.matchingFAS_iff_dw1_statement` / no corpus row | `Digraph.migration.matching.matchingFAS_iff_dw1_statement_compat` |
| `Packing.conjectures.U9.matchings_extends_to_hamilton_cycles_in_hypercubes_statement` / opg:matchings_extends_to_hamilton_cycles_in_hypercubes | `Packing.migration.matching.matchings_extends_to_hamilton_cycles_in_hypercubes_statement_compat` |
| `Hypergraph.conjectures.U12.rysers_statement` / opg:rysers_conjecture | `Hypergraph.migration.matching.rysers_statement_compat` |
| `Hypergraph.conjectures.X6.lovasz_r_partite_matching_deletion_statement` / studies:std_lov_sz_conjecture_on_r_partite_hypergraph_matchi | `Hypergraph.migration.matching.lovasz_r_partite_matching_deletion_statement_compat` |
| `Hypergraph.conjectures.X6.r_partite_matching_deletion_tradeoff_statement` / arxiv:2505.05339#02 | `Hypergraph.migration.matching.r_partite_matching_deletion_tradeoff_statement_compat` |
| `Hypergraph.conjectures.X6.erdos_matching_extremal_formula_statement` / erdos:1020 | `Hypergraph.migration.matching.erdos_matching_extremal_formula_statement_compat` |
| `Hypergraph.conjectures.X73.regular_tripartite_hypergraph_matching_lower_bound_statement` / studies:std_aharoni_charbit_howard_conjecture_on_matchings_i | `Hypergraph.migration.matching.regular_tripartite_hypergraph_matching_lower_bound_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py matching --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Packing.conjectures.X15alone.x15_matching`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `extremal-graph-theory/theories/migration/edge_count.v#X180Legacy.log_degree_multitasker_exists_statement`, `graph-theory-misc/theories/migration/subcubic.v#X14Legacy.subcubic_matching_lower_bound_statement`, `packing-theory/theories/migration/cycle_edges.v#U9Legacy.matchings_extends_to_hamilton_cycles_in_hypercubes_statement`, `hypergraph-theory/theories/migration/incidence_degree.v#X73Legacy.regular_tripartite_hypergraph_matching_lower_bound_statement`, `hypergraph-theory/theories/migration/partite_uniform.v#U12PartiteLegacy.rysers_statement`, `hypergraph-theory/theories/migration/partite_uniform.v#X6PartiteLegacy.lovasz_r_partite_matching_deletion_statement`, `hypergraph-theory/theories/migration/partite_uniform.v#X6PartiteLegacy.r_partite_matching_deletion_tradeoff_statement`, `hypergraph-theory/theories/migration/partite_uniform.v#X73PartiteLegacy.regular_tripartite_hypergraph_matching_lower_bound_statement`, `hypergraph-theory/theories/migration/partite_uniform.v#X73PartiteOriginal.regular_tripartite_hypergraph_matching_lower_bound_statement`, `hypergraph-theory/theories/migration/uniform_hypergraph.v#X6UniformLegacy.x6_extremal_no_k_matching`, `hypergraph-theory/theories/migration/uniform_hypergraph.v#X6UniformLegacy.erdos_matching_extremal_formula_statement`, `hypergraph-theory/theories/migration/regularity.v#X73RegularLegacy.regular_tripartite_hypergraph_matching_lower_bound_statement`.

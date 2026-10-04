# Migration report: partite-uniform-hypergraph

Inputs: `meta/migration_reports/partite_uniform.spec.json` and `meta/library_primitives/partite-uniform-hypergraph.json`.
Regenerate: `python3 meta/migration_report.py partite_uniform --write`.
Full evidence: `python3 meta/migration_report.py partite_uniform --details /tmp/migration-details`.

- Canonical: `Hypergraph.foundations.hypergraph.hg_partite_uniform`.
- Baseline: `e53098e84635d8612e34e5d239fd13fe5afa9fb8`.
- Scope: 3 helpers, 6 statements, 22 frozen objects, 62 recorded references.
- Source checks: 202/202 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Hypergraph.conjectures.U12.rysers_statement` / opg:rysers_conjecture | `Hypergraph.migration.partite_uniform.rysers_statement_compat` |
| `Hypergraph.conjectures.X6.lovasz_r_partite_matching_deletion_statement` / studies:std_lov_sz_conjecture_on_r_partite_hypergraph_matchi | `Hypergraph.migration.partite_uniform.lovasz_r_partite_matching_deletion_statement_compat` |
| `Hypergraph.conjectures.X6.r_partite_matching_deletion_tradeoff_statement` / arxiv:2505.05339#02 | `Hypergraph.migration.partite_uniform.r_partite_matching_deletion_tradeoff_statement_compat` |
| `Hypergraph.conjectures.X72.ryser_intersecting_partite_cover_gap_statement` / studies:std_abu_khazneh_bar_t_pokrovskiy_szab_question_on_co | `Hypergraph.migration.partite_uniform.ryser_intersecting_partite_cover_gap_statement_compat` |
| `Hypergraph.conjectures.X73.regular_tripartite_hypergraph_matching_lower_bound_statement` / studies:std_aharoni_charbit_howard_conjecture_on_matchings_i | `Hypergraph.migration.partite_uniform.regular_tripartite_hypergraph_matching_lower_bound_statement_compat` |
| `Hypergraph.conjectures.X225.kpartite_hypergraph_turan_exponent_dmax_statement` / arxiv:2401.00359#01 | `Hypergraph.migration.partite_uniform.kpartite_hypergraph_turan_exponent_dmax_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py partite_uniform --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `hypergraph-theory/theories/migration/incidence_degree.v#X73Legacy.regular_tripartite_hypergraph_matching_lower_bound_statement`, `hypergraph-theory/theories/migration/incidence_degree.v#X225Legacy.kpartite_hypergraph_turan_exponent_dmax_statement`, `hypergraph-theory/theories/migration/uniform_hypergraph.v#X225UniformLegacy.kpartite_hypergraph_turan_exponent_dmax_statement`, `hypergraph-theory/theories/migration/uniform_hypergraph.v#X225UniformOriginal.kpartite_hypergraph_turan_exponent_dmax_statement`.

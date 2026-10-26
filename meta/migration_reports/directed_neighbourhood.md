# Migration report: directed-neighbourhood

Inputs: `meta/migration_reports/directed_neighbourhood.spec.json` and `meta/library_primitives/directed-neighbourhood.json`.
Regenerate: `python3 meta/migration_report.py directed_neighbourhood --write`.
Full evidence: `python3 meta/migration_report.py directed_neighbourhood --details /tmp/migration-details`.

- Canonical: `Digraph.foundations.neighbourhoods.Nout`.
- Baseline: `761e776c64d251a0a9af04a40628766d012aff36`.
- Scope: 6 helpers, 12 statements, 43 frozen objects, 192 recorded references.
- Source checks: 441/441 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Digraph.conjectures.classic_core.seymour_second_neighbourhood_statement` / opg:seymours_second_neighbourhood_conjecture | `Digraph.migration.directed_neighbourhood.seymour_second_neighbourhood_statement_compat` |
| `Digraph.conjectures.classic_core.long_dicycle_diregular_statement` / opg:long_directed_cycles_in_digraph_with_minimum_in_and_out_degree | `Digraph.migration.directed_neighbourhood.long_dicycle_diregular_statement_compat` |
| `Digraph.conjectures.classic_core.jackson_hamilton_small_diregular_statement` / no corpus row | `Digraph.migration.directed_neighbourhood.jackson_hamilton_small_diregular_statement_compat` |
| `Digraph.conjectures.P9.hamilton_cycle_in_small_d_diregular_graphs_statement` / opg:hamilton_cycle_in_small_d_diregular_graphs | `Digraph.migration.directed_neighbourhood.hamilton_cycle_in_small_d_diregular_graphs_statement_compat` |
| `Digraph.conjectures.P9.antidirected_trees_in_digraphs_statement` / opg:antidirected_trees_in_digraphs | `Digraph.migration.directed_neighbourhood.antidirected_trees_in_digraphs_statement_compat` |
| `Digraph.conjectures.P9.arc_disjoint_directed_cycles_in_regular_directed_gra_statement` / opg:arc_disjoint_directed_cycles_in_regular_directed_graphs | `Digraph.migration.directed_neighbourhood.arc_disjoint_directed_cycles_in_regular_directed_gra_statement_compat` |
| `Digraph.conjectures.P9.decomposing_an_even_tournament_in_directed_paths_statement` / opg:decomposing_an_even_tournament_in_directed_paths | `Digraph.migration.directed_neighbourhood.decomposing_an_even_tournament_in_directed_paths_statement_compat` |
| `Digraph.conjectures.X19.behzad_chartrand_wall_girth_regular_digraph_statement` / studies:std_behzad_chartrand_wall_conjecture_girth_of_regula | `Digraph.migration.directed_neighbourhood.behzad_chartrand_wall_girth_regular_digraph_statement_compat` |
| `Digraph.conjectures.X2.mader_delta0_transitive_tournament_statement` / arxiv:1610.00876#00 | `Digraph.migration.directed_neighbourhood.mader_delta0_transitive_tournament_statement_compat` |
| `Digraph.conjectures.X2.semidegree_oriented_paths_statement` / arxiv:2503.23191#00 | `Digraph.migration.directed_neighbourhood.semidegree_oriented_paths_statement_compat` |
| `Digraph.conjectures.X17.stein_oriented_paths_strict_semidegree_statement` / studies:std_stein_s_conjecture_on_oriented_paths | `Digraph.migration.directed_neighbourhood.stein_oriented_paths_strict_semidegree_statement_compat` |
| `Digraph.conjectures.X107.bounded_degree_acyclic_oriented_ramsey_linear_statement` / studies:std_buci_letzter_sudakov_problem_oriented_ramsey_num | `Digraph.migration.directed_neighbourhood.bounded_degree_acyclic_oriented_ramsey_linear_statement_compat` |

Source weakenings after migration: ONE-WAY source-repair certificates (`frozen -> live`), not migration equivalences; every other row keeps its exact iff: `Digraph.conjectures.P9.antidirected_trees_in_digraphs_statement` (`2 <= k ->` -> `2 <= k -> loopless D ->`; record `meta/STATEMENT_IMPROVEMENTS.md`), `Digraph.conjectures.P9.arc_disjoint_directed_cycles_in_regular_directed_gra_statement` (`diregular D k ->` -> `0 < #|D| -> diregular D k ->`; record `meta/STATEMENT_IMPROVEMENTS.md`).

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py directed_neighbourhood --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `GTBase.orientations.rel_indegree`, `Chromatic.foundations.alon_tarsi.at_indegree`, `Digraph.conjectures.P9.arcset_indeg`, `Digraph.conjectures.P9.arcset_outdeg`, `Digraph.conjectures.packing.selindeg`, `Digraph.conjectures.X86.x86_sel_indeg`, `Digraph.conjectures.path_fas.sdeg`, `Digraph.conjectures.twinwidth.red_deg`, `Infinite.conjectures.D4_unblocked.i_neighbourhood`, `Digraph.core.tournament.N_out`, `Digraph.core.tournament.N_in`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `digraph-theory/theories/migration/degree_balance.v#Legacy.x221_eulerian`, `digraph-theory/theories/migration/degree_balance.v#Legacy.cv_eulerian`, `digraph-theory/theories/migration/degree_balance.v#Legacy.Eulerian`, `digraph-theory/theories/migration/path_vertices.v#X2BoundsLegacy.mader_delta_zero_bound`, `digraph-theory/theories/migration/directed_neighbourhood.v#X107Legacy.x107_total_degree_at_most`.

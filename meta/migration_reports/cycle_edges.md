# Migration report: cycle-edges

Inputs: `meta/migration_reports/cycle_edges.spec.json` and `meta/library_primitives/cycle-edges.json`.
Regenerate: `python3 meta/migration_report.py cycle_edges --write`.
Full evidence: `python3 meta/migration_report.py cycle_edges --details /tmp/migration-details`.

- Canonical: `GTBase.walks_paths.seq_cycle_edge_set`.
- Baseline: `0a0203ee4e1ff00605e4cbfa89108dcbea0e812f`.
- Scope: 8 helpers, 11 statements, 34 frozen objects, 92 recorded references.
- Source checks: 335/335 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Cycle.conjectures.X9.proper_edge_coloured_short_cycle_statement` / arxiv:1806.00825#00 | `Cycle.migration.cycle_edges.proper_edge_coloured_short_cycle_statement_compat` |
| `Cycle.conjectures.X24.one_factorization_long_rainbow_cycle_statement` / studies:std_akbari_etesami_mahini_mahmoody_question_on_long | `Cycle.migration.cycle_edges.one_factorization_long_rainbow_cycle_statement_compat` |
| `Cycle.conjectures.XE1.erdos_184_statement` / erdos:184 | `Cycle.migration.cycle_edges.erdos_184_statement_compat` |
| `Cycle.conjectures.XE2.erdos_641_statement` / erdos:641 | `Cycle.migration.cycle_edges.erdos_641_statement_compat` |
| `Packing.conjectures.X25.kotzig_perfect_one_factorization_statement` / studies:std_kotzig_s_perfect_1_factorization_conjecture | `Packing.migration.cycle_edges.kotzig_perfect_one_factorization_statement_compat` |
| `Packing.conjectures.U9.matchings_extends_to_hamilton_cycles_in_hypercubes_statement` / opg:matchings_extends_to_hamilton_cycles_in_hypercubes | `Packing.migration.cycle_edges.matchings_extends_to_hamilton_cycles_in_hypercubes_statement_compat` |
| `GTMisc.conjectures.X216.second_hamilton_cycle_cubic_polytime_statement` / bm:bm-021 | `GTMisc.migration.cycle_edges.second_hamilton_cycle_cubic_polytime_statement_compat` |
| `Hamilton.conjectures.U2.four_connected_graphs_are_not_uniquely_hamiltonian_statement` / opg:4_connected_graphs_are_not_uniquely_hamiltonian | `Hamilton.migration.cycle_edges.four_connected_graphs_are_not_uniquely_hamiltonian_statement_compat` |
| `Hamilton.conjectures.U2.uniquely_hamiltonian_graphs_statement` / opg:uniquely_hamiltonian_graphs | `Hamilton.migration.cycle_edges.uniquely_hamiltonian_graphs_statement_compat` |
| `Hamilton.conjectures.U2.decomposing_the_prism_of_a_3_connected_cubic_planar_statement` / opg:decomposing_the_prism_of_a_3_connected_cubic_planar_graphs_in_hamilton_cycles | `Hamilton.migration.cycle_edges.decomposing_the_prism_of_a_3_connected_cubic_planar_statement_compat` |
| `Hamilton.conjectures.X211.cantoni_planar_cubic_three_hamilton_cycles_statement` / bm:bm-085 | `Hamilton.migration.cycle_edges.cantoni_planar_cubic_three_hamilton_cycles_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py cycle_edges --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Extremal.conjectures.X84.x84_cycle_edge_set`, `Digraph.conjectures.P9.cyc_arcs`, `Cycle.conjectures.U6.cyc_pairs`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `cycle-theory/theories/migration/genuine_cycle.v#X9Legacy.proper_edge_coloured_short_cycle_statement`, `cycle-theory/theories/migration/genuine_cycle.v#XE1Legacy.cycle_or_edge_piece`, `cycle-theory/theories/migration/genuine_cycle.v#XE2Legacy.erdos_641_statement`, `cycle-theory/theories/migration/perfect_matching.v#X24Legacy.one_factorization_long_rainbow_cycle_statement`, `packing-theory/theories/migration/matching.v#U9MatchingLegacy.matchings_extends_to_hamilton_cycles_in_hypercubes_statement`, `packing-theory/theories/migration/hypercubes.v#U9Legacy.matchings_extends_to_hamilton_cycles_in_hypercubes_statement`.

# Migration report: genuine-cycle

Inputs: `meta/migration_reports/genuine_cycle.spec.json` and `meta/library_primitives/genuine-cycle.json`.
Regenerate: `python3 meta/migration_report.py genuine_cycle --write`.
Full evidence: `python3 meta/migration_report.py genuine_cycle --details /tmp/migration-details`.

- Canonical: `GTBase.walks_paths.seq_cycle`.
- Baseline: `00d6bb3a80759b365fffab282d47603510bf839e`.
- Scope: 8 helpers, 17 statements, 51 frozen objects, 149 recorded references.
- Source checks: 437/437 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.XE2.erdos_58_statement` / erdos:58 | `Chromatic.migration.genuine_cycle.erdos_58_statement_compat` |
| `Chromatic.conjectures.XE2.erdos_751_statement` / erdos:751 | `Chromatic.migration.genuine_cycle.erdos_751_statement_compat` |
| `Chromatic.conjectures.XE2.erdos_1091_statement` / erdos:1091 | `Chromatic.migration.genuine_cycle.erdos_1091_statement_compat` |
| `Cycle.conjectures.X212.smith_two_longest_cycles_statement` / bm:bm-064 | `Cycle.migration.genuine_cycle.smith_two_longest_cycles_statement_compat` |
| `Cycle.conjectures.X212.bondy_linear_cycle_cubic_statement` / bm:bm-065 | `Cycle.migration.genuine_cycle.bondy_linear_cycle_cubic_statement_compat` |
| `Cycle.conjectures.X212.birmele_long_cycle_transversal_statement` / bm:bm-066 | `Cycle.migration.genuine_cycle.birmele_long_cycle_transversal_statement_compat` |
| `Cycle.conjectures.X9.proper_edge_coloured_short_cycle_statement` / arxiv:1806.00825#00 | `Cycle.migration.genuine_cycle.proper_edge_coloured_short_cycle_statement_compat` |
| `Cycle.conjectures.X9.min_degree_three_linearly_many_chords_cycle_statement` / arxiv:2502.04726#03 | `Cycle.migration.genuine_cycle.min_degree_three_linearly_many_chords_cycle_statement_compat` |
| `Cycle.conjectures.XE1.erdos_184_statement` / erdos:184 | `Cycle.migration.genuine_cycle.erdos_184_statement_compat` |
| `Cycle.conjectures.XE2.erdos_641_statement` / erdos:641 | `Cycle.migration.genuine_cycle.erdos_641_statement_compat` |
| `Cycle.conjectures.XE2.erdos_71_statement` / erdos:71 | `Cycle.migration.genuine_cycle.erdos_71_statement_compat` |
| `Cycle.conjectures.XE2.erdos_752_statement` / erdos:752 | `Cycle.migration.genuine_cycle.erdos_752_statement_compat` |
| `Cycle.conjectures.XE2.erdos_815_statement` / erdos:815 | `Cycle.migration.genuine_cycle.erdos_815_statement_compat` |
| `Extremal.conjectures.XE2.erdos_767_statement` / erdos:767 | `Extremal.migration.genuine_cycle.erdos_767_statement_compat` |
| `GTMisc.conjectures.X113.coarse_erdos_posa_cycles_forest_statement` / studies:std_chudnovsky_seymour_coarse_erd_s_p_sa_conjecture | `GTMisc.migration.genuine_cycle.coarse_erdos_posa_cycles_forest_statement_compat` |
| `GTMisc.conjectures.XE1.erdos_883_statement` / erdos:883 | `GTMisc.migration.genuine_cycle.erdos_883_statement_compat` |
| `Digraph.conjectures.XE2.erdos_1006_statement` / erdos:1006 | `Digraph.migration.genuine_cycle.erdos_1006_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py genuine_cycle --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `GTBase.common.hamiltonian_cycle`, `Hamilton.conjectures.U2.hamiltonian_cycle`, `Cycle.conjectures.X10.x10_rainbow_cycle`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `chromatic-theory/theories/migration/consecutive_in_cycle.v#XE1Legacy.odd_cycle_with_diagonals`, `chromatic-theory/theories/migration/subgraph_of.v#XE2Legacy.erdos_1091_statement`, `chromatic-theory/theories/migration/subgraph_of.v#XE2Legacy.erdos_58_statement`, `cycle-theory/theories/migration/consecutive_in_cycle.v#X9Legacy.min_degree_three_linearly_many_chords_cycle_statement`, `extremal-graph-theory/theories/migration/consecutive_in_cycle.v#XE2Legacy.no_cycle_with_incident_chords`, `graph-theory-misc/theories/migration/path_vertices.v#X113Legacy.has_k_distant_cycles`, `graph-theory-misc/theories/migration/path_vertices.v#X113Legacy.is_forest_after`, `cycle-theory/theories/migration/cycle_edges.v#X9Legacy.proper_edge_coloured_short_cycle_statement`, `cycle-theory/theories/migration/cycle_edges.v#XE1Legacy.cycle_or_edge_piece`, `cycle-theory/theories/migration/cycle_edges.v#XE2Legacy.erdos_641_statement`, `cycle-theory/theories/migration/cycle_vertices.v#X212Legacy.smith_two_longest_cycles_statement`, `cycle-theory/theories/migration/longest_cycle.v#Legacy.x212_longest_cycle`, `extremal-graph-theory/theories/migration/edge_count.v#XE2Legacy.incident_chord_extremal`, `cycle-theory/theories/migration/min_degree_at_least.v#XE2Legacy.erdos_752_statement`.

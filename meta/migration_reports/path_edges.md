# Migration report: path-edges

Inputs: `meta/migration_reports/path_edges.spec.json` and `meta/library_primitives/path-edges.json`.
Regenerate: `python3 meta/migration_report.py path_edges --write`.
Full evidence: `python3 meta/migration_report.py path_edges --details /tmp/migration-details`.

- Canonical: `GTBase.walks_paths.seq_edge_set`.
- Baseline: `048c768adce0cfcbf5b5a5763d71fc8daf483db8`.
- Scope: 5 helpers, 7 statements, 31 frozen objects, 81 recorded references.
- Source checks: 284/284 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `GTMisc.conjectures.X14.andersen_rainbow_path_statement` / studies:std_andersen_s_conjecture | `GTMisc.migration.path_edges.andersen_rainbow_path_statement_compat` |
| `GTMisc.conjectures.X62.rainbow_paths_linear_edge_cover_statement` / arxiv:2301.08707#01 | `GTMisc.migration.path_edges.rainbow_paths_linear_edge_cover_statement_compat` |
| `GTMisc.conjectures.X172.metric_lines_bridges_counterexamples_finitely_generated_statement` / arxiv:1606.06011#01 | `GTMisc.migration.path_edges.metric_lines_bridges_counterexamples_finitely_generated_statement_compat` |
| `Minor.conjectures.U7.coloring_and_immersion_statement` / opg:coloring_and_immersion | `Minor.migration.path_edges.coloring_and_immersion_statement_compat` |
| `Minor.conjectures.X174.kt_immersion_clique_count_extremal_statement` / arxiv:1606.06810#00 | `Minor.migration.path_edges.kt_immersion_clique_count_extremal_statement_compat` |
| `Extremal.conjectures.XE2.erdos_915_statement` / erdos:915 | `Extremal.migration.path_edges.erdos_915_statement_compat` |
| `Packing.conjectures.X178.gallai_odd_semiclique_path_decomposition_statement` / arxiv:1609.06257#00 | `Packing.migration.path_edges.gallai_odd_semiclique_path_decomposition_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py path_edges --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Cycle.conjectures.X9.x9_cycle_edges`, `Cycle.conjectures.X24.x24_cycle_edge_seq`, `Packing.conjectures.X25.x25_cycle_edge_seq`, `GTMisc.conjectures.X216.x216_cycle_edges`, `Cycle.conjectures.XE1.xe1_cycle_edges`, `Chromatic.conjectures.U5.edge_colour_seq`, `Cycle.conjectures.X10.x10_rainbow_cycle`, `Digraph.conjectures.P9.dipath_arcs`, `Extremal.conjectures.D2tur.ham_path_edges`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `extremal-graph-theory/theories/migration/internal_vertices.v#XE2Legacy.statement`, `graph-theory-misc/theories/migration/edge_colourings.v#X14Legacy.andersen_rainbow_path_statement`, `graph-theory-misc/theories/migration/edge_colourings.v#X62Legacy.rainbow_paths_linear_edge_cover_statement`, `graph-theory-misc/theories/migration/internal_vertices.v#X172Legacy.one_bridge_replacement`, `graph-theory-misc/theories/migration/simple_path.v#X14Legacy.rainbow_path`, `graph-theory-misc/theories/migration/simple_path.v#X62Legacy.rainbow_paths_linear_edge_cover_statement`, `packing-theory/theories/migration/simple_path.v#X178Legacy.path_decomposition_at_most`, `extremal-graph-theory/theories/migration/edge_count.v#XE2Legacy.erdos_915_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE2Original.erdos_915_statement`, `minor-theory/theories/migration/clique_counts.v#X174Legacy.kt_immersion_clique_count_extremal_statement`.

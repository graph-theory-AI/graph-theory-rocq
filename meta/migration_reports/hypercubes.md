# Migration report: hypercube

Inputs: `meta/migration_reports/hypercubes.spec.json` and `meta/library_primitives/hypercube.json`.
Regenerate: `python3 meta/migration_report.py hypercubes --write`.
Full evidence: `python3 meta/migration_report.py hypercubes --details /tmp/migration-details`.

- Canonical: `GTBase.hypercubes.product_hypercube`.
- Baseline: `f5d2d3a0652fe3858fa8a22d9edd0d297bac8a2a`.
- Scope: 3 helpers, 6 statements, 29 frozen objects, 110 recorded references.
- Source checks: 269/269 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Extremal.conjectures.XE1.erdos_1035_statement` / erdos:1035 | `Extremal.migration.hypercubes.erdos_1035_statement_compat` |
| `Extremal.conjectures.XE1.erdos_567_statement` / erdos:567 | `Extremal.migration.hypercubes.erdos_567_statement_compat` |
| `Topological.conjectures.D3cr.the_crossing_number_of_the_hypercube_statement` / opg:the_crossing_number_of_the_hypercube | `Topological.migration.hypercubes.the_crossing_number_of_the_hypercube_statement_compat` |
| `Packing.conjectures.U9.matchings_extends_to_hamilton_cycles_in_hypercubes_statement` / opg:matchings_extends_to_hamilton_cycles_in_hypercubes | `Packing.migration.hypercubes.matchings_extends_to_hamilton_cycles_in_hypercubes_statement_compat` |
| `Packing.conjectures.U9.weak_saturation_of_the_cube_in_the_clique_statement` / opg:weak_saturation_of_the_cube_in_the_clique | `Packing.migration.hypercubes.weak_saturation_of_the_cube_in_the_clique_statement_compat` |
| `Packing.conjectures.X226.subcube_partition_count_ratio_subexponential_statement` / arxiv:2401.00299#04 | `Packing.migration.hypercubes.subcube_partition_count_ratio_subexponential_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py hypercubes --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `GTBase.base.graph_power`, `Extremal.conjectures.XE2.xe2_cube_square_floor`, `Packing.conjectures.X226.x226_subcube_dim`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `extremal-graph-theory/theories/migration/complement.v#XE1Legacy.erdos_567_statement`, `extremal-graph-theory/theories/migration/complement.v#XE1Original.erdos_567_statement`, `extremal-graph-theory/theories/migration/consecutive_in_cycle.v#XE1Legacy.erdos_567_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE1Legacy.erdos_567_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE1Original.erdos_567_statement`, `extremal-graph-theory/theories/migration/hypercubes.v#Legacy.xe1_hypercube`, `extremal-graph-theory/theories/migration/min_degree_at_least.v#XE1Legacy.erdos_567_statement`, `extremal-graph-theory/theories/migration/min_degree_at_least.v#XE1Original.erdos_567_statement`, `extremal-graph-theory/theories/migration/subgraph_of.v#XE1Legacy.erdos_1035_statement`, `extremal-graph-theory/theories/migration/subgraph_of.v#XE1Legacy.erdos_567_statement`, `extremal-graph-theory/theories/migration/subgraph_of.v#XE1Original.erdos_567_statement`, `topological-graph-theory/theories/migration/hypercubes.v#Legacy.hypercube`, `packing-theory/theories/migration/cycle_edges.v#U9Legacy.matchings_extends_to_hamilton_cycles_in_hypercubes_statement`, `packing-theory/theories/migration/matching.v#U9MatchingLegacy.matchings_extends_to_hamilton_cycles_in_hypercubes_statement`, `packing-theory/theories/migration/matching.v#U9MatchingOriginal.matchings_extends_to_hamilton_cycles_in_hypercubes_statement`.

# Migration report: multigraph-regularity

Inputs: `meta/migration_reports/mregular.spec.json` and `meta/library_primitives/multigraph-regularity.json`.
Regenerate: `python3 meta/migration_report.py mregular --write`.
Full evidence: `python3 meta/migration_report.py mregular --details /tmp/migration-details`.

- Canonical: `GTBase.base.mregular`.
- Baseline: `58f2862aa45b932cebb4cc59401a6b16f5d0c82a`.
- Scope: 3 helpers, 11 statements, 16 frozen objects, 64 recorded references.
- Source checks: 190/190 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.U5.three_edge_coloring_statement` / opg:3_edge_coloring_conjecture | `Chromatic.migration.mregular.three_edge_coloring_statement_compat` |
| `Chromatic.conjectures.U5.universal_steiner_triple_systems_statement` / opg:universal_steiner_triple_systems | `Chromatic.migration.mregular.universal_steiner_triple_systems_statement_compat` |
| `Cycle.conjectures.U6.cycle_double_covers_containing_predefined_2_regular_statement` / opg:cycle_double_covers_containing_predefined_2_regular_subgraphs | `Cycle.migration.mregular.cycle_double_covers_containing_predefined_2_regular_statement_compat` |
| `Cycle.conjectures.U6.three_decomposition_statement` / opg:3_decomposition_conjecture | `Cycle.migration.mregular.three_decomposition_statement_compat` |
| `Cycle.conjectures.U6.odd_cycles_and_low_oddness_statement` / opg:odd_cycles_and_low_oddness | `Cycle.migration.mregular.odd_cycles_and_low_oddness_statement_compat` |
| `Cycle.conjectures.U6.strong_5_cycle_double_cover_statement` / opg:strong_5_cycle_double_cover_conjecture | `Cycle.migration.mregular.strong_5_cycle_double_cover_statement_compat` |
| `Cycle.conjectures.U10.intersecting_two_perfect_matchings_statement` / opg:intersecting_two_perfect_matchings | `Cycle.migration.mregular.intersecting_two_perfect_matchings_statement_compat` |
| `Cycle.conjectures.U10.petersen_coloring_statement` / opg:petersen_coloring_conjecture | `Cycle.migration.mregular.petersen_coloring_statement_compat` |
| `Cycle.conjectures.U10.the_berge_fulkerson_statement` / opg:the_berge_fulkerson_conjecture | `Cycle.migration.mregular.the_berge_fulkerson_statement_compat` |
| `Cycle.conjectures.implications_U6.external_cdc_cubic_2connected_reduction_statement` / no corpus row | `Cycle.migration.mregular.external_cdc_cubic_2connected_reduction_statement_compat` |
| `Cycle.conjectures.implications_U6.external_five_even_cover_cubic_reduction_statement` / no corpus row | `Cycle.migration.mregular.external_five_even_cover_cubic_reduction_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py mregular --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `GTBase.base.regular`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `cycle-theory/theories/migration/spanning_trees.v#U6Legacy.three_decomposition_statement`.

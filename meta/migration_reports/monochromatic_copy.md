# Migration report: monochromatic-copy

Inputs: `meta/migration_reports/monochromatic_copy.spec.json` and `meta/library_primitives/monochromatic-copy.json`.
Regenerate: `python3 meta/migration_report.py monochromatic_copy --write`.
Full evidence: `python3 meta/migration_report.py monochromatic_copy --details /tmp/migration-details`.

- Canonical: `Hypergraph.foundations.hypergraph_copies.hg_mono_copy`.
- Baseline: `598d668fa9225c8271852c856ce3990c7fa7890e`.
- Scope: 3 helpers, 3 statements, 29 frozen objects, 61 recorded references.
- Source checks: 195/195 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Hypergraph.conjectures.X108.three_uniform_degenerate_hypergraph_ramsey_linear_statement` / studies:std_burr_erd_s_conjecture_for_3_uniform_hypergraphs | `Hypergraph.migration.monochromatic_copy.three_uniform_degenerate_hypergraph_ramsey_linear_statement_compat` |
| `Hypergraph.conjectures.X117.conlon_fox_rodl_hedgehog_ramsey_statement` / studies:std_conlon_fox_r_dl_question_on_hedgehog_ramsey_numb | `Hypergraph.migration.monochromatic_copy.conlon_fox_rodl_hedgehog_ramsey_statement_compat` |
| `Hypergraph.conjectures.X119.conlon_fox_sudakov_three_uniform_ramsey_tower_statement` / studies:std_conlon_fox_sudakov_problem_on_3_uniform_hypergra | `Hypergraph.migration.monochromatic_copy.conlon_fox_sudakov_three_uniform_ramsey_tower_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py monochromatic_copy --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `hypergraph-theory/theories/migration/incidence_degree.v#X108Legacy.three_uniform_degenerate_hypergraph_ramsey_linear_statement`, `hypergraph-theory/theories/migration/uniform_hypergraph.v#X108UniformLegacy.three_uniform_degenerate_hypergraph_ramsey_linear_statement`, `hypergraph-theory/theories/migration/uniform_hypergraph.v#X108UniformOriginal.three_uniform_degenerate_hypergraph_ramsey_linear_statement`, `hypergraph-theory/theories/migration/uniform_hypergraph.v#X119UniformLegacy.conlon_fox_sudakov_three_uniform_ramsey_tower_statement`, `hypergraph-theory/theories/migration/forces_mono.v#X108ForcingLegacy.x108_two_colour_ramsey_at_most`, `hypergraph-theory/theories/migration/forces_mono.v#X117ForcingLegacy.x117_forces_mono`, `hypergraph-theory/theories/migration/forces_mono.v#X119ForcingLegacy.x119_forces_mono`, `hypergraph-theory/theories/migration/hedgehog.v#X117HedgehogLegacy.x117_ramsey_number`, `hypergraph-theory/theories/migration/hedgehog.v#X117HedgehogLegacy.conlon_fox_rodl_hedgehog_ramsey_statement`.

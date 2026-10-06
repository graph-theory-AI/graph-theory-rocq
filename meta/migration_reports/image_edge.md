# Migration report: image-edge

Inputs: `meta/migration_reports/image_edge.spec.json` and `meta/library_primitives/image-edge.json`.
Regenerate: `python3 meta/migration_report.py image_edge --write`.
Full evidence: `python3 meta/migration_report.py image_edge --details /tmp/migration-details`.

- Canonical: `mathcomp.boot.finset.imset`.
- Baseline: `aa1f6f38d309d50725f98b5e1b42dff6414af30b`.
- Scope: 3 helpers, 3 statements, 20 frozen objects, 71 recorded references.
- Source checks: 151/151 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Hypergraph.conjectures.X108.three_uniform_degenerate_hypergraph_ramsey_linear_statement` / studies:std_burr_erd_s_conjecture_for_3_uniform_hypergraphs | `Hypergraph.migration.image_edge.three_uniform_degenerate_hypergraph_ramsey_linear_statement_compat` |
| `Hypergraph.conjectures.X117.conlon_fox_rodl_hedgehog_ramsey_statement` / studies:std_conlon_fox_r_dl_question_on_hedgehog_ramsey_numb | `Hypergraph.migration.image_edge.conlon_fox_rodl_hedgehog_ramsey_statement_compat` |
| `Hypergraph.conjectures.X119.conlon_fox_sudakov_three_uniform_ramsey_tower_statement` / studies:std_conlon_fox_sudakov_problem_on_3_uniform_hypergra | `Hypergraph.migration.image_edge.conlon_fox_sudakov_three_uniform_ramsey_tower_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py image_edge --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `hypergraph-theory/theories/migration/incidence_degree.v#X108Legacy.three_uniform_degenerate_hypergraph_ramsey_linear_statement`, `hypergraph-theory/theories/migration/uniform_hypergraph.v#X108UniformLegacy.three_uniform_degenerate_hypergraph_ramsey_linear_statement`, `hypergraph-theory/theories/migration/uniform_hypergraph.v#X108UniformOriginal.three_uniform_degenerate_hypergraph_ramsey_linear_statement`, `hypergraph-theory/theories/migration/uniform_hypergraph.v#X119UniformLegacy.conlon_fox_sudakov_three_uniform_ramsey_tower_statement`, `hypergraph-theory/theories/migration/monochromatic_copy.v#X108CopyLegacy.x108_monochromatic_copy`, `hypergraph-theory/theories/migration/monochromatic_copy.v#X117CopyLegacy.x117_monochromatic_copy`, `hypergraph-theory/theories/migration/monochromatic_copy.v#X119CopyLegacy.x119_monochromatic_copy`, `hypergraph-theory/theories/migration/forces_mono.v#X108ForcingLegacy.x108_two_colour_ramsey_at_most`, `hypergraph-theory/theories/migration/forces_mono.v#X117ForcingLegacy.x117_forces_mono`, `hypergraph-theory/theories/migration/forces_mono.v#X119ForcingLegacy.x119_forces_mono`, `hypergraph-theory/theories/migration/hedgehog.v#X117HedgehogLegacy.conlon_fox_rodl_hedgehog_ramsey_statement`, `hypergraph-theory/theories/migration/hedgehog.v#X117HedgehogLegacy.x117_ramsey_number`.

# Migration report: minor-model

Inputs: `meta/migration_reports/minor_models.spec.json` and `meta/library_primitives/minor-model.json`.
Regenerate: `python3 meta/migration_report.py minor_models --write`.
Full evidence: `python3 meta/migration_report.py minor_models --details /tmp/migration-details`.

- Canonical: `GraphTheory.core.minor.minor_rmap`.
- Baseline: `35b6b165295fb373d864d646d74284c4751dae65`.
- Scope: 2 helpers, 6 statements, 13 frozen objects, 35 recorded references.
- Source checks: 133/133 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Minor.conjectures.X200.planar_H_model_erdos_posa_oklogk_statement` / arxiv:1710.06282#00 | `Minor.migration.minor_models.planar_H_model_erdos_posa_oklogk_statement_compat` |
| `Digraph.conjectures.two_extremal.conjecture_P` / derived:drv_twoext_conjp | `Digraph.migration.minor_models.conjecture_P_compat` |
| `Digraph.conjectures.P9.large_acyclic_induced_subdigraph_in_a_planar_oriente_statement` / opg:large_acyclic_induced_subdigraph_in_a_planar_oriented_graph | `Digraph.migration.minor_models.large_acyclic_induced_subdigraph_in_a_planar_oriente_statement_compat` |
| `Digraph.conjectures.P9.oriented_chromatic_number_of_planar_graphs_statement` / opg:oriented_chromatic_number_of_planar_graphs | `Digraph.migration.minor_models.oriented_chromatic_number_of_planar_graphs_statement_compat` |
| `Digraph.conjectures.P9.partitioning_planar_digraphs_statement` / opg:partitioning_planar_digraphs | `Digraph.migration.minor_models.partitioning_planar_digraphs_statement_compat` |
| `Digraph.conjectures.colouring_variants.oriented_chromatic_planar_bounded_statement` / no corpus row | `Digraph.migration.minor_models.oriented_chromatic_planar_bounded_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py minor_models --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Infinite.conjectures.D4inf2.minor_model`, `Extremal.conjectures.X98.x98_model_vertex`, `GTMisc.conjectures.X114.x114_model_vertex`, `Minor.foundations.containment.sdm_covers`, `Minor.conjectures.X220.x220_shallow_minor`.

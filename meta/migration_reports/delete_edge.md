# Migration report: single-edge-deletion

Inputs: `meta/migration_reports/delete_edge.spec.json` and `meta/library_primitives/single-edge-deletion.json`.
Regenerate: `python3 meta/migration_report.py delete_edge --write`.
Full evidence: `python3 meta/migration_report.py delete_edge --details /tmp/migration-details`.

- Canonical: `GTBase.common.del_edge_set`.
- Baseline: `dbee364e6be7ac2e9a8e7edecbb1ff5f0878c8c0`.
- Scope: 4 helpers, 3 statements, 21 frozen objects, 39 recorded references.
- Source checks: 147/147 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X64.finite_bridgeless_cubic_two_homogeneous_exceptions_statement` / arxiv:2511.02892#05 | `Chromatic.migration.delete_edge.finite_bridgeless_cubic_two_homogeneous_exceptions_statement_compat` |
| `Extremal.conjectures.X60.induced_saturation_even_cycle_polynomial_size_statement` / arxiv:2505.24100#01 | `Extremal.migration.delete_edge.induced_saturation_even_cycle_polynomial_size_statement_compat` |
| `Extremal.conjectures.X61.infinite_family_without_finite_induced_saturation_statement` / arxiv:2506.08810#00 | `Extremal.migration.delete_edge.infinite_family_without_finite_induced_saturation_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py delete_edge --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Reconstruction.conjectures.U11.sde_rel`, `Reconstruction.conjectures.U11.sdel_edge`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `chromatic-theory/theories/migration/simple_edges.v#X64Legacy.bridgeless`, `extremal-graph-theory/theories/migration/induced_free.v#X61Legacy.induced_saturated`, `extremal-graph-theory/theories/migration/induced_free.v#X61Original.induced_saturated`.

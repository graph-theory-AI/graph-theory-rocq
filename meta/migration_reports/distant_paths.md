# Migration report: distant-paths

Inputs: `meta/migration_reports/distant_paths.spec.json` and `meta/library_primitives/distant-paths.json`.
Regenerate: `python3 meta/migration_report.py distant_paths --write`.
Full evidence: `python3 meta/migration_report.py distant_paths --details /tmp/migration-details`.

- Canonical: `GTBase.distant_paths.pairwise_distant_seqs`.
- Baseline: `058da18a5f7867ad874d93cc2d57056dc25537ba`.
- Scope: 7 helpers, 5 statements, 45 frozen objects, 89 recorded references.
- Source checks: 292/292 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `GTMisc.conjectures.X39.coarse_menger_ball_separator_statement` / studies:std_coarse_menger_conjecture_georgakopoulos_papasogl | `GTMisc.migration.distant_paths.coarse_menger_ball_separator_statement_compat` |
| `GTMisc.conjectures.X40.coarse_menger_distance_two_separator_statement` / arxiv:2508.14332#00 | `GTMisc.migration.distant_paths.coarse_menger_distance_two_separator_statement_compat` |
| `GTMisc.conjectures.X116.coarse_menger_paths_bounded_separator_statement` / studies:std_coarse_menger_conjecture | `GTMisc.migration.distant_paths.coarse_menger_paths_bounded_separator_statement_compat` |
| `GTMisc.conjectures.X146.geelen_coarse_gallai_A_paths_statement` / studies:std_geelen_s_coarse_gallai_conjecture | `GTMisc.migration.distant_paths.geelen_coarse_gallai_A_paths_statement_compat` |
| `Packing.conjectures.X26.bounded_degree_distant_induced_menger_statement` / arxiv:2309.07905#00 | `Packing.migration.distant_paths.bounded_degree_distant_induced_menger_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py distant_paths --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `GTMisc.conjectures.X113.x113_pairwise_distant_cycles`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `graph-theory-misc/theories/migration/set_path.v#X39Legacy.has_k_distant_xy_paths`, `graph-theory-misc/theories/migration/set_path.v#X116Legacy.has_k_distant_ST_paths`, `packing-theory/theories/migration/set_path.v#X26Legacy.has_k_distant_xy_paths`, `graph-theory-misc/theories/migration/set_separators.v#X39Legacy.coarse_menger_ball_separator_statement`, `graph-theory-misc/theories/migration/set_separators.v#X40Legacy.coarse_menger_distance_two_separator_statement`, `packing-theory/theories/migration/set_separators.v#X26Legacy.bounded_degree_distant_induced_menger_statement`.

# Migration report: set-path

Inputs: `meta/migration_reports/set_path.spec.json` and `meta/library_primitives/set-path.json`.
Regenerate: `python3 meta/migration_report.py set_path --write`.
Full evidence: `python3 meta/migration_report.py set_path --details /tmp/migration-details`.

- Canonical: `GTBase.walks_paths.seq_set_path`.
- Baseline: `fbf33a001157c4b734e98ddd3968d4e13d54602f`.
- Scope: 4 helpers, 5 statements, 36 frozen objects, 112 recorded references.
- Source checks: 265/265 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `GTMisc.conjectures.X39.coarse_menger_ball_separator_statement` / studies:std_coarse_menger_conjecture_georgakopoulos_papasogl | `GTMisc.migration.set_path.coarse_menger_ball_separator_statement_compat` |
| `GTMisc.conjectures.X40.coarse_menger_distance_two_separator_statement` / arxiv:2508.14332#00 | `GTMisc.migration.set_path.coarse_menger_distance_two_separator_statement_compat` |
| `GTMisc.conjectures.X116.coarse_menger_paths_bounded_separator_statement` / studies:std_coarse_menger_conjecture | `GTMisc.migration.set_path.coarse_menger_paths_bounded_separator_statement_compat` |
| `Minor.conjectures.X11.induced_menger_anticomplete_paths_statement` / arxiv:2512.17232#00 | `Minor.migration.set_path.induced_menger_anticomplete_paths_statement_compat` |
| `Packing.conjectures.X26.bounded_degree_distant_induced_menger_statement` / arxiv:2309.07905#00 | `Packing.migration.set_path.bounded_degree_distant_induced_menger_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py set_path --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `GTMisc.conjectures.X146.x146_A_path`, `GTMisc.conjectures.X216.x216_odd_xy_path`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `graph-theory-misc/theories/migration/path_vertices.v#X39Legacy.has_k_distant_xy_paths`, `graph-theory-misc/theories/migration/path_vertices.v#X39Legacy.separates_xy`, `graph-theory-misc/theories/migration/path_vertices.v#X116Legacy.has_k_distant_ST_paths`, `graph-theory-misc/theories/migration/path_vertices.v#X116Legacy.statement`, `minor-theory/theories/migration/path_vertices.v#X11Legacy.has_k_anticomplete_xy_paths`, `minor-theory/theories/migration/path_vertices.v#X11Legacy.no_xy_path_after_closed_neighbourhood`, `packing-theory/theories/migration/path_vertices.v#X26Legacy.has_k_distant_xy_paths`, `packing-theory/theories/migration/path_vertices.v#X26Legacy.separates_xy`, `graph-theory-misc/theories/migration/set_separators.v#Legacy.x39_separates_xy`, `graph-theory-misc/theories/migration/set_separators.v#X39Legacy.coarse_menger_ball_separator_statement`, `graph-theory-misc/theories/migration/set_separators.v#X40Legacy.coarse_menger_distance_two_separator_statement`, `packing-theory/theories/migration/set_separators.v#Legacy.x26_separates_xy`, `packing-theory/theories/migration/set_separators.v#X26Legacy.bounded_degree_distant_induced_menger_statement`, `graph-theory-misc/theories/migration/balls.v#X39Legacy.x39_has_k_distant_xy_paths`, `graph-theory-misc/theories/migration/balls.v#X39Legacy.coarse_menger_ball_separator_statement`, `graph-theory-misc/theories/migration/balls.v#X40Legacy.coarse_menger_distance_two_separator_statement`, `graph-theory-misc/theories/migration/balls.v#X116Legacy.x116_has_k_distant_ST_paths`, `graph-theory-misc/theories/migration/balls.v#X116Legacy.coarse_menger_paths_bounded_separator_statement`, `packing-theory/theories/migration/balls.v#X26Legacy.x26_has_k_distant_xy_paths`, `packing-theory/theories/migration/balls.v#X26Legacy.bounded_degree_distant_induced_menger_statement`, `graph-theory-misc/theories/migration/distant_paths.v#Legacy.x39_has_k_distant_xy_paths`, `graph-theory-misc/theories/migration/distant_paths.v#Legacy.x116_has_k_distant_ST_paths`, `graph-theory-misc/theories/migration/distant_paths.v#X39Legacy.coarse_menger_ball_separator_statement`, `graph-theory-misc/theories/migration/distant_paths.v#X40Legacy.coarse_menger_distance_two_separator_statement`, `graph-theory-misc/theories/migration/distant_paths.v#X116Legacy.coarse_menger_paths_bounded_separator_statement`, `packing-theory/theories/migration/distant_paths.v#Legacy.x26_has_k_distant_xy_paths`, `packing-theory/theories/migration/distant_paths.v#X26Legacy.bounded_degree_distant_induced_menger_statement`.

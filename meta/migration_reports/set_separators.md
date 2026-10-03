# Migration report: set-separator

Inputs: `meta/migration_reports/set_separators.spec.json` and `meta/library_primitives/set-separator.json`.
Regenerate: `python3 meta/migration_report.py set_separators --write`.
Full evidence: `python3 meta/migration_report.py set_separators --details /tmp/migration-details`.

- Canonical: `GraphTheory.core.connectivity.separator`.
- Baseline: `a02e1c2108db331363787c099f8fcb99aa4e6b41`.
- Scope: 2 helpers, 3 statements, 33 frozen objects, 35 recorded references.
- Source checks: 205/205 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `GTMisc.conjectures.X39.coarse_menger_ball_separator_statement` / studies:std_coarse_menger_conjecture_georgakopoulos_papasogl | `GTMisc.migration.set_separators.coarse_menger_ball_separator_statement_compat` |
| `GTMisc.conjectures.X40.coarse_menger_distance_two_separator_statement` / arxiv:2508.14332#00 | `GTMisc.migration.set_separators.coarse_menger_distance_two_separator_statement_compat` |
| `Packing.conjectures.X26.bounded_degree_distant_induced_menger_statement` / arxiv:2309.07905#00 | `Packing.migration.set_separators.bounded_degree_distant_induced_menger_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py set_separators --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Cycle.foundations.connectivity.ueseparates`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `graph-theory-misc/theories/migration/balls.v#X39Legacy.coarse_menger_ball_separator_statement`, `graph-theory-misc/theories/migration/balls.v#X40Legacy.coarse_menger_distance_two_separator_statement`, `packing-theory/theories/migration/balls.v#X26Legacy.bounded_degree_distant_induced_menger_statement`.

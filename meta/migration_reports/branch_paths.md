# Migration report: branch-paths

Inputs: `meta/migration_reports/branch_paths.spec.json` and `meta/library_primitives/branch-paths.json`.
Regenerate: `python3 meta/migration_report.py branch_paths --write`.
Full evidence: `python3 meta/migration_report.py branch_paths --details /tmp/migration-details`.

- Canonical: `Chromatic.foundations.branch_paths.branch_paths_at_least`.
- Baseline: `311fdcb89dc12a78c62cb0ee6d2477896cbce9a7`.
- Scope: 3 helpers, 3 statements, 7 frozen objects, 11 recorded references.
- Source checks: 73/73 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X177.forest_of_lanterns_pervasive_statement` / arxiv:1609.00314#00 | `Chromatic.migration.branch_paths.forest_of_lanterns_pervasive_statement_compat` |
| `Chromatic.conjectures.X185.every_multigraph_widespread_statement` / arxiv:1701.05597#00 | `Chromatic.migration.branch_paths.every_multigraph_widespread_statement_compat` |
| `Chromatic.conjectures.X186.subdivision_or_local_chi_two_statement` / arxiv:1701.05597#01 | `Chromatic.migration.branch_paths.subdivision_or_local_chi_two_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py branch_paths --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Extremal.conjectures.X98.x98_induced_subdivision`, `GTMisc.conjectures.X114.x114_induced_subdivision`, `Minor.foundations.containment.has_subdivision`.

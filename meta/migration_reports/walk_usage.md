# Migration report: walk-uses

Inputs: `meta/migration_reports/walk_usage.spec.json` and `meta/library_primitives/walk-uses.json`.
Regenerate: `python3 meta/migration_report.py walk_usage --write`.
Full evidence: `python3 meta/migration_report.py walk_usage --details /tmp/migration-details`.

- Canonical: `GTBase.walk_usage.seq_consecutiveb`.
- Baseline: `016b8687b63e0191aaa50bf5427ad20cd9c487e9`.
- Scope: 2 helpers, 2 statements, 9 frozen objects, 28 recorded references.
- Source checks: 91/91 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `GTMisc.conjectures.D7.approximation_ratio_for_maximum_edge_disjoint_paths_statement` / opg:approximation_ratio_for_maximum_edge_disjoint_paths_problem | `GTMisc.migration.walk_usage.approximation_ratio_for_maximum_edge_disjoint_paths_statement_compat` |
| `Infinite.conjectures.D4inf4.universal_highly_arc_transitive_digraphs_statement` / opg:universal_highly_arc_transitive_digraphs | `Infinite.migration.walk_usage.universal_highly_arc_transitive_digraphs_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py walk_usage --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Cycle.conjectures.D1.edp_feasible`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `infinite-graph-theory/theories/migration/walk_usage.v#Legacy.walk_uses`.

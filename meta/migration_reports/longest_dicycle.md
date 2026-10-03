# Migration report: longest-dicycle

Inputs: `meta/migration_reports/longest_dicycle.spec.json` and `meta/library_primitives/longest-dicycle.json`.
Regenerate: `python3 meta/migration_report.py longest_dicycle --write`.
Full evidence: `python3 meta/migration_report.py longest_dicycle --details /tmp/migration-details`.

- Canonical: `Digraph.foundations.longest_cycles.longest_dicycle`.
- Baseline: `0646ae36e10c28c712ccfc84370daf9ff9ebba43`.
- Scope: 1 helpers, 1 statements, 2 frozen objects, 35 recorded references.
- Source checks: 57/57 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Digraph.conjectures.X2.vertex_transitive_longest_dicycles_intersect_statement` / arxiv:2602.16333#02 | `Digraph.migration.longest_dicycle.vertex_transitive_longest_dicycles_intersect_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py longest_dicycle --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Digraph.conjectures.grounding_unvd_sad.has_long_dicycle`, `Cycle.conjectures.X212.x212_longest_cycle`.

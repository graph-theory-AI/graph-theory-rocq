# Migration report: longest-cycle

Inputs: `meta/migration_reports/longest_cycle.spec.json` and `meta/library_primitives/longest-cycle.json`.
Regenerate: `python3 meta/migration_report.py longest_cycle --write`.
Full evidence: `python3 meta/migration_report.py longest_cycle --details /tmp/migration-details`.

- Canonical: `GTBase.walks_paths.seq_longest_cycle`.
- Baseline: `c52825404e519998716b02ccb40f73cfc604dc56`.
- Scope: 3 helpers, 3 statements, 8 frozen objects, 27 recorded references.
- Source checks: 105/105 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Cycle.conjectures.X10.smith_longest_cycles_r_connected_statement` / studies:std_smith_s_conjecture_longest_cycles_in_r_connected | `Cycle.migration.longest_cycle.smith_longest_cycles_r_connected_statement_compat` |
| `Cycle.conjectures.X212.smith_two_longest_cycles_statement` / bm:bm-064 | `Cycle.migration.longest_cycle.smith_two_longest_cycles_statement_compat` |
| `Hom.conjectures.U3.chords_of_longest_cycles_statement` / opg:chords_of_longest_cycles | `Hom.migration.longest_cycle.chords_of_longest_cycles_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py longest_cycle --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Hom.conjectures.U3.longest_path`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `cycle-theory/theories/migration/cycle_vertices.v#X10Legacy.smith_longest_cycles_r_connected_statement`, `cycle-theory/theories/migration/cycle_vertices.v#X212Legacy.smith_two_longest_cycles_statement`, `cycle-theory/theories/migration/genuine_cycle.v#X212Legacy.smith_two_longest_cycles_statement`.

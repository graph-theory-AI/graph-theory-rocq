# Migration report: chordal

Inputs: `meta/migration_reports/chordal.spec.json` and `meta/library_primitives/chordal.json`.
Regenerate: `python3 meta/migration_report.py chordal --write`.
Full evidence: `python3 meta/migration_report.py chordal --details /tmp/migration-details`.

- Canonical: `GTBase.chordal.chordal_by_cycles`.
- Baseline: `63be19754ec48469f01c62cbd684f1a55b640cdf`.
- Scope: 2 helpers, 2 statements, 14 frozen objects, 15 recorded references.
- Source checks: 98/98 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Packing.conjectures.XE1.erdos_81_statement` / erdos:81 | `Packing.migration.chordal.erdos_81_statement_compat` |
| `GTMisc.conjectures.X169.token_sliding_chordal_clique_tree_degree_polytime_statement` / arxiv:1605.00442#00 | `GTMisc.migration.chordal.token_sliding_chordal_clique_tree_degree_polytime_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py chordal --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Digraph.conjectures.chi_bounded.chordal_C3`.

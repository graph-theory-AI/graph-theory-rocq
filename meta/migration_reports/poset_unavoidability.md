# Migration report: poset-unavoidability

Inputs: `meta/migration_reports/poset_unavoidability.spec.json` and `meta/library_primitives/poset-unavoidability.json`.
Regenerate: `python3 meta/migration_report.py poset_unavoidability --write`.
Full evidence: `python3 meta/migration_report.py poset_unavoidability --details /tmp/migration-details`.

- Canonical: `Minor.foundations.poset_unavoidability.poset_unavoidable`.
- Baseline: `97605ddae838bc6e84b0602240148246e9d065f2`.
- Scope: 1 helpers, 1 statements, 2 frozen objects, 6 recorded references.
- Source checks: 31/31 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Minor.conjectures.X228.unavoidable_minor_kelly_construction_statement` / arxiv:2002.00496#02 | `Minor.migration.poset_unavoidability.unavoidable_minor_kelly_construction_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py poset_unavoidability --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Digraph.conjectures.unvd.unavoidable`.

# Migration report: poset-unavoidability

Inputs: `meta/migration_reports/poset_unavoidability.spec.json` and `meta/library_primitives/poset-unavoidability.json`.
Regenerate: `python3 meta/migration_report.py poset_unavoidability --write`.
Full evidence: `python3 meta/migration_report.py poset_unavoidability --details /tmp/migration-details`.

- Canonical: `Minor.foundations.poset_unavoidability.poset_unavoidable`.
- Baseline: `97605ddae838bc6e84b0602240148246e9d065f2`.
- Scope: 4 helpers, 6 statements, 12 frozen objects, 71 recorded references.
- Source checks: 171/171 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Minor.conjectures.X228.unavoidable_minor_kelly_construction_statement` / arxiv:2002.00496#02 | `Minor.migration.poset_unavoidability.unavoidable_minor_kelly_construction_statement_compat` |
| `Digraph.conjectures.X17.sumner_oriented_tree_unavoidable_statement` / studies:std_sumner_s_conjecture | `Digraph.migration.tournament_unavoidability.sumner_oriented_tree_unavoidable_statement_compat` |
| `Digraph.conjectures.unvd.conj_9` / arxiv:2410.23566#03 | `Digraph.migration.tournament_unavoidability.conj_9_compat` |
| `Digraph.conjectures.unvd.prob_6` / arxiv:2410.23566#00 | `Digraph.migration.tournament_unavoidability.prob_6_compat` |
| `Digraph.conjectures.X221.kextension_linear_unavoidability_statement` / arxiv:2410.23566#05 | `Digraph.migration.tournament_unavoidability.kextension_linear_unavoidability_statement_compat` |
| `Digraph.conjectures.reals_growth.prob6_unvd_statement` / no corpus row | `Digraph.migration.tournament_unavoidability.prob6_unvd_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py poset_unavoidability --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `digraph-theory/theories/migration/degree_balance.v#X221Legacy.eulerian_avoidable`.

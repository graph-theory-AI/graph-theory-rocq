# Migration report: prism-configuration

Inputs: `meta/migration_reports/prism_configuration.spec.json` and `meta/library_primitives/prism-configuration.json`.
Regenerate: `python3 meta/migration_report.py prism_configuration --write`.
Full evidence: `python3 meta/migration_report.py prism_configuration --details /tmp/migration-details`.

- Canonical: `Minor.foundations.prism_configurations.prism_configuration`.
- Baseline: `29336a8c9d22d7016d665c696c444bfb15dbefb5`.
- Scope: 2 helpers, 1 statements, 12 frozen objects, 21 recorded references.
- Source checks: 94/94 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Minor.conjectures.X220.theta_prism_even_wheel_free_bounded_treewidth_statement` / arxiv:2203.06775#00 | `Minor.migration.prism_configuration.theta_prism_even_wheel_free_bounded_treewidth_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py prism_configuration --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Topological.conjectures.D6emb.is_prism`, `Topological.conjectures.D6emb.is_antiprism`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `minor-theory/theories/migration/model_support.v#X220Legacy.x220_prism`, `minor-theory/theories/migration/consecutive_in_cycle.v#X220Legacy.theta_prism_even_wheel_free_bounded_treewidth_statement`, `minor-theory/theories/migration/induced_cycles.v#X220Legacy.theta_prism_even_wheel_free_bounded_treewidth_statement`.

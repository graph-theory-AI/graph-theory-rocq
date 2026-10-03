# Migration report: perfect-matching

Inputs: `meta/migration_reports/perfect_matching.spec.json` and `meta/library_primitives/perfect-matching.json`.
Regenerate: `python3 meta/migration_report.py perfect_matching --write`.
Full evidence: `python3 meta/migration_report.py perfect_matching --details /tmp/migration-details`.

- Canonical: `GTBase.common.perfect_matching`.
- Baseline: `9e030727db115917ae077ac07a8fc6aa68661f73`.
- Scope: 3 helpers, 3 statements, 10 frozen objects, 25 recorded references.
- Source checks: 93/93 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Cycle.conjectures.X24.one_factorization_long_rainbow_cycle_statement` / studies:std_akbari_etesami_mahini_mahmoody_question_on_long | `Cycle.migration.perfect_matching.one_factorization_long_rainbow_cycle_statement_compat` |
| `Packing.conjectures.X18.knn_fair_perfect_matching_statement` / arxiv:1611.03196#01 | `Packing.migration.perfect_matching.knn_fair_perfect_matching_statement_compat` |
| `Packing.conjectures.X25.kotzig_perfect_one_factorization_statement` / studies:std_kotzig_s_perfect_1_factorization_conjecture | `Packing.migration.perfect_matching.kotzig_perfect_one_factorization_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py perfect_matching --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Cycle.conjectures.U10.is_perfect_matching`, `Cycle.conjectures.U10.perfect_matching_cover`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `cycle-theory/theories/migration/cycle_edges.v#X24Legacy.one_factorization_long_rainbow_cycle_statement`.

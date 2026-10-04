# Migration report: regularity

Inputs: `meta/migration_reports/regularity.spec.json` and `meta/library_primitives/regularity.json`.
Regenerate: `python3 meta/migration_report.py regularity --write`.
Full evidence: `python3 meta/migration_report.py regularity --details /tmp/migration-details`.

- Canonical: `Hypergraph.foundations.hypergraph_regularity.hg_regular`.
- Baseline: `7e030f252c859c5334185673b10b69971cab9402`.
- Scope: 1 helpers, 1 statements, 7 frozen objects, 11 recorded references.
- Source checks: 58/58 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Hypergraph.conjectures.X73.regular_tripartite_hypergraph_matching_lower_bound_statement` / studies:std_aharoni_charbit_howard_conjecture_on_matchings_i | `Hypergraph.migration.regularity.regular_tripartite_hypergraph_matching_lower_bound_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py regularity --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Infinite.conjectures.D4inf3.regular`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `hypergraph-theory/theories/migration/partite_uniform.v#X73PartiteLegacy.regular_tripartite_hypergraph_matching_lower_bound_statement`, `hypergraph-theory/theories/migration/matching.v#X73MatchingLegacy.regular_tripartite_hypergraph_matching_lower_bound_statement`.

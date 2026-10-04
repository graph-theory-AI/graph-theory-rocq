# Migration report: edges-between

Inputs: `meta/migration_reports/edges_between.spec.json` and `meta/library_primitives/edges-between.json`.
Regenerate: `python3 meta/migration_report.py edges_between --write`.
Full evidence: `python3 meta/migration_report.py edges_between --details /tmp/migration-details`.

- Canonical: `GTBase.common.edges_between`.
- Baseline: `842ff4d456f543db4030b424a3c53d5c22fd70c9`.
- Scope: 4 helpers, 4 statements, 14 frozen objects, 37 recorded references.
- Source checks: 135/135 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Extremal.conjectures.X118.conlon_fox_sudakov_dense_pair_statement` / studies:std_conlon_fox_sudakov_conjecture_dense_pair | `Extremal.migration.edges_between.conlon_fox_sudakov_dense_pair_statement_compat` |
| `Extremal.conjectures.X120.conlon_fox_sudakov_sparse_pair_statement` / studies:std_conlon_fox_sudakov_sparse_pair_conjecture | `Extremal.migration.edges_between.conlon_fox_sudakov_sparse_pair_statement_compat` |
| `Extremal.conjectures.X223.h_free_eps_bounded_sparse_pair_statement` / arxiv:1810.00058#02 | `Extremal.migration.edges_between.h_free_eps_bounded_sparse_pair_statement_compat` |
| `Extremal.conjectures.X223.induced_turan_even_cycle_sparse_statement` / arxiv:2405.05902#01 | `Extremal.migration.edges_between.induced_turan_even_cycle_sparse_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py edges_between --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `extremal-graph-theory/theories/migration/induced_free.v#X118Legacy.statement`, `extremal-graph-theory/theories/migration/induced_free.v#X120Legacy.statement`.

# Migration report: cut-size

Inputs: `meta/migration_reports/cut_size.spec.json` and `meta/library_primitives/cut-size.json`.
Regenerate: `python3 meta/migration_report.py cut_size --write`.
Full evidence: `python3 meta/migration_report.py cut_size --details /tmp/migration-details`.

- Canonical: `GTBase.common.cut_size`.
- Baseline: `9de20ca72a0d7c8279ff8861033bfd80ce12a84a`.
- Scope: 4 helpers, 3 statements, 19 frozen objects, 30 recorded references.
- Source checks: 140/140 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Extremal.conjectures.X76.ck_free_max_cut_polynomial_surplus_statement` / studies:std_alon_et_al_c_k_free_max_cut_conjecture | `Extremal.migration.cut_size.ck_free_max_cut_polynomial_surplus_statement_compat` |
| `Extremal.conjectures.X78.h_free_max_cut_three_fourths_surplus_statement` / studies:std_alon_krivelevich_sudakov_max_cut_exponent_conjec | `Extremal.migration.cut_size.h_free_max_cut_three_fourths_surplus_statement_compat` |
| `Hypergraph.conjectures.X209.hypergraph_cut_excess_theta_sqrt_statement` / arxiv:1803.08462#00 | `Hypergraph.migration.cut_size.hypergraph_cut_excess_theta_sqrt_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py cut_size --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Hypergraph.conjectures.X209.x209_uniform`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `extremal-graph-theory/theories/migration/edge_count.v#X76Legacy.ck_free_max_cut_polynomial_surplus_statement`, `extremal-graph-theory/theories/migration/edge_count.v#X76Original.ck_free_max_cut_polynomial_surplus_statement`, `extremal-graph-theory/theories/migration/edge_count.v#X78Legacy.h_free_max_cut_three_fourths_surplus_statement`, `extremal-graph-theory/theories/migration/edge_count.v#X78Original.h_free_max_cut_three_fourths_surplus_statement`, `extremal-graph-theory/theories/migration/subgraph_of.v#X78Legacy.h_free_max_cut_three_fourths_surplus_statement`.

# Migration report: clique-count

Inputs: `meta/migration_reports/clique_counts.spec.json` and `meta/library_primitives/clique-count.json`.
Regenerate: `python3 meta/migration_report.py clique_counts --write`.
Full evidence: `python3 meta/migration_report.py clique_counts --details /tmp/migration-details`.

- Canonical: `GTBase.clique_counts.all_clique_count`.
- Baseline: `16d5a05dea232c0b2e3321675e31e8279c3f2350`.
- Scope: 5 helpers, 4 statements, 19 frozen objects, 25 recorded references.
- Source checks: 148/148 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Extremal.conjectures.D2tur.number_of_cliques_in_minor_closed_classes_statement` / opg:number_of_cliques_in_minor_closed_classes | `Extremal.migration.clique_counts.number_of_cliques_in_minor_closed_classes_statement_compat` |
| `Extremal.conjectures.X4.triangle_supersaturation_statement` / erdos:1010 | `Extremal.migration.clique_counts.triangle_supersaturation_statement_compat` |
| `Minor.conjectures.X174.kt_immersion_clique_count_extremal_statement` / arxiv:1606.06810#00 | `Minor.migration.clique_counts.kt_immersion_clique_count_extremal_statement_compat` |
| `Minor.conjectures.X175.kt_subdivision_clique_count_asymptotic_statement` / arxiv:1606.06810#01 | `Minor.migration.clique_counts.kt_subdivision_clique_count_asymptotic_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py clique_counts --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `GTMisc.conjectures.U13.is_max_clique`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `extremal-graph-theory/theories/migration/edge_count.v#X4Legacy.triangle_supersaturation_statement`, `minor-theory/theories/migration/path_edges.v#X174Legacy.kt_immersion_clique_count_extremal_statement`, `minor-theory/theories/migration/internal_vertices.v#X175Legacy.statement`.

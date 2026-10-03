# Migration report: induced-subdivision

Inputs: `meta/migration_reports/induced_subdivisions.spec.json` and `meta/library_primitives/induced-subdivision.json`.
Regenerate: `python3 meta/migration_report.py induced_subdivisions --write`.
Full evidence: `python3 meta/migration_report.py induced_subdivisions --details /tmp/migration-details`.

- Canonical: `GTBase.induced_subdivisions.induced_subdivision_model`.
- Baseline: `952a89bdecf65bed9be3a1393eabc91ca091d26c`.
- Scope: 4 helpers, 2 statements, 14 frozen objects, 81 recorded references.
- Source checks: 109/109 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Extremal.conjectures.X98.polynomial_kuhn_osthus_induced_subdivision_statement` / studies:std_bonamy_et_al_polynomial_k_hn_osthus_conjecture | `Extremal.migration.induced_subdivisions.polynomial_kuhn_osthus_induced_subdivision_statement_compat` |
| `GTMisc.conjectures.X114.subcubic_induced_subdivision_np_complete_statement` / studies:std_chudnovsky_seymour_trotignon_question_on_subcubi | `GTMisc.migration.induced_subdivisions.subcubic_induced_subdivision_np_complete_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py induced_subdivisions --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Minor.foundations.containment.subdiv_model`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `extremal-graph-theory/theories/migration/subgraph_of.v#X98Legacy.polynomial_kuhn_osthus_induced_subdivision_statement`, `graph-theory-misc/theories/migration/subcubic.v#X114Legacy.subcubic_induced_subdivision_np_complete_statement`.

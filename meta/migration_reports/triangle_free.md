# Migration report: triangle-free

Inputs: `meta/migration_reports/triangle_free.spec.json` and `meta/library_primitives/triangle-free.json`.
Regenerate: `python3 meta/migration_report.py triangle_free --write`.
Full evidence: `python3 meta/migration_report.py triangle_free --details /tmp/migration-details`.

- Canonical: `GTBase.base.triangle_free`.
- Baseline: `f52251a96beabaef4c9005e8dd9a9a29c4cca17c`.
- Scope: 3 helpers, 3 statements, 11 frozen objects, 17 recorded references.
- Source checks: 94/94 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X132.dvorak_norin_postle_planar_list_flexibility_statement` / studies:std_dvo_k_norin_postle_flexibility_conjecture_planar | `Chromatic.migration.triangle_free.dvorak_norin_postle_planar_list_flexibility_statement_compat` |
| `Chromatic.conjectures.X187.planar_triangle_free_request_graph_fraction_statement` / arxiv:1702.00588#00 | `Chromatic.migration.triangle_free.planar_triangle_free_request_graph_fraction_statement_compat` |
| `Chromatic.conjectures.X192.triangle_free_minor_closed_chromatic_additive_approx_statement` / arxiv:1707.03888#00 | `Chromatic.migration.triangle_free.triangle_free_minor_closed_chromatic_additive_approx_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py triangle_free --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `GTMisc.conjectures.XE2.xe2_triangle_free_rel`, `Digraph.conjectures.chi_bounded.underlying_triangle_free`, `Digraph.conjectures.X221.x221_oriented_triangle_free`, `Digraph.conjectures.X193.x193_directed_triangle_free`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `chromatic-theory/theories/migration/proper_colouring.v#X187Legacy.planar_triangle_free_request_graph_fraction_statement`, `chromatic-theory/theories/migration/minor_classes.v#Legacy.triangle_free_minor_closed_chromatic_additive_approx_statement`.

# Migration report: degree-balance

Inputs: `meta/migration_reports/degree_balance.spec.json` and `meta/library_primitives/degree-balance.json`.
Regenerate: `python3 meta/migration_report.py degree_balance --write`.
Full evidence: `python3 meta/migration_report.py degree_balance --details /tmp/migration-details`.

- Canonical: `Digraph.foundations.degree_balance.balanced`.
- Baseline: `298112264b7c31820acf889c6da29b710fd39c9a`.
- Scope: 3 helpers, 5 statements, 13 frozen objects, 110 recorded references.
- Source checks: 172/173 pass; FAILED.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Digraph.conjectures.X221.orientation_C4_eulerian_avoidable_statement` / arxiv:2510.11311#04 | `Digraph.migration.degree_balance.orientation_C4_eulerian_avoidable_statement_compat` |
| `Digraph.conjectures.colouring_variants.majority_3col_eulerian_statement` / arxiv:1608.03040#04 | `Digraph.migration.degree_balance.majority_3col_eulerian_statement_compat` |
| `Digraph.conjectures.two_extremal.H6_no_full_cover` / derived:drv_twoext_h6 | `Digraph.migration.degree_balance.H6_no_full_cover_compat` |
| `Digraph.conjectures.two_extremal_glue.conj_9_2_glued` / no corpus row | `Digraph.migration.degree_balance.conj_9_2_glued_compat` |
| `Digraph.conjectures.glue_eul_subtype.conj_9_2_glued_e` / no corpus row | `Digraph.migration.degree_balance.conj_9_2_glued_e_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py degree_balance --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Cycle.conjectures.U6.eulerian`, `Cycle.conjectures.U6.is_eulerian_tour`, `Chromatic.foundations.alon_tarsi.at_eulerian`, `Digraph.conjectures.X221.x221_eulerian_avoidable`.
- FAILED: affected statement coverage matches baseline dependencies: missing=[]; extra=['Digraph.conjectures.glue_eul_subtype.conj_9_2_glued_e', 'Digraph.conjectures.two_extremal_glue.conj_9_2_glued']

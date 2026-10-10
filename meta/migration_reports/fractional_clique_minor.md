# Migration report: fractional-clique-minor

Inputs: `meta/migration_reports/fractional_clique_minor.spec.json` and `meta/library_primitives/fractional-clique-minor.json`.
Regenerate: `python3 meta/migration_report.py fractional_clique_minor --write`.
Full evidence: `python3 meta/migration_report.py fractional_clique_minor --details /tmp/migration-details`.

- Canonical: `Extremal.foundations.fractional_hadwiger.frac_clique_minor`.
- Baseline: `95ac06eb99283588fb5dc8d4350a728cbf68dba3`.
- Scope: 2 helpers, 1 statements, 6 frozen objects, 46 recorded references.
- Source checks: 78/78 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Extremal.conjectures.D2chr.fractional_hadwiger_statement` / opg:fractional_hadwiger | `Extremal.migration.fractional_clique_minor.fractional_hadwiger_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py fractional_clique_minor --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Extremal.conjectures.D2chr.is_hadwiger`, `Extremal.conjectures.grounding_D2chr.old_frac_clique_minor`, `Atlas.foundations.fractional.hopt`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `extremal-graph-theory/theories/migration/bfold_colouring.v#D2chrLegacy.fractional_hadwiger_statement`, `extremal-graph-theory/theories/migration/fractional_chromatic.v#D2chrLegacy.fractional_hadwiger_statement`, `extremal-graph-theory/theories/migration/fractional_chromatic.v#D2chrOriginal.statement`.

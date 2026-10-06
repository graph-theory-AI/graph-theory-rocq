# Migration report: hedgehog

Inputs: `meta/migration_reports/hedgehog.spec.json` and `meta/library_primitives/hedgehog.json`.
Regenerate: `python3 meta/migration_report.py hedgehog --write`.
Full evidence: `python3 meta/migration_report.py hedgehog --details /tmp/migration-details`.

- Canonical: `Hypergraph.foundations.hedgehog.hedgehog_edges`.
- Baseline: `eaa6564c3788f6e3e2db7a7bddbe9adba157c334`.
- Scope: 4 helpers, 1 statements, 11 frozen objects, 22 recorded references.
- Source checks: 84/84 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Hypergraph.conjectures.X117.conlon_fox_rodl_hedgehog_ramsey_statement` / studies:std_conlon_fox_r_dl_question_on_hedgehog_ramsey_numb | `Hypergraph.migration.hedgehog.conlon_fox_rodl_hedgehog_ramsey_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py hedgehog --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `GTMisc.conjectures.X87.x87_edge`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `hypergraph-theory/theories/migration/image_edge.v#X117ImageLegacy.x117_ramsey_number`, `hypergraph-theory/theories/migration/image_edge.v#X117ImageLegacy.conlon_fox_rodl_hedgehog_ramsey_statement`, `hypergraph-theory/theories/migration/monochromatic_copy.v#X117CopyLegacy.x117_ramsey_number`, `hypergraph-theory/theories/migration/monochromatic_copy.v#X117CopyLegacy.conlon_fox_rodl_hedgehog_ramsey_statement`, `hypergraph-theory/theories/migration/forces_mono.v#X117ForcingLegacy.x117_ramsey_number`, `hypergraph-theory/theories/migration/forces_mono.v#X117ForcingLegacy.conlon_fox_rodl_hedgehog_ramsey_statement`.

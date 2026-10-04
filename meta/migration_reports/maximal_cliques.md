# Migration report: maximal-clique

Inputs: `meta/migration_reports/maximal_cliques.spec.json` and `meta/library_primitives/maximal-clique.json`.
Regenerate: `python3 meta/migration_report.py maximal_cliques --write`.
Full evidence: `python3 meta/migration_report.py maximal_cliques --details /tmp/migration-details`.

- Canonical: `GTBase.maximal_cliques.maximal_clique`.
- Baseline: `1f4e9c1dd60c2d543b08d5eb1fb18c1f24ff505a`.
- Scope: 2 helpers, 2 statements, 14 frozen objects, 31 recorded references.
- Source checks: 102/102 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X181.random_graph_clique_chromatic_tight_constant_statement` / arxiv:1612.06539#00 | `Chromatic.migration.maximal_cliques.random_graph_clique_chromatic_tight_constant_statement_compat` |
| `Packing.conjectures.XE1.erdos_151_statement` / erdos:151 | `Packing.migration.maximal_cliques.erdos_151_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py maximal_cliques --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `GTMisc.conjectures.U13.is_max_clique`, `Hypergraph.conjectures.XE2.xe2_maximal_hyperclique`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `chromatic-theory/theories/migration/monochromatic.v#X181Legacy.x181_clique_colourable`, `packing-theory/theories/migration/stable_sets.v#XE1Legacy.erdos_151_statement`.

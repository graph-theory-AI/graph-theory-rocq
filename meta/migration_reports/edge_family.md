# Migration report: edge-family

Inputs: `meta/migration_reports/edge_family.spec.json` and `meta/library_primitives/edge-family.json`.
Regenerate: `python3 meta/migration_report.py edge_family --write`.
Full evidence: `python3 meta/migration_report.py edge_family --details /tmp/migration-details`.

- Canonical: `Packing.foundations.edge_families.edge_family`.
- Baseline: `9e030727db115917ae077ac07a8fc6aa68661f73`.
- Scope: 1 helpers, 4 statements, 7 frozen objects, 20 recorded references.
- Source checks: 80/80 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Packing.conjectures.X15.bipartite_matching_underrepresentation_statement` / arxiv:1611.03196#03 | `Packing.migration.edge_families.bipartite_matching_underrepresentation_statement_compat` |
| `Packing.conjectures.X15.bipartite_matching_underrepresentation_llm_statement` / no corpus row | `Packing.migration.edge_families.bipartite_matching_underrepresentation_llm_statement_compat` |
| `Packing.conjectures.X15.bipartite_matching_underrepresentation_llm2_statement` / no corpus row | `Packing.migration.edge_families.bipartite_matching_underrepresentation_llm2_statement_compat` |
| `Packing.conjectures.X15.bipartite_matching_underrepresentation_llm3_statement` / no corpus row | `Packing.migration.edge_families.bipartite_matching_underrepresentation_llm3_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py edge_family --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Packing.conjectures.X15alone.x15_edge_family`.

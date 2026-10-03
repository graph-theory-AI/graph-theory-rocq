# Migration report: complement

Inputs: `meta/migration_reports/complement.spec.json` and `meta/library_primitives/complement.json`.
Regenerate: `python3 meta/migration_report.py complement --write`.
Full evidence: `python3 meta/migration_report.py complement --details /tmp/migration-details`.

- Canonical: `GraphTheory.core.sgraph.compl`.
- Baseline: `49ddc033ec6be3372ba6813f044fd26922fad16d`.
- Scope: 10 helpers, 16 statements, 59 frozen objects, 163 recorded references.
- Source checks: 448/448 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X3.gyarfas_complementation_chi_bounded_statement` / studies:std_gy_rf_s_complementation_conjecture | `Chromatic.migration.complement.gyarfas_complementation_chi_bounded_statement_compat` |
| `Chromatic.conjectures.XE2.erdos_753_statement` / erdos:753 | `Chromatic.migration.complement.erdos_753_statement_compat` |
| `Extremal.conjectures.X56.c8_complement_c8_erdos_hajnal_statement` / arxiv:2102.04994#00 | `Extremal.migration.complement.c8_complement_c8_erdos_hajnal_statement_compat` |
| `Extremal.conjectures.XE1.erdos_545_statement` / erdos:545 | `Extremal.migration.complement.erdos_545_statement_compat` |
| `Extremal.conjectures.XE1.erdos_550_statement` / erdos:550 | `Extremal.migration.complement.erdos_550_statement_compat` |
| `Extremal.conjectures.XE1.erdos_552_statement` / erdos:552 | `Extremal.migration.complement.erdos_552_statement_compat` |
| `Extremal.conjectures.XE1.erdos_566_statement` / erdos:566 | `Extremal.migration.complement.erdos_566_statement_compat` |
| `Extremal.conjectures.XE1.erdos_567_statement` / erdos:567 | `Extremal.migration.complement.erdos_567_statement_compat` |
| `Extremal.conjectures.XE1.erdos_568_statement` / erdos:568 | `Extremal.migration.complement.erdos_568_statement_compat` |
| `Extremal.conjectures.XE1.erdos_812_statement` / erdos:812 | `Extremal.migration.complement.erdos_812_statement_compat` |
| `Extremal.conjectures.XE1.erdos_87_statement` / erdos:87 | `Extremal.migration.complement.erdos_87_statement_compat` |
| `Extremal.conjectures.XE2.erdos_547_statement` / erdos:547 | `Extremal.migration.complement.erdos_547_statement_compat` |
| `Extremal.conjectures.XE2.erdos_549_statement` / erdos:549 | `Extremal.migration.complement.erdos_549_statement_compat` |
| `Extremal.conjectures.XE2.erdos_570_statement` / erdos:570 | `Extremal.migration.complement.erdos_570_statement_compat` |
| `Extremal.conjectures.XE2.erdos_800_statement` / erdos:800 | `Extremal.migration.complement.erdos_800_statement_compat` |
| `GTMisc.conjectures.X29.no_c5_c7_complement_c7_normal_graph_statement` / studies:std_normal_graph_conjecture_de_simone_k_rner | `GTMisc.migration.complement.no_c5_c7_complement_c7_normal_graph_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py complement --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Chromatic.conjectures.U8.local_complement`, `GTMisc.conjectures.X94.x94_bicomplement`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `extremal-graph-theory/theories/migration/induced_free.v#X56Legacy.statement`, `extremal-graph-theory/theories/migration/subgraph_of.v#XE1Legacy.graph_ramsey`, `extremal-graph-theory/theories/migration/consecutive_in_cycle.v#XE1Legacy.erdos_567_statement`, `extremal-graph-theory/theories/migration/bipartition.v#XE2Legacy.erdos_549_statement`, `extremal-graph-theory/theories/migration/bipartition.v#XE2Original.erdos_549_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE1Legacy.erdos_545_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE1Legacy.erdos_566_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE1Legacy.erdos_567_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE1Legacy.erdos_568_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE2Legacy.erdos_570_statement`, `extremal-graph-theory/theories/migration/min_degree_at_least.v#XE1Legacy.erdos_545_statement`, `extremal-graph-theory/theories/migration/min_degree_at_least.v#XE1Legacy.erdos_566_statement`, `extremal-graph-theory/theories/migration/min_degree_at_least.v#XE1Legacy.erdos_567_statement`, `extremal-graph-theory/theories/migration/min_degree_at_least.v#XE1Legacy.erdos_568_statement`, `extremal-graph-theory/theories/migration/min_degree_at_least.v#XE2Legacy.erdos_570_statement`, `chromatic-theory/theories/migration/chi_bounded_classes.v#X3Legacy.gyarfas_complementation_chi_bounded_statement`, `extremal-graph-theory/theories/migration/whole_tree.v#XE1Legacy.erdos_550_statement`, `extremal-graph-theory/theories/migration/whole_tree.v#XE1Legacy.erdos_568_statement`, `extremal-graph-theory/theories/migration/whole_tree.v#XE2Legacy.erdos_547_statement`, `extremal-graph-theory/theories/migration/whole_tree.v#XE2Legacy.erdos_549_statement`.

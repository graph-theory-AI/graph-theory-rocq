# Migration report: monochromatic

Inputs: `meta/migration_reports/monochromatic.spec.json` and `meta/library_primitives/monochromatic.json`.
Regenerate: `python3 meta/migration_report.py monochromatic --write`.
Full evidence: `python3 meta/migration_report.py monochromatic --details /tmp/migration-details`.

- Canonical: `GTBase.monochromatic.monochromatic_on`.
- Baseline: `47eed16af2f9575575a573f3b8a93860d47e72ca`.
- Scope: 3 helpers, 5 statements, 18 frozen objects, 86 recorded references.
- Source checks: 191/191 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X181.random_graph_clique_chromatic_tight_constant_statement` / arxiv:1612.06539#00 | `Chromatic.migration.monochromatic.random_graph_clique_chromatic_tight_constant_statement_compat` |
| `Chromatic.conjectures.X194.clustered_chromatic_minor_class_treedepth_bound_statement` / arxiv:1708.02370#00 | `Chromatic.migration.monochromatic.clustered_chromatic_minor_class_treedepth_bound_statement_compat` |
| `Chromatic.conjectures.X218.odd_minor_free_defective_clustered_treedepth_statement` / arxiv:2308.15721#00 | `Chromatic.migration.monochromatic.odd_minor_free_defective_clustered_treedepth_statement_compat` |
| `Topological.conjectures.X138.esperet_joret_surface_triangle_free_clustered_two_colouring_statement` / studies:std_esperet_joret_question_on_clustered_colouring_of | `Topological.migration.monochromatic.esperet_joret_surface_triangle_free_clustered_two_colouring_statement_compat` |
| `GTMisc.conjectures.U13.two_colouring_a_graph_without_a_monochromatic_maximu_statement` / opg:2_colouring_a_graph_without_a_monochromatic_maximum_clique | `GTMisc.migration.monochromatic.two_colouring_a_graph_without_a_monochromatic_maximu_statement_compat` |

Source weakenings after migration: ONE-WAY source-repair certificates (`frozen -> live`), not migration equivalences; every other row keeps its exact iff: `Chromatic.conjectures.X194.clustered_chromatic_minor_class_treedepth_bound_statement` (`2 <= k -> x194_treedepth_at_most H k` -> `x194_ctd_at_most H k`; record `meta/STATEMENT_IMPROVEMENTS.md`; row fields `implemented_by`, `source_verified_by`, `source_verified_at`, `verification_note`; leg fields `commit`, `note`).

Source re-encodings after migration: certificates of each record's stated relation, not migration equivalences: `Chromatic.conjectures.X218.odd_minor_free_defective_clustered_treedepth_statement` (`1 <= k -> x218_connected_treedepth_at_most H k -> ~ x218_connected_treedepth_at_most H k.-1 -> x218_defective_chromatic_class_le (fun G : sgraph => ~ x218_odd_minor G H) (k - 1) /\ x218_clustered_chromatic_class_le (fun G : sgraph => ~ x218_odd_minor G H) (k - 1)` -> `x218_ctd_at_most H k -> ~ x218_ctd_at_most H k.-1 -> x218_clustered_chromatic_class_le (fun G : sgraph => ~ x218_odd_minor_tree_model G H) (2 * k - 2) /\ x218_defective_chromatic_class_le (fun G : sgraph => ~ x218_odd_minor_tree_model G H) (k - 1) /\ (forall j : nat, j.+1 < k -> ~ x218_defective_chromatic_class_le (fun G : sgraph => ~ x218_odd_minor_tree_model G H) j)`; relation `({frozen} -> True) /\ ({live} -> True)`; record `meta/STATEMENT_IMPROVEMENTS.md`; row fields `source_verified_by`, `source_verified_at`, `verification_note`; leg fields `statement`, `note`).

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py monochromatic --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `GTMisc.conjectures.X20.x20_monochromatic_connected_set`, `Extremal.conjectures.XE2.xe2_monochromatic_path`, `Extremal.conjectures.XE1.xe1_monochromatic_copy_in_complete`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `chromatic-theory/theories/migration/maximal_cliques.v#X181Legacy.x181_clique_colourable`, `graph-theory-misc/theories/migration/induced_cycles.v#U13RowLegacy.two_colouring_a_graph_without_a_monochromatic_maximu_statement`, `topological-graph-theory/theories/migration/surface_embeddable.v#X138Legacy.esperet_joret_surface_triangle_free_clustered_two_colouring_statement`.

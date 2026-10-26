# Migration report: strongly-regular

Inputs: `meta/migration_reports/strongly_regular.spec.json` and `meta/library_primitives/strongly-regular.json`.
Regenerate: `python3 meta/migration_report.py strongly_regular --write`.
Full evidence: `python3 meta/migration_report.py strongly_regular --details /tmp/migration-details`.

- Canonical: `GTBase.strongly_regular.strongly_regular_parameters`.
- Baseline: `a69e27fedb17b9a509dc794b45f6e2aa5c8f4e9e`.
- Scope: 3 helpers, 2 statements, 8 frozen objects, 26 recorded references.
- Source checks: 91/91 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Hom.conjectures.U3.cores_of_strongly_regular_graphs_statement` / opg:cores_of_strongly_regular_graphs | `Hom.migration.strongly_regular.cores_of_strongly_regular_graphs_statement_compat` |
| `Spectral.conjectures.D5.triangle_free_strongly_regular_graphs_statement` / opg:triangle_free_strongly_regular_graphs | `Spectral.migration.strongly_regular.triangle_free_strongly_regular_graphs_statement_compat` |

Source repairs after migration: ONE-WAY source-repair certificates (`live -> frozen`), not migration equivalences; every other row keeps its exact iff: `Spectral.conjectures.D5.triangle_free_strongly_regular_graphs_statement` (`exists g : 'I_8 -> sgraph, (forall i, triangle_free (g i) /\ strongly_regular (g i)) /\ (forall i j, i != j -> ~ inhabited (g i ≃ g j))` -> `exists (G : sgraph) (k lam mu : nat), [/\ (0 < #|G|)%N, triangle_free G, strongly_regular_parameters G k lam mu, (0 < mu)%N & (mu < k)%N] /\ forall i : 'I_7, ~ inhabited (G ≃ known_triangle_free_srg i)`; record `meta/STATEMENT_IMPROVEMENTS.md`).

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py strongly_regular --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

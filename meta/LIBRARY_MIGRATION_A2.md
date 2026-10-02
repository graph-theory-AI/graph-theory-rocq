# Library Migration A2: Set-of-Edges Deletion

> Batch A, family A2 (normalized `delete_edges`, `delete_edges_rel`), implemented
> 2026-10-02. Frozen from 03742d1 and committed on top of 0259cec. Registry document
> `meta/library_primitives/edge-set-deletion.json`, status `deprecated` (the seven names
> stay as transparent aliases for one cycle); fidelity fragment
> `meta/foundation_fidelity/edge-set-deletion.json`. `reviewed_by` stays unset until the
> step-10 cross-review (marcol) and the coordinator's statement-theorem check are
> recorded.
>
> Compact report `meta/migration_reports/delete_edges.md`, regenerated from
> `meta/migration_reports/delete_edges.spec.json`: 221 source checks pass, and
> `--check --kernel` confirms the exact statement types and assumptions.

## Sources

All seven are frozen verbatim in `Legacy` (the graphs with their opaque symmetry and
irreflexivity proofs). Hashes are sha256 of the normalized declaration at 03742d1.
The ones checked against the baseline inventory are its `declaration_hash`.

| Definition | Original | sha256 | Now unfolds to | Helper certificate |
|---|---|---|---|---|
| `Chromatic.conjectures.X7.x7_delete_edges_rel` | X7.v:16 | `a335612d…` | `@del_es_rel G F` | `x7_delete_edges_rel_compat` |
| `Chromatic.conjectures.X7.x7_delete_edges` | X7.v:31 | `3cd6737b…` | `del_edge_set G F` | `x7_delete_edges_compat`, `x7_delete_edges_diso` |
| `Chromatic.conjectures.XE1.xe1_delete_edges_rel` | XE1.v:46 | `635ec135…` | `@del_es_rel G F` | `xe1_delete_edges_rel_compat` |
| `Chromatic.conjectures.XE1.xe1_delete_edges` | XE1.v:61 | `25db5d4e…` | `del_edge_set G F` | `xe1_delete_edges_compat`, `xe1_delete_edges_diso` |
| `Extremal.conjectures.XE1.xe1_delete_edges_rel` | XE1.v:56 | `635ec135…` | `@del_es_rel G F` | `xe1_delete_edges_rel_compat` |
| `Extremal.conjectures.XE1.xe1_delete_edges` | XE1.v:67 | `25db5d4e…` | `del_edge_set G F` | `xe1_delete_edges_compat`, `xe1_delete_edges_diso` |
| `Extremal.conjectures.X191.x191_delete_edges` | X191.v:38 | `a6c08b2b…` | `del_edge_set F X` | `x191_delete_edges_compat`, `x191_delete_edges_diso` |

The three relations are convertible with the canonical (`erefl`), and so is the
adjacency of the three `SGraph` wrappers. Each frozen graph also freezes its opaque
symmetry and irreflexivity proofs as scaffolding. The graph-construction certificates
`*_delete_edges_proofs_compat` show that the `SGraph` built from the frozen proofs is
isomorphic, through the identity, to the one built from the retained live lemmas.
They relate the two constructions; they do not claim the opaque proof terms are equal. The graphs themselves differ only in their
proof fields, so the identity is an isomorphism (`GTBase.common.del_edge_set_eq_diso`).
X191 builds the graph with `fg_mk_sgraph`, whose symmetric closure of an already
symmetric, irreflexive relation is pointwise equal to the canonical adjacency
(unconditional).

## Rows

Each frozen statement goes through frozen copies along its whole affected chain;
`Print All Dependencies` confirms that no frozen closure reaches `del_edge_set`,
`del_es_rel` or a live helper.

| Row | Statement | Chain | Per-row theorem |
|---|---|---|---|
| arxiv:2310.12891#00 (X7, partial) | `fixed_k_vertex_critical_edge_robust_statement` | `x7_edge_deletion_preserves_chromatic` | `Chromatic.migration.delete_edges.fixed_k_vertex_critical_edge_robust_statement_compat` |
| arxiv:2508.08703#00 (X7) | `six_regular_four_one_graph_statement` | `x7_four_one_graph`, `x7_no_critical_edge` | `Chromatic.migration.delete_edges.six_regular_four_one_graph_statement_compat` |
| erdos:944 (XE1 chromatic) | `erdos_944_statement` | `xe1_all_edge_critical_sets_large`, `xe1_edge_critical_set` | `Chromatic.migration.delete_edges.erdos_944_statement_compat` |
| erdos:23 (XE1 extremal) | `erdos_23_statement` | direct | `Extremal.migration.delete_edges.erdos_23_statement_compat` |
| erdos:613 (XE2, solved) | `erdos_613_statement` | `xe2_bipartite_plus_bounded_degree` (XE1 helper, cross-module) | `Extremal.migration.delete_edges.erdos_613_statement_compat` |
| erdos:742 (XE2, solved) | `erdos_742_statement` | `xe2_diameter_critical_two` (XE1 helper, cross-module) | `Extremal.migration.delete_edges.erdos_742_statement_compat` |
| arxiv:1706.05642#00 (X191, BLOCKED) | `dense_H_free_clique_blowup_subquadratic_error_statement` | `x191_subquadratic_deletion_to_partite` | `Extremal.migration.delete_edges.dense_H_free_clique_blowup_subquadratic_error_statement_compat` |

Each per-row theorem is `XnnLegacy.<statement> <-> <statement>`. The properties of
the deleted graphs move along the identity isomorphism:
- χ (X7, XE1 chromatic, X191) by `GTBase.common.chi_diso`, which upstream leaves
  unproved as `coloring.diso_chi`;
- bipartiteness (erdos 23, erdos 613) by `Extremal.migration.delete_edges.bipartite_diso`;
- balls and bounded diameter (erdos 742) by `ball_diso` and
  `xe1_diameter_at_most_diso` in the same module.

For the convertible class the frozen and live statements are also definitionally
equal; the proofs still go through the transports, so they do not depend on that.
Statement texts, doc blocks (including the X191 BLOCKED note), manifest rows and leg
states are unchanged.

## Kernel dependency evidence

`Print All Dependencies` was run through the pinned wrapper on the built
certificates, for each frozen statement and each live statement. Probe and outputs:
`/srv/graph-theory-rocq/coordination/evidence/A2-delete_edges/print_all_dependencies_{probe.sh,summary.txt,full.txt.gz}`.

| Row | Frozen closure | Live closure |
|---|---|---|
| X7 fixed_k | `Legacy.x7_delete_edges{,_rel,_sym,_irrefl}`, `X7Legacy.edge_deletion_preserves_chromatic`; no live family constant | `X7.x7_delete_edges`, `X7.x7_edge_deletion_preserves_chromatic`, `common.del_edge_set`, `common.del_es_{rel,sym,irrefl}` |
| X7 six_regular | `Legacy.x7_delete_edges{,_rel,_sym,_irrefl}`, `X7Legacy.{four_one_graph,no_critical_edge}`; none | `X7.x7_{delete_edges,four_one_graph,no_critical_edge}`, `common.del_edge_set`, `common.del_es_*` |
| XE1 erdos_944 | `Legacy.xe1_delete_edges{,_rel,_sym,_irrefl}`, `XE1Legacy.{edge_critical_set,all_edge_critical_sets_large}`; none | `XE1.xe1_{delete_edges,edge_critical_set,all_edge_critical_sets_large}`, `common.del_edge_set`, `common.del_es_*` |
| XE1 erdos_23 | `Legacy.xe1_delete_edges{,_rel,_sym,_irrefl}`; none | `XE1.xe1_delete_edges`, `common.del_edge_set`, `common.del_es_*` |
| XE2 erdos_613 | `Legacy.xe1_delete_edges{,_rel,_sym,_irrefl}`, `XE2Legacy.bipartite_plus_bounded_degree`; none | `XE1.xe1_delete_edges`, `XE2.xe2_bipartite_plus_bounded_degree`, `common.del_edge_set`, `common.del_es_*` |
| XE2 erdos_742 | `Legacy.xe1_delete_edges{,_rel,_sym,_irrefl}`, `XE2Legacy.diameter_critical_two`; none | `XE1.xe1_delete_edges`, `XE2.xe2_diameter_critical_two`, `common.del_edge_set`, `common.del_es_*` |
| X191 dense_H | `Legacy.x191_delete_edges`, `X191Legacy.subquadratic_deletion_to_partite`; none | `X191.x191_{delete_edges,subquadratic_deletion_to_partite}`, `common.del_edge_set`, `common.del_es_*` |

"None" means that no frozen closure contains `common.del_edge_set`, `common.del_es_rel`,
`del_es_sym`, `del_es_irrefl` or any live helper or chain constant of this family.

## Canonical API (GTBase.common)

The contract is in the doc comment of `del_edge_set`. New lemmas:
- `del_edge_setE` (adjacency) and `del_edge_set1` (single edge `[set e]`);
- `edges_del_edge_set` (`E(del_edge_set G F) = E(G) :\: F`);
- `del_edge_set_nonedges` (non-edges in `F` have no effect);
- `del_edge_set_eq_diso` (identity isomorphism from a same-carrier graph with the
  same adjacency);
- `chi_diso`;
- grounding: `card_del_edge_set`, `del_edge_setT` (deleting `E(G)` leaves no edge)
  and `del_edge_set_K3`, next to the existing `del_edge_set0`.

`common.v` imports (does not export) upstream `coloring` for `chi_diso`; no existing
name in `common.v` resolves differently. The public-only client
`base/theories/examples/del_edge_set.v` imports only `GTBase.common` and upstream
`coloring`. Fidelity: `GTBase.common.del_edge_set` and `del_es_rel` are FAITHFUL.

## Classified, not migrated

- Single-edge deletion: X64 `x64_delete_edge_rel`/`_graph`, X60
  `x60_delete_edge_rel`/`_graph`, and cross-name U11 `sdel_edge` (used by
  reconstruction foundations/kelly.v). Each equals `del_edge_set G [set e]`
  pointwise (`del_edge_set1`). These are deferred to their own family, because M1's
  X64 and A1's X61 frozen snapshots resolve through the X64/X60 graphs.
- `Extremal.conjectures.XE1.xe1_triangle_free_diameter_completion_edges` is dead and
  buggy (STATEMENT_IMPROVEMENTS.md:1891). It is a consumer of this family, its text is
  unchanged, and it is not repaired here.
- The six `*_delete_edges_sym` / `*_irrefl` lemmas keep their names and statements;
  they are re-proved from `del_es_sym`/`del_es_irrefl` and are not claimed.

## Knock-on edits

None outside the seven sources. The only other proof edits are the six retained
lemmas. No implication, grounding or application file unfolds these helpers.

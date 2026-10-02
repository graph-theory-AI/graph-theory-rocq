# Library Migration A3: Single-Edge Deletion

> Batch A, family A3 (normalized `delete_edge_rel`, `delete_edge_graph`), stacked on
> A2 (`dbee364`) on 2026-10-02. Registry document
> `meta/library_primitives/single-edge-deletion.json`, status `deprecated` (the four
> names stay as transparent aliases for one cycle). Fidelity reuses A2's enrollment
> of `del_edge_set` and `del_es_rel` (`meta/foundation_fidelity/edge-set-deletion.json`);
> A3 owns no fragment. `reviewed_by` stays unset until marcol's step-10 cross-review
> and the coordinator's statement-theorem check are recorded.
>
> Compact report `meta/migration_reports/delete_edge.md`, regenerated from
> `meta/migration_reports/delete_edge.spec.json`.

## Sources

| Definition | Now unfolds to | Helper certificates |
|---|---|---|
| `Chromatic.conjectures.X64.x64_delete_edge_rel` | `@del_es_rel G [set e]` | `x64_delete_edge_rel_compat` |
| `Chromatic.conjectures.X64.x64_delete_edge_graph` | `del_edge_set G [set e]` | `x64_delete_edge_graph_compat`, `x64_delete_edge_diso`, `x64_delete_edge_proofs_compat` |
| `Extremal.conjectures.X60.x60_delete_edge_rel` | `@del_es_rel G [set e]` | `x60_delete_edge_rel_compat` |
| `Extremal.conjectures.X60.x60_delete_edge_graph` | `del_edge_set G [set e]` | `x60_delete_edge_graph_compat`, `x60_delete_edge_diso`, `x60_delete_edge_proofs_compat` |

The old relation `(x -- y) && ([set x; y] != e)` equals `del_es_rel G [set e]` pointwise
for every vertex set `e`, unconditionally (`GTBase.common.del_edge_set1`). This
includes invalid `e` (empty, a singleton, three or more vertices), where both delete
nothing. Upstream `sgraph.del_edges e` deletes every edge inside `e`, so it differs for
larger `e` and is not the canonical. The four support lemmas
`x64/x60_delete_edge_sym/_irrefl` keep their statements and are re-proved from
`del_es_sym`/`del_es_irrefl`. They are frozen as each `Legacy` graph's opaque proof
scaffolding. The graph-construction certificates `*_delete_edge_proofs_compat` show that
the `SGraph` built from the frozen proofs is isomorphic, through the identity, to the
one built from the live lemmas; they do not claim the proof terms are equal.

## Rows

| Row | Statement | Chain | Per-row theorem | End-to-end theorem |
|---|---|---|---|---|
| arxiv:2511.02892#05 (X64) | `finite_bridgeless_cubic_two_homogeneous_exceptions_statement` | `x64_bridgeless` | `Chromatic.migration.delete_edge.finite_bridgeless_cubic_two_homogeneous_exceptions_statement_compat` | `..._original_compat` (M1+A3) |
| arxiv:2505.24100#01 (X60) | `induced_saturation_even_cycle_polynomial_size_statement` | direct | `Extremal.migration.delete_edge.induced_saturation_even_cycle_polynomial_size_statement_compat` | `..._original_compat` (M1+A3) |
| arxiv:2506.08810#00 (X61, cross-module) | `infinite_family_without_finite_induced_saturation_statement` | `x61_induced_saturated` | `Extremal.migration.delete_edge.infinite_family_without_finite_induced_saturation_statement_compat` | `..._original_compat` (M1+A1+A3) |

Transports along the identity isomorphism of the deleted graphs:
- connectivity (X64) by upstream `iso_connected`;
- induced cycles (X60) by `x60_has_induced_cycle_diso`, built on the new
  `GTBase.common.induced_copy_host_diso`;
- `x61_induced_free` of the deleted graph (X61) by `GTBase.common.induced_free_host_diso`.
  The deleted graph is the HOST, the first argument, of `induced_free`.

Every guard and status is unchanged: statement texts, doc blocks, manifest rows and leg
states. The end-to-end originals freeze the pre-M1 edge sets (M1's
`simple_edges.Legacy.exists_edge_set` for X64, `simple_edges.Legacy.edge_set` for
X60/X61) and, for X61, A1's frozen `Legacy.x61_induced_free`, so each one is the row as
it stood before every migration that touched it.

## Kernel dependency evidence

The report's local-closure check does not see through files, and X61 reaches the family
through X60. So `Print All Dependencies` was run on the compiled certificates for every
frozen and live row. Probe and outputs:
`/srv/graph-theory-rocq/coordination/evidence/A3-delete_edge/print_all_dependencies_{probe.sh,summary.txt,full.txt.gz}`.

| Closure | Live deletion helpers or canonical | Live M1/A1 aliases | Frozen copies reached |
|---|---|---|---|
| `X64Legacy` row | none | `x64_edge_set`, `sg_edge_set` (outside A3's chain) | `Legacy.x64_delete_edge_{rel,sym,irrefl,graph}` |
| `X64Original` row | none | none | the same, plus `simple_edges.Legacy.exists_edge_set` |
| `X60Legacy` row | none | `x60_edge_set`, `sg_edge_set` (outside A3's chain) | `Legacy.x60_delete_edge_{rel,sym,irrefl,graph}` |
| `X60Original` row | none | none | the same, plus `simple_edges.Legacy.edge_set` |
| `X61Legacy` row | none | `x60_edge_set`, `x61_induced_free`, `common.induced_free`, `sg_edge_set` (outside A3's chain) | `Legacy.x60_delete_edge_{rel,sym,irrefl,graph}` |
| `X61Original` row | none | none | the same, plus `induced_free.Legacy.x61_induced_free` and `simple_edges.Legacy.edge_set` |

Each live row reaches `common.del_edge_set`, `del_es_{rel,sym,irrefl}` and its live alias.

## Historical snapshots

M1's `Chromatic.migration.simple_edges.X64Legacy.bridgeless` froze only the edge set, and
A1's `Extremal.migration.induced_free.X61Legacy`/`X61Original.induced_saturated` froze
the induced-free chain. All of them still call the live `x64_delete_edge_graph` /
`x60_delete_edge_graph`, which A3 redirects. They are kept unchanged: their theorems
stay true and certify their own families' steps. The fully frozen rows are A3's
`X64Original` and `X61Original`. The report lists the three snapshots under known
limitations.

## Canonical API additions (GTBase.common)

- `induced_copy_host_diso`: an isomorphism of hosts maps an induced copy on `S` to one
  on a vertex set of the same size;
- `induced_free_host_diso`: induced-freeness depends on the host only up to isomorphism
  (the companion of A1's pattern-side `induced_free_diso`);
- single-edge grounding: `del_edge_set1_edge` (a real edge is removed),
  `del_edge_set1_other` (other pairs keep their adjacency), `del_edge_set1_invalid`
  (non-pairs delete nothing), `del_edge_set1_twice` (repeated deletion), with A2's
  `del_edge_set1` and `del_edge_set_K3`.

The public-only client `base/theories/examples/del_edge.v` imports only `GTBase.common`.

## Deferred

`Reconstruction.conjectures.U11.sde_rel` and `sdel_edge` (Section `G`/`e`,
`sde_sym`/`sde_irrefl`) are the same concept. They reach the Kelly and deck bridges,
`edge_reconstruction_statement` and `external_whitney_line_inversion_statement`, and are
left for a consumer-scoped follow-up.

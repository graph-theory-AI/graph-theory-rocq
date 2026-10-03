# Library Migration A8: Ordered Edge and Non-edge Counts Between Two Vertex Sets

> Batch A, family A8 (normalized `edges_between` / `nonedges_between`), implemented 2026-10-03,
> stacked on the final A7 pin `842ff4d` (A7 series `526ad18`, B8 history `66bd93c`, metadata `8ef76c7`,
> public count `842ff4d`; all unmerged). A8 does not depend on A7's content. Registry
> document `meta/library_primitives/edges-between.json`, status `deprecated` (the four names stay as
> transparent aliases for one cycle). Fidelity fragment `meta/foundation_fidelity/edges-between.json`
> enrolls `edges_between` and `nonedges_between` (FAITHFUL). `reviewed_by` stays unset until the
> independent step-10 review and the coordinator's statement check are recorded.
>
> Compact report `meta/migration_reports/edges_between.md`, regenerated from
> `meta/migration_reports/edges_between.spec.json` (baseline `842ff4d`, the real parent).

## Sources

| Definition | Old body | Relation |
|---|---|---|
| `Extremal.conjectures.X118.x118_edges_between` | `#|[set p : G * G | [&& p.1 \in A, p.2 \in B & p.1 -- p.2]]|` | conversion to `edges_between A B` |
| `Extremal.conjectures.X120.x120_edges_between` | same | conversion to `edges_between A B` |
| `Extremal.conjectures.X120.x120_nonedges_between` | `#|[set p : G * G | [&& p.1 \in A, p.2 \in B & ~~ (p.1 -- p.2)]]|` | conversion to `nonedges_between A B` |
| `Extremal.conjectures.X223.x223_edges_between` | `#|[set uv : G * G | (uv.1 \in A) && (uv.2 \in B) && (uv.1 -- uv.2)]|` | `eq_card` and `andbA` |

All four count ORDERED pairs of `A x B`. The new canonicals are `GTBase.common.edges_between` and
`GTBase.common.nonedges_between`, with exactly the X118/X120 bodies. `A` and `B` are arbitrary sets:
- they may be empty or overlap, and no disjointness is added;
- a vertex `x` of `A :&: B` gives the diagonal pair `(x, x)`, a NON-edge, since adjacency is
  irreflexive;
- an edge inside `A :&: B` is counted in both orientations.

On disjoint sets the non-edge count agrees with the number of complement edges between the sets, and the
edge count with the number of edges of `E(G)` meeting both sets. With overlap these readings can fail: a
shared vertex is a non-edge pair but no complement edge, and an edge inside the overlap is counted twice.
The edge-count reading may still agree for overlapping sets: for `A = B = [set: 'K_1]` the ordered edge
count and the unordered cross-edge count are both 0, while the ordered non-edge count is 1 and the
complement count 0. The two readings are separate lemmas, both guarded by disjointness, which is
sufficient. The X118/X120 rows keep their own `[disjoint A & B]` conjunct, and X223's `x223_ct_sparse`
keeps arbitrary, possibly overlapping sets.

Not touched:
- X223's `x223_anticomplete` is a Prop (disjoint sets with no edge between them), not a count.
- X76's and X78's `cut_size` count the edges of a cut.

## Canonical API (GTBase.common)

- `edges_between_sym`, `nonedges_between_sym`: swapping the sets keeps each count.
- `edges_nonedges_between`: the two counts partition `A x B` (`#|A| * #|B|`).
- Empty sets: `edges_between_set0`, `edges_between0`, `nonedges_between_set0`, `nonedges_between0`.
- A shared vertex is one diagonal non-edge and no edge: `edges_between_set1`, `nonedges_between_set1`.
- Complete graphs: exactly the diagonal pairs are non-edges. `nonedges_between_Kn` gives
  `#|A :&: B|`, `edges_between_Kn` gives `#|A| * #|B| - #|A :&: B|`, and `edges_between_K2` shows that
  `K_2` taken whole has its edge in both orientations.
- `edges_between_cross`: on DISJOINT sets, the number of edges of `E(G)` meeting both sets. This is the
  bijection proof formerly in `implications_X223`, adapted.
- `nonedges_between_compl`: on DISJOINT sets, the number of edges of `compl G` between the sets.
  `nonedges_between_compl_overlap` shows that the lemma cannot drop its guard: for a shared vertex the
  non-edge count is 1 and the complement count 0.

The public client `base/theories/examples/edges_between.v` imports `GTBase.base` only. It covers the
partition, swap symmetry, an empty side, a shared vertex, both disjointness-guarded readings, the
overlap counterexample, complete graphs, `K_2` taken whole (2) and its two disjoint singletons (1).

## Rows and certificates

The report tool's discovery gives four statements and two intermediate chains, frozen verbatim at
`842ff4d` in `extremal-graph-theory/theories/migration/edges_between.v`:
- `Legacy`: the four counts.
- `X118Legacy` and `X120Legacy`: the dense- and sparse-pair rows; A1's induced-free helpers stay live
  there.
- `X223Legacy`: `sparse_pair`, `ct_sparse` and the two rows `h_free_eps_bounded_sparse_pair_statement`
  and `induced_turan_even_cycle_sparse_statement`.

Certificates:
- The three X118/X120 count certificates and both of their rows are conversions.
- `x223_edges_between_compat` is `eq_card` with `andbA`.
- `sparse_pair_compat` rewrites the count, and `ct_sparse_compat` transports it under the set
  quantifiers.
- The two X223 rows are proved by setoid rewriting of their chain, with no `try`, so a missed rewrite
  is an error. The file declares local `Proper` instances for `and3`/`and4`.

Rational cross-multiplications, quantifier order, natural subtraction, zero cases, induced-free
premises and statuses are untouched.

## History and complete Originals

A1 froze the X118 and X120 rows (`Extremal.migration.induced_free.X118Legacy.statement`,
`X120Legacy.statement`) over its frozen induced-free helpers, but kept the live pair counts. Those
snapshots are documented in this family's spec, and their bodies are unchanged. The complete rows
`X118Original` and `X120Original` are the `9e03072` texts over A1's frozen `Legacy.x118_induced_free`
and `Legacy.x120_induced_free` (aliased as `A1`, not imported) and this family's frozen counts.
`<row>_original_compat` proves each one structurally, through A1's certificates, as A1's own row
certificates do. A1's spec records A8's two per-row copies, which call its live helpers, and its
compact summary is regenerated.

## Proof consumers

Statements unchanged:
- `implications_X223.x118_edges_betweenE` and `x120_edges_betweenE` keep their proofs; both sides now
  unfold to `edges_between`.
- `implications_X223.x223_edges_between_card_cross` keeps its type, with the disjointness premise, and
  is now `edges_between_cross`. The comment before the first two lemmas is updated: the three counts are
  now one definition.
- `grounding_X223.x223_edges_between0`, `edges_between_K2_gt0`, `ct_sparse_compl_K2` and
  `not_ct_sparse_K2` now unfold through `edges_between` in their proofs.
- `sparse_pair_set0` and `not_sparse_pair_K2` are unchanged.

# Library Migration A5: Ordinary Subgraph Containment

> Batch A, family A5 (normalized `subgraph_of`), implemented 2026-10-02. It sits on a private
> baseline: the merge of A4 (`5ec0f33`, with the A3 series) and Marcol's B3 (`49ddc033`). B3
> froze X98's subdivision Record, which this family's X98 history builds on. That merge is
> not part of the family: the family change is the single commit on top of it.
> Registry document `meta/library_primitives/subgraph-of.json`, status `deprecated` (the seven
> names stay as transparent aliases for one cycle). Fidelity fragment
> `meta/foundation_fidelity/subgraph-of.json` enrolls `has_subgraph` (FAITHFUL). `reviewed_by`
> stays unset until marcol's step-10 cross-review and the coordinator's statement-theorem check
> are recorded.
>
> Compact report `meta/migration_reports/subgraph_of.md`, regenerated from
> `meta/migration_reports/subgraph_of.spec.json` (baseline `49ddc033`).

## Sources

| Definition | Old body | Now unfolds to |
|---|---|---|
| `Chromatic.conjectures.X31.x31_subgraph_of` | `exists f : H -> G, injective f /\ forall x y, x -- y -> f x -- f y` | `has_subgraph G H` |
| `Chromatic.conjectures.XE1.xe1_subgraph_of` | same | same |
| `Extremal.conjectures.X59.x59_subgraph_of` | same | same |
| `Extremal.conjectures.X78.x78_subgraph_of` | same | same |
| `Extremal.conjectures.XE1.xe1_subgraph_of` | same | same |
| `GTMisc.conjectures.U13.subgraph_of` | `exists f : H -> G, injective f /\ is_hom f` | same |
| `GTMisc.conjectures.XE2.xe2_subgraph_of` | as X31 | same |

All seven are ordinary containment: an injective map from the pattern `H` into the host `G`
that sends edges to edges, with nothing required of non-edges. The canonical
`GTBase.common.has_subgraph G H := subgraph H G` takes the HOST first, the reverse of the local
`(H G)` order. Upstream `subgraph` asks only for `hom_s`, adjacency of edges with distinct
images. Injectivity and irreflexivity make that premise automatic, so
`has_subgraphP : has_subgraph G H <-> exists f, injective f /\ forall x y, x -- y -> f x -- f y`
holds unconditionally. The two forms are logically equivalent, not convertible. `is_hom` is
defined after `common.v` in `base.v`, so the characterization states its adjacency clause
explicitly (no import cycle); U13's `is_hom` unfolds to it.

## Canonical API and grounding (GTBase.common)

- `has_subgraphP`: the witness characterization; the contract is in the definition's doc
  comment.
- `has_subgraph_trans`, `has_subgraph_card` (`#|H| <= #|G|`), `has_subgraph_del_edge_set`
  (deleting edges gives a subgraph).
- Degenerate cases: `has_subgraph0` and `has_subgraph_K0` (every host contains the empty
  pattern), `has_subgraph_K0_host` (the empty host contains exactly the empty patterns).
- `has_subgraph_not_induced`: two isolated vertices form a subgraph of `K_2` but no induced
  subgraph of it. Ordinary containment is kept apart from induced containment (A1's
  `induced_free`, upstream `isubgraph`) and from minors.
- Existing: `has_subgraph_refl`, `has_subgraph_Kn`.

The public-only client `base/theories/examples/has_subgraph.v` imports `GTBase.base` only. It
covers the witness view, composition, the size bound, empty patterns and hosts, edge deletion,
ordinary-but-not-induced, and two negatives (`K_2` does not fit in `K_1`; an edge does not fit
in an edgeless host of the same size).

## Rows and certificates

The report tool's own discovery gives 35 affected statements. Certificates sit in
`{chromatic-theory,extremal-graph-theory,graph-theory-misc}/theories/migration/subgraph_of.v`;
each helper is frozen verbatim at `49ddc033` in `Legacy`:

| Area | Frozen modules | Statements |
|---|---|---|
| chromatic | `X31Legacy`, `XE1Legacy`, `XE2Legacy` (XE2 reaches XE1's helper across modules) | 7 |
| extremal | `XE1Legacy` (six chains, prefix dropped, and 13 statements), `XE2Legacy` (9, across modules), `X59Legacy`, `X78Legacy`, `X96Legacy` and `X98Legacy` (X96/X98 reach X59's helper across modules), `X98Original` | 26 |
| misc | `U13Legacy`, `XE2Legacy` | 2 |

The six extremal XE1 chains are `graph_ramsey`, `graph_ramsey_number`,
`diagonal_ramsey_number`, `c4_forcing_min_degree`, `turan_number_for_graph` and
`min_turan_over_size_edges`. Their Ramsey and Turán minimality clauses are frozen whole.

Each helper certificate is `iff_sym (has_subgraphP G H)`. Each chain and statement certificate
transports that iff through the unchanged statement by setoid rewriting under the logical
connectives. Each certificate file declares local `Proper` instances for `and3`/`and4`, so the
`[/\ ...]` forms (X78, X96, U13) are covered. Rewriting uses Corelib's `Setoid`/`Morphisms`
and no axiom; every certificate prints "Closed under the global context". Per-row theorems
are `XnnLegacy.<formal_name> <-> <formal_name>`; quantifiers, Ramsey minimality, negated
subgraph predicates, polynomial, degree and girth bounds, nonempty guards, statuses and
documented limitations are untouched.

## X98 and the B3 history

B3 (`49ddc033`) froze X98's subdivision Record (type, constructor, seven fields), its
`inhabited` wrapper and the statement, in `Extremal.migration.consecutive_in_path.X98Legacy`.
That statement copy still calls the live `x59_subgraph_of`, so after A5 it is a documented
snapshot limitation in this family's spec. Its theorem stays true and certifies B3's step; its
frozen body is not edited. A5 adds:
- `X98Legacy.polynomial_kuhn_osthus_induced_subdivision_statement`, the per-row copy with this
  family's frozen helper and the live (post-B3) Record;
- `X98Original.polynomial_kuhn_osthus_induced_subdivision_statement`, the combined pre-B3,
  pre-A5 row. It uses B3's frozen `X98Legacy.induced_subdivision` and this family's
  `Legacy.x59_subgraph_of`, and is certified by
  `polynomial_kuhn_osthus_induced_subdivision_statement_original_compat` through B3's
  `x98_induced_subdivision_compat`.

The row's other helpers (`average_degree_geq`, `x59_poly_eval`, `KB`) are untouched. M1
edge/count aliases in other rows (for instance `x4_edge_count` in X96 and the XE1 Turán
chain) stay live, so no row here is described as a pre-M1 original.

## Proof consumers

Statements unchanged:
- `GTMisc.conjectures.grounding_U13.subgraph_of_refl` now builds its witness through
  `has_subgraphP`.
- Atlas e117 (`implications_A1.subgraph_of_large_average_degree_and_large_average_d_implies_chromatic_girth_average_degree_subgraph`)
  destructs U13's embedding and builds X31's through `has_subgraphP`; the argument (compose
  with `val`) is the same.

## Kernel evidence and gate notes

`Print All Dependencies` of the frozen and live statements and `Print Assumptions` of every
certificate, run through the pinned image, are kept outside the repository in
`/srv/graph-theory-rocq/coordination/evidence/A5-subgraph_of/`.

On the committed tree:
- the certificates and API print "Closed under the global context" (9 + 36 + 4 certificates, 16 API and client
  theorems);
- every frozen statement closure avoids the live helpers, the six live XE1 chains and the canonical, while every
  live closure reaches `has_subgraph`;
- `subgraph_of --check --kernel` passes 504/504 with the exact types.

The broad atlas build stops at a missing `digraph-theory` prerequisite of the unrelated `implications_A2`, which
is not built in the review tree. The exact `implications_A1.vo` target (e117) is forced through the atlas project
flags; it keeps its type and its assumptions are closed. No full atlas build is claimed.

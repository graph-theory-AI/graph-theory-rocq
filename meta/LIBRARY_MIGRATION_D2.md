# D2: supplied-partition uniform hypergraphs

D2 is implemented on the fixed D1 pin `e53098e84635d8612e34e5d239fd13fe5afa9fb8` (mathematical
baseline C25 `3be65ee`). It is the new `partite-uniform-hypergraph` shard.

The canonical is the existing public `Hypergraph.foundations.hypergraph.hg_partite_uniform`; its
definition, Section discharge `T k part E` and Arguments are unchanged. For a supplied map
`part : T -> 'I_k` and family `E`, every member meets each class in exactly one vertex. No
existential partition, positive rank, nonempty family, balance, surjectivity or no-isolated-vertex
guard is added. At rank 0 the carrier is empty and every family qualifies, the singleton empty edge
included. The API next to the definition covers: empty family, subfamilies, vertex deletion,
member cardinality and D1 `uniform_family` (no `0 < k` premise), a per-class witness, an onto map
and `k <= #|T|` under a member premise, rank 0, and the identity-partitioned full edge.

U12's `r_partite_uniform` and X6's `x6_r_partite_uniform` unfold to it through a qualified
`Require` without Import, so U12 keeps its own Berge `hg_connected`.

Frozen at D1 are 3 sources and 6 complete current rows (U12 Ryser, X6 Lovasz deletion and its
trade-off, X72, X73, X225 #01), plus 2 complete A10+D1+D2 Originals:
- X73: the raw partite copy with A10's actual `X73Legacy.hyperdegree_regular`.
- X225 #01: the raw partite copy with D1's actual `UniformLegacy.hg_uniform`/`hg_turan` and A10's
  actual `FoundationLegacy.dmax`, whose Qed-opaque witness is reused.

That gives 8 whole-statement iffs; the Originals reuse the A10/D1 whole iffs by conversion. The 11
certified A10/D1 support objects are listed in the historical role. A10's `degree_le` and
`degenerate_card` occur only inside the opaque witness and have no certificate of their own.

The four older partial snapshots stay byte-exact with notes, and reciprocal notes are added in A10
and D1. Consumer types and proofs are unchanged, including the nine direct headers and the Atlas
cops bridge. X225 keeps both hypotheses; statuses, legs and docs are unchanged. The client is
`hypergraph-theory/theories/examples/supplied_partitions.v`. Regenerate with
`python3 meta/migration_report.py partite_uniform --write`. Evidence: coordination
`evidence/D2-by-lancelot/`.

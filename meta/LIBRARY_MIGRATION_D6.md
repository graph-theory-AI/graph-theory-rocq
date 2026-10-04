# D6: matchings of a supplied hyperedge family

D6 is implemented on the fixed D5 pin `e14645d6fb6068c1a89862f60b82e958212f2422`. It completes the deferred
`hypergraph-edge-family` class of the existing `matching` shard, the last compiled class of that registry.

The canonical is the new public `Hypergraph.foundations.hypergraph_matchings.hg_matching M E`: `M` is a subfamily of the
hyperedge family `E : {set {set T}}` and its distinct members are pairwise disjoint. That is the unchanged body of both
sources, over any finite carrier, with `M` before `E`. The disjointness clause is exactly MathComp's `trivIset`
(`hg_matchingP`, through `trivIsetP`). MathComp's `partition` (no `set0`, covering) and the simple-graph upstream
`matching` (genuine edges) are different notions, and with no second-area consumer the canonical stays in Hypergraph.
There is no uniformity, positivity, nonempty-edge, covering or maximality guard, so the empty hyperedge may be a member.
The public client shows the empty family, singletons (the empty hyperedge included), the empty carrier against the empty
family, overlapping members, both monotonicities and the reflection.

`U12.hg_matching` (new normalized name `hg_matching`) and `X6.x6_matching` are now qualified aliases. Frozen in
`Hypergraph.migration.matching` at the D5 pin, with every text byte-identical at the family baseline `9e03072` where it is
bound:
- the 2 sources;
- the 4 matching-number, no-k-matching and extremal chains, kept as chains;
- the 5 complete current rows: U12 Ryser, X6 Lovasz deletion and its trade-off, X6 #1020 and X73;
- the complete original extremal chain and 5 complete Originals over the actual raw D2 partite, D1 `x6_uniform` and A10
  X73 regularity constants, which are borrowed through the aliases `PU`/`UH`/`ID`.

That is 17 owned and 5 borrowed objects (matching 26 -> 48 mappings, 16 rows), with 5 current and 5 complete Original
whole iffs. All 17 bridges are conversions.

No older proof needed adaptation: the 17 old consumer proof headers in 5 files compile unchanged, including the verified
deletion-tradeoff -> Ryser edge. `consumers_remaining` goes 15 -> 16 (U12's `is_matching_number`). The eight older
partial snapshots (A10, D2 and D1) keep their texts and receive notes. Reciprocal notes are added to D2 (+4), D1 (+2) and
A10 (+1), and D5's three notes are kept. Only X6's distinct-variant entry is removed (X15alone stays excluded). The old
C1/C24/C25 "deferred"/"now" prose is marked historical. Statuses, legs, docs and guards are unchanged.
Evidence: coordination `evidence/D6-by-lancelot/`.

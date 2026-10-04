# D4: monochromatic copies of a supplied hypergraph

D4 is implemented on the fixed D3 pin `598d668fa9225c8271852c856ce3990c7fa7890e`. It is the new
`monochromatic-copy` shard.

The canonical is the new public `Hypergraph.foundations.hypergraph_copies.hg_mono_copy E col`. For a
colouring `col : {set U} -> C` of all subsets of a finite host and any palette, some colour and some
injection of the whole pattern carrier send every member `e` to a host set `f @: e` of that colour.
It has no uniformity, nonempty, palette-size or no-isolated guard. For an `eqType` palette,
`hg_mono_copyP` proves it is the existing `hg_containsb` in one colour class. The API and client
cover the empty family (copy iff injection), empty pattern or host, a larger pattern, subfamilies,
relabelling, the bool/`'I_2` bridge and the impossible `'I_0` colouring (so q = 0 forcing stays
vacuous).

X108/X117 (bool) and X119 (`'I_q`) `monochromatic_copy` are now aliases of it; the bool ones are the
same term, so `x117_monochromatic_copyE` stays a conversion. Frozen at D3 are 3 sources, 5
forcing/Ramsey chains and 3 complete current rows, giving 3 new whole iffs, all conversions. The
complete histories are D3's existing X108ImageOriginal, X119ImageOriginal and complete
X117ImageLegacy rows, reused at `9e03072` with D3's certificates (3 reused whole iffs), together
with their D3/D1/A10 support (historical role).

**Proof adaptation:** three proof lines of D3's copy certificates in `migration/image_edge.v` were
adapted, with statements unchanged, because the live copies now unfold to `f @: e`. D3's `image-edge`
registry `consumers_remaining` drops 3 -> 0. The C8 spec drops the three now-owned distinct
variants, and C8's registry notes name the new owner. The four older snapshots keep their notes,
and reciprocal D3/A10/D1 notes are added. Evidence: coordination `evidence/D4-by-lancelot/`.

# D5: forcing a monochromatic copy under every colouring

D5 is implemented on the fixed D4 pin `7647f2bd8507b2b2ebab4f2a7b92f1f8cf7ae95b`. It is the new
`forces-mono` shard.

The canonical is the new public `Hypergraph.foundations.hypergraph_forcing.hg_forces_mono E U C`:
every colouring `col : {set U} -> C` of all subsets of a finite host `U`, by any palette `C : Type`,
has D4's `hg_mono_copy E col`. Host and palette are explicit arguments. It has no inhabited-palette,
positive-q, uniformity, nonempty or no-isolated guard. An empty palette forces vacuously, so X119's
q = 0 Ramsey predicate holds exactly at R = 0. A singleton palette forces iff the carrier injects,
and any carrier bound takes an explicit colour (`hg_forces_mono_card`). The client also shows
elimination, subfamilies, empty patterns and the bool/`'I_2` transport through inverse maps.

X108's `x108_two_colour_ramsey_at_most`, X117's `x117_forces_mono` (both bool) and X119's
`x119_forces_mono` (`'I_q`, keeping `E q N`) are now aliases of it. Frozen at D4 are 3 sources, the
2 Ramsey-number chains (forcing and minimality, kept as chains) and 3 complete current rows, giving
3 new whole iffs, all conversions. The complete histories are D3's existing X108ImageOriginal,
X119ImageOriginal and complete X117ImageLegacy rows, reused at `9e03072` with D3's certificates (3
reused whole iffs), together with their D3/D1/A10 support (historical role).

No older proof needed adaptation; D4's three reviewed D3 adaptations are kept. D4's
`monochromatic-copy` `consumers_remaining` drops 3 -> 0. The four older snapshots keep their notes,
and reciprocal D3/D4/A10/D1 notes are added. Statuses, legs, docs, guards and the opaque
`x119_sqrt_ex` witness are unchanged. Evidence: coordination `evidence/D5-by-lancelot/`.

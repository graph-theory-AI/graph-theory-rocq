# D1: uniform finite hypergraphs

D1 is implemented on the tooling prerequisite `277986293d4d5e97b5381db21d35dcd8da95ace9`. The
mathematical baseline and the public descriptor pins are C25
`3be65eed7084abfae36dee74f7117b598325bc4c`. It completes the proposed `uniform-hypergraph` shard.

The canonical is the focused `GTBase.hypergraph_uniformity`, imported explicitly. It defines
`uniform_family E k := forall e, e \in E -> #|e| = k` over an arbitrary finite type, the Boolean
`uniform_familyb` (reflected by `uniform_familyP`), and the same-body indexed
`uniform_incidence inc k` with the injectivity-free image bridge `uniform_incidence_imageE`. No
nonempty, rank, loopless, isolated-vertex, inhabitance or partiteness guard is added.

The eight local set-family helpers and the public `hg_uniform`/`hg_uniformb` (same Section
argument order) unfold to the canonical. U5's `uniform_hg H d` unfolds to
`uniform_incidence (@hinc H) d` over the unchanged Record.

Frozen at C25 are 11 sources, 7 chains (including the natural-valued `hg_turan`) and 20 complete
current rows. Each phase sits in a module importing only its own conjecture file, so U12's
edge-connectivity `hg_connected` stays U12's. Five complete Originals reuse the A9/A10 frozen
modules through the aliases `CS`/`ID`: X209 (`CS.X209Legacy.scaled_excess`, keeping the unused T'
and outer E'), X6 #834 and XE2 #833 (`ID.Legacy.x6_hg_degree`), X108
(`ID.X108Legacy.d_degenerate`) and X225 #01 (the frozen `hg_turan` with the actual
`ID.FoundationLegacy.dmax`). That gives 25 whole-statement iffs.

All 37 actual consumers keep their types and proofs. The A9/A10 partial snapshots are byte-exact,
with reciprocal stale notes; A9's `x209_uniform` distinct-variant entry was removed because D1 now
owns it. Statuses, legs, docs, defects and annotations are unchanged. The public client is
`base/theories/examples/hypergraph_uniformity.v`. Regenerate with
`python3 meta/migration_report.py uniform_hypergraph --write`. Bindings are in the spec, and
evidence is in coordination `evidence/D1-by-lancelot/`.

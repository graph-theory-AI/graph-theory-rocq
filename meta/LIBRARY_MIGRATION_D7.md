# D7: the finite hedgehog hypergraph

D7 is implemented on the fixed D6 pin `eaa6564c3788f6e3e2db7a7bddbe9adba157c334`. It is the new `hedgehog` shard.

The canonical is the new public `Hypergraph.foundations.hedgehog`, with the carriers of the X117 vocabulary unchanged:
- `hedgehog_spike t`: the subtype `{p : 'I_t * 'I_t | p.1 < p.2}`;
- `hedgehog_vertex t`: the sum `'I_t + hedgehog_spike t`;
- `hedgehog_edge s`: the tagged triple `[set inl i; inl j; inr s]`;
- `hedgehog_edges t`: the image family `[set hedgehog_edge s | s : hedgehog_spike t]`.

Finite structures are MathComp's subtype, sum, set and image instances, inferred by unfolding as before (no new
instance). There is no positivity or rank guard: `t = 0` is empty and `t = 1` has no edge. The API proves that each edge
has three vertices, that its spike vertex identifies it (so construction is injective), membership in the family, rank
three, and the vertex and edge counts. The public client covers `t = 0, 1, 2` and 3-uniformity, stated with D1's
`uniform_family` and vacuous for `t < 2`.

`x117_spike`, `x117_vertex`, `x117_edge` and `x117_edges` are now qualified aliases. Their Type-valued and dependent
headers are unchanged. Frozen in `Hypergraph.migration.hedgehog` at the D6 pin (the family baseline):
- the 4 raw constructors, which call one another only through `HedgehogLegacy`;
- the Ramsey chain (forcing at R and minimality) and the complete current row, which keep the live D5 forcing;
- the complete D3+D4+D5+D7 Original chain and row, over the raw constructors and D3's actual frozen
  image/copy/forcing (3 borrowed objects, alias `IM`).

That is 8 owned and 3 borrowed mappings, with 2 whole iffs (current and full Original). Both rows keep the epsilon
guards, threshold order, least R, truncated `2 * e2 - e1` and both powered bounds. The source certificates are
equalities by conversion. The current chain and row are conversions. The Originals transport through D3's forcing
bridge `x117_forces_mono_compat`, as D3's own proofs do.

No older proof needed adaptation. The six older partial snapshots (Ramsey chain and row in D3 `X117ImageLegacy`, D4
`X117CopyLegacy` and D5 `X117ForcingLegacy`) stay byte-exact and get notes. Reciprocal notes are added to D3, D4 and D5
(+2 each). The registry envelope also covers `GTMisc.conjectures.X87.x87_edge` (normalized `edge`), an ordered Boolean
edge lookup; it is a deferred class and its source and row are untouched, so the status is `migrating`. All D6 additions
are unchanged. Statuses, legs, docs and guards are unchanged. Evidence: coordination `evidence/D7-by-lancelot/`.

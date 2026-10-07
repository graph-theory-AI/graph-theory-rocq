# D10: attained Ramsey numbers of a supplied hypergraph

D10 is implemented on the fixed (unmerged) D9 pin `eae6c3ae123de43cad5ac0675ee25ab3f48c7b10`. It is the new
`ramsey-number` shard (normalized name `ramsey_number`).

The canonical is the new public `Hypergraph.foundations.hypergraph_ramsey.hg_ramsey_number E C R`: the host `'I_R` forces a
monochromatic copy of `E` under the palette `C : Type` (D5 `hg_forces_mono`), and every forcing host size `N` has
`R <= N`. `R` is supplied: there is no existence theorem, choice or minimum extraction. The carrier, family and palette are
arbitrary, with no guard. The API gives:
- attainment, minimality and uniqueness;
- with an empty palette, the minimum 0;
- with a colour and the empty family, the minimum `#|T|`, because the whole carrier must still inject.

The public client covers the empty carrier, the singleton empty edge and a Boolean example. It also shows that forcing
alone, or minimality alone, is not the attained minimum.

`X117.x117_ramsey_number` (`bool`, the hedgehog family) and `X119.x119_ramsey_number` (`'I_q`, arbitrary `E`) are now
qualified aliases with unchanged headers and implicit arguments. Frozen in `Hypergraph.migration.ramsey_number` at the D9
pin (the family baseline):
- both sources, which keep the live D5 forcing and D7 hedgehog aliases;
- the complete X117 row: positive `e1`/`e2`, the threshold, least `R`, both bounds and the truncated subtraction;
- the complete X119 row: `q >= 2`, `cq` before `T`/`E`, live D1 uniformity, the no-isolated guard and the opaque
  `x119_sqrt` tower.

The complete histories are the existing deepest Originals, reused unchanged with their genuine iff: D7
`X117HedgehogOriginal` and D3 `X119ImageOriginal`, with their 13 raw supports in the historical role. That is 4 owned and
15 borrowed mappings, with 4 whole iffs.

No older proof needed adaptation: the ten reverse files compile unchanged. D5's `forces-mono` `consumers_remaining` goes
3 -> 1. D1's `X119UniformLegacy` row, which still calls the live `x119_ramsey_number`, gets a note. Reciprocal notes are
added to D1 (+1), D3/D4/D5 (+4 each) and D7 (+2). Extremal `x195`/`x215_ramsey_number` are deferred graph-arrow classes of
this owner and are untouched, so the status is `migrating`.

The inherited D9 report diagnostics (regularity 138/139 and cycle_edges 334/335, report-tool lexical attribution) are
unchanged and recorded separately. Evidence: coordination `evidence/D10-by-lancelot/`.

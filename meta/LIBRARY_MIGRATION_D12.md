# D12: spanning edge-colour classes (first stage of the colour-class promotion)

D12 is implemented on the fixed (unmerged) D10 pin `2f37b10a711c81b9bfb6dcb1581ac2c527974baa` as the new
`edge-colour-class` shard (normalized names `edge_colour_rel`, `colour_graph`).

The canonical is `GTBase.edge_colourings.edge_colour_class col p`, with adjacency `edge_colour_class_rel col p`
`= (x -- y) && p (col [set x; y])`. It is the reviewed contract of `Extremal.foundations.edge_colourings.colour_class`,
promoted under distinct names so that no file importing both modules rebinds a short name:
- the spanning host carrier, so isolated vertices stay;
- a total set map `col : {set G} -> C` over an arbitrary `eqType` palette;
- a colour predicate `p`.

There is no guard. All pre-existing `GTBase.edge_colourings` declarations are unchanged; the file is append-only. The API
covers:
- adjacency;
- the edge set and its `p` / `predC p` split;
- the identity transport, which computes;
- off-edge irrelevance;
- the `predT` / `pred0` / single-colour / constant-colouring corners.

A public client covers edgeless, empty and small concrete hosts and the empty palette.

The six helpers `x34`/`x212`/`x23_edge_colour_rel col i` and `_colour_graph col i` are now qualified aliases at
`p := pred1 i`, with headers and implicit arguments unchanged. Their adjacency is the frozen one by conversion. The graphs
carry different opaque symmetry/irreflexivity proofs, so they are related only by the identity isomorphism, never equated.
The six local sym/irrefl lemmas keep their headers and are now proved by the canonical lemmas. These are the only
proof adaptations; their original scripts are frozen with the Legacy relation.

Frozen in `<area>/theories/migration/edge_colour_class.v`:
- the six sources and six opaque lemmas;
- the linear-forest and linear-arboricity chains, as frozen dependencies only, not newly owned;
- the three rows.

There are four whole iffs:
- the X34, X212 and X23 current rows, by kernel-checked conversion (`is_forest` and `Delta` read only the carrier and the
  adjacency);
- the complete `X34Original`, over M1's frozen raw edge set `simple_edges.Legacy.exists_edge_set` (the X34 text at
  `061154c`).

The X34 Original keeps:
- the same colouring for the widened linear-forest colours and the `ord_max` matching;
- the exact `let q`;
- the planar / odd / `9 <= Delta G` guards, with the documented 9-vs-7 defect.

X212 and X23 keep:
- the supplied total colouring;
- the attained AND universal minimum;
- all of their guards.

There are 26 owned mappings and 1 borrowed one.

One truthful lexical note is appended to the regularity spec: the new frozen X212 row uses `GTBase.base.regular`, which is
the approved D9 wording. No other existing spec, registry or certificate changes. The status is `migrating`: the
same-contract public adapter for Extremal `colour_class` is pending as the next stage of this family. The inherited D9
report diagnostics are unchanged. Evidence: coordination `evidence/D12-by-lancelot/`.

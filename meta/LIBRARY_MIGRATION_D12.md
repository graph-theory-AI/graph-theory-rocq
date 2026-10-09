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
same-contract public adapter for Extremal `colour_class` was then pending as the next stage of this family (done below). The inherited D9
report diagnostics are unchanged. Evidence: coordination `evidence/D12-by-lancelot/`.

## Second stage: the Extremal public adapter

This stage is implemented on the first-stage pin `7cf3dfc5d1117e061b002c8aa758646713302438`, within the same family and
owner.

**Adapter.** `Extremal.foundations.edge_colourings.cc_rel col p` and `colour_class col p` are now transparent public
adapters of `GTBase.edge_colourings.edge_colour_class_rel col p` and `edge_colour_class col p`. They keep the original
Section binders `(G : sgraph) (C : eqType)` and `(col : {set G} -> C) (p : pred C)`, the spanning carrier and
`Arguments colour_class [G C] col p`. The public names `cc_rel` and `colour_class` are kept.
- `cc_sym` and `cc_irrefl` keep their headers and are proved by the promoted lemmas. Their original scripts no longer
  apply once `cc_rel` is an alias; these are the only adaptations.
- Every other API, client and consumer script compiles unchanged: the foundation lemmas, `implications_X215` (gc:e239),
  the groundings, X195/X196/X215/X229, `implications_X223` and the C6 certificate.

**Frozen Section.** The whole original Section `ColourClass`, unchanged since `3011c28`, is frozen in
`extremal-graph-theory/theories/migration/edge_colour_class.v`. The modules are dependency-ordered (`Legacy`,
`ProofsLegacy`, `GraphLegacy`, `ApiLegacy`) and each repeats the Section binders; cross-references are qualified.

**Certificates.**
- Adjacency `=2`, by conversion.
- The identity isomorphism, which computes to the identity.
- SGraph-to-SGraph isomorphisms for the opaque proofs.
- The X229 row (arxiv:2309.04460#01), by kernel conversion; `connected` reads only the carrier and the adjacency.
- The complete X229 Original over C6's raw `Legacy.proper_ecolouring` at `3011c28`, qualified and not imported. It keeps
  one positive uniform `C` before every host, palette and colouring, robust expansion, every `L` with
  `2 ^ L <= #|G|`, the exact density bound, and one `P` whose two complementary spanning classes are connected.

**Mappings.** 7 are appended: 2 public repository sources (enrolled at the family baseline `2f37b10a` with the original
blob and declaration hashes), 2 opaque supports, the current row, the borrowed C6 provider, and the Original. That gives
34 mappings and 6 whole iffs.

**Notes.**
- The C6 `X229Legacy` snapshot, which keeps the live `colour_class`, gets a note in this family's spec.
- The new current X229 snapshot, which keeps C6's live `proper_ecolouring`, gets a reciprocal note in the C6 spec.
- The C6 certificate file and all C6 mappings are unchanged.

**Registry.**
- Both classes are migrated aliases.
- The status is `deprecated`.
- `consumers_remaining` is 17, derived from the inventory.

**Prose.** Two root-requested qualifications, with no change to the mathematics:
- under a constant colouring only the chosen colour's class can be nonempty, and an edgeless host has none;
- the evidence wording separates the 23-file discovery closure from the actual 55-consumer closure of the public append.

The promotion is not claimed complete until the reviewed gates pass on the integrated parent.

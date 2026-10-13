# Edge copies and list edge-decompositions

This family is based on the simple-cut family's parent `423936c66e0df86dff050496e86421193ebb1bcd`.

## The public owner: `GTBase.edge_copies`

- **`edge_image f`** is the set of 2-element vertex sets `[set f x; f y]` over the adjacent pattern pairs.
- **`injective_edge_image T F`** (X47's copy) asks for an injective map whose image is `F`. The image edges need not be host edges.
- **`embedded_edge_copy T A`** (X212's copy) also preserves adjacency, so its image lies in `E(G)`.

**Two list conventions are kept separate**, because neither is a strengthening of the other:
- **`edge_decomposition_by_equal_parts`** (X47): parts are injective images inside `E(G)`, they cover `E(G)`, and two parts that share an edge are equal. A list may therefore repeat an identical part.
- **`edge_decomposition_exact`** (X212): every member is an embedded copy, and every 2-element set is counted exactly as often as it is a host edge. A repeated nonempty part is excluded; repeated empty parts are allowed.

No tree, nonempty-pattern, connectedness or nonempty-part guard belongs to these definitions.

**API:**
- the image membership and its nested-quantifier form (`injective_edge_image_nested`);
- host-edge containment, and the equivalence "injective image inside `E(G)`" ⇔ embedded copy;
- the undup transport from equal parts to the exact count;
- the empty-host and self decompositions, and the refutation of a doubled part under the exact count;
- `tree_has_edge`.

**The public examples ground:** an injective image outside the host; a repeated `K_2` part accepted by equal parts but refused by the exact count; empty hosts with the empty list; repeated empty copies of the one-vertex tree; and the edge of a two-vertex tree.

## Rows and history

**The rows.** X47, X48 and the Barat-Thomassen row keep their quantifier order and guards:
- X47 and X48 keep their positive pattern edge count;
- the Barat-Thomassen row keeps `0 < #|T|`, its existential `k` and its divisibility hypothesis.

**What is frozen.** The five source definitions are frozen verbatim at the base in `Packing.migration.edge_copies` and `Cycle.migration.edge_copies`, as are the three complete rows. Every frozen object has a whole-object equivalence. X47's nested-quantifier image equals the public pair-form image by proof; the X212 bodies are kernel conversions.

**The X47/X48 Originals** are the deepest valid texts. They compose this family's raw copy with M1's raw edge set, A11's raw minimum degree and the simple-cut family's raw cuts. The earlier certificates (simple edges, minimum degree, simple cuts) are not edited; their snapshots keep the live helpers they froze.

**The X212 definitions and the Barat-Thomassen row** are unchanged since their creation and use no earlier migrated helper, so their frozen copies are their deepest originals.

## The Atlas boundary

`Atlas.foundations.tree_decompositions` imports no conjecture module. Its seven declarations keep their names, binders and proofs' role for `Atlas.conjectures.implications_A1`, and are stated over:
- `E(G)`;
- `GTBase.simple_cuts.cut_edges`;
- `GTBase.edge_copies`'s equal-part and exact-count decompositions.

The X47 and X212 names are aliases of these. Six former types hold by conversion with their former bodies.

**The exception is `x47_decomposition_x212`.** Its former premise used X47's nested-quantifier copy image, which equals the pair-form image only by proof (`x47_copy_edge_set_compat`). Its former contract is therefore recovered through `x47_tree_decomposition_by_copies_compat` and `x212_decomposition_into_copies_compat`, not by conversion. The same holds for the former contracts of the two X47/X48 → Barat-Thomassen edges of `implications_A1`, through the whole-row certificates.

Both direction-sensitive implication edges of `implications_A1` keep their statements.

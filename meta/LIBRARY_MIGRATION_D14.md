# D14: linear forests (first three-row stage)

D14 is implemented by Arthur on the working base A28P `1123673d3b2910361a05bc5381fdecd68c610951` (master go
`master-D14-implementation-go.md` 1b6f63a0; contract readback receipt 15a4ec56), as the new `linear-forest` family
(normalized name `linear_forest_colour`). Before review and READY it is refreshed onto the final parent (the reconciled main
after D13 and PR27) by merging that parent in, and its re-derivation is rerun there.

**Canonical.** `GTBase.path_trees.linear_forest G := is_forest [set: G] /\ Delta G <= 2`, appended to the existing
`path_trees` module (`path_tree` and its API unchanged): no connectedness, nonemptiness or size guard. API: projections,
`linear_forestI`, the degree form `linear_forestP` (through `Delta_le2P`), `path_tree_linear_forest`, `path_treeP`
(`path_tree G <-> linear_forest G /\ connected [set: G]`), `linear_forest_edgeless`, K0/K1/K2 positives, triangle and claw
negatives. The public client (`base/theories/examples/path_trees.v`) adds an unused colour class: the whole host carrier,
no edge, a linear forest.

**Aliases.** X34, X212 and X23 `xNN_linear_forest_colour col i` are now `GTBase.path_trees.linear_forest
(xNN_colour_graph col i)` through a qualified `Require GTBase.path_trees` (no Import), over D12's live colour class; headers
and implicit arguments unchanged; no proof adaptation.

**Mappings (36).** Owned (11), frozen at the baseline in `<area>/theories/migration/linear_forest.v`: the three sources,
five chains (X34 `linear_forests_and_matching`; X212/X23 `linear_arboricity_at_most`, `linear_arboricity`) and three current
rows, each certified by kernel-checked conversion. Borrowed (25) with their exact D12 descriptors and certificates, unchanged.
Six whole iff: the three current rows and D12's complete `X34Original` (M1 raw edge set, 061154c), `X212Legacy` and
`X23Legacy` (2f37b10a). Every guard is kept, including the q = 0 impossibility, the attained and universal minimum, X34's
widen_ord / ord_max split with the documented 9-vs-7 defect and X212's documented k = 0 divergence; nothing is repaired.

**Metadata.** Three reciprocal stale-snapshot notes in D12's spec (the new frozen sources keep D12's live colour class); the
regularity lexical note (the new frozen X212 row uses `GTBase.base.regular`); path-tree's three colour-class
`distinct_variants` leave that list (now owned here) with a summary line, and its registry prose names the new owner.
Later classes of this owner, not migrated here: Digraph `path_fas.linear_forest` and GTMisc X74 `x74_induced_linear_forest`.
No generated file is committed. Evidence: coordination `evidence/resume-2026-10-06/D14-*-by-arthur/`.

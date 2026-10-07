# D9: local neighbourhood regularity of an infinite graph

D9 is implemented on the fixed D8 pin `216204c1dfe3a483cc952446ff1f494397ccc7a8`. It extends the existing `regularity`
owner (D8) by migrating its deferred `infinite-neighbour-enumeration` class.

The canonical is the new public `Infinite.foundations.regularity.iregular r G`, defined on the existing
`Infinite.foundations.igraph` carrier, which is unchanged. Every vertex has an injective `'I_r` enumeration of exactly
its neighbours, with both directions of coverage. The enumerators are local and existential: there is no global
selection, choice or decidability, and `r` comes before `G`. There is no guard: an empty carrier is regular at every
`r`, and `r = 0` means no adjacency. The API derives `finite_sub` of each neighbourhood from the same enumerator. The
public client covers the empty graph, degree 0, an inhabited edgeless graph rejecting positive degrees, the single
edge with an `'I_1` enumeration, and local finiteness.

`Infinite.conjectures.D4inf3.regular` is now a qualified alias with an unchanged header. Frozen in
`Infinite.migration.regularity`:
- the source;
- the complete row, with both outer existentials and all five conjuncts: `2 < r`, `locally_finite`, `regular`,
  `one_ended` and the documented spanning-double-ray `uniquely_hamiltonian` proxy.

These are 2 owned mappings with 1 whole iff, both conversions. Their effective commit is the family baseline
`7e030f2`, frozen at `216204c` (descriptive only); the source and its whole closure are byte-identical at both. With
the finite class, the owner has 9 mappings and 3 whole iffs. The finite descriptors, baseline, notes and reviews are
unchanged. Both classes are now migrated, so the status is `deprecated`.

No older proof needed adaptation: the five reverse files (21 old headers) compile unchanged. The short name `regular`
is also `GTBase.base.regular`. The repository-wide lexical scans reach 31 non-migration files and 15 frozen bodies
outside the actual D4inf3 reverse closure; they are declared as lexical matches only. Evidence: coordination
`evidence/D9-by-lancelot/`.

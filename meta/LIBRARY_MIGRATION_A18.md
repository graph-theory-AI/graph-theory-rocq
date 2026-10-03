# Library Migration A18: Inclusion-Maximal Cliques

Batch A family A18, on the fixed A17 pin `1f4e9c1` (no private union). Registry
`meta/library_primitives/maximal-clique.json`; spec, hashes and per-row certificates:
`meta/migration_reports/maximal_cliques.{spec.json,md}`; API contracts are in the Rocq doc comments.

- **Contract.** `GTBase.maximal_cliques` is a thin adapter over MathComp `maxset` of `cliqueb`. It adds no
  generic maximality infrastructure and no clique predicate.
  - `maximal_clique S := maxset cliqueb S`: `S` is a clique and no proper superset is a clique (`maximal_cliqueP`,
    through GraphTheory's `maxset_properP` and `cliqueP`).
  - `nontrivial_maximal_clique S := (1 < #|S|) && maximal_clique S` adds the size guard.
  - X181's Boolean helper equals `nontrivial_maximal_clique` by a Boolean equality, so its size guard stays in the
    helper.
  - XE1's Prop helper is reflected onto `maximal_clique` (an iff), with no size or nonempty guard.

  No conversion or propositional extensionality is claimed. Inclusion-maximal is not maximum cardinality:
  upstream `maxcliques` and U13's `is_max_clique` stay distinct, as does the hypergraph `xe2_maximal_hyperclique`.
- **API.** The reflection, the Boolean presentations, the clique projection, no proper clique extension, and
  extension of any clique to a maximal one (`maxset_exists`).
- **Client.** Each case the public client covers:
  - `K_0`: the empty set is maximal but not nontrivial;
  - `K_1`: the singleton is maximal but not nontrivial;
  - `K_n`: the whole set is maximal, and nontrivial from two vertices on;
  - nonempty edgeless graphs: exactly the singletons are maximal;
  - the disjoint `K_2 + K_3`: the `K_2` is a nontrivial inclusion-maximal clique that is not maximum, next to the
    maximum `K_3`.
- **Rows.** Frozen verbatim at `1f4e9c1`: both helpers, the five chains and the two current rows.
  - X181 chains: the ffun colouring into `'I_k`; the window, with ordinal `k`, floor logarithms, natural subtraction
    and both inequalities; and the exact G(n,1/2) weight under the positive-mass `fg_whp`.
  - X181 row: partial; the documented upper-window defect is kept.
  - XE1 chains: the transversal, keeping its `2 <= #|K|` guard outside the helper; and the attained minimal
    transversal size.
  - XE1 #151 row: the whole greatest-guarantee hypothesis and the truncated subtraction.
- **Complete rows.** X181Original (texts at C8's baseline `47eed16`) composes the frozen helper with C8's frozen
  monochromatic body through all three chains and reuses C8's certificate. XE1's row has no older history. That
  makes three whole-row iffs.
- **History.** C8's X181 colourability copy still names the live helper; it stays byte-for-byte and is documented
  in the spec. A18's per-row copy keeps C8's live monochromatic helper and is documented reciprocally in C8's spec.
  A16's and A17's specs and registries drop exactly their two maximal-clique exclusions; U13 stays. The five C8 X181
  certificates and all 35 old proof headers keep their types. Doc blocks are unchanged.
- **Reproduction.** Build the packages. Run `python3 meta/migration_report.py maximal_cliques --check --kernel` and
  the milestones Chromatic X181 and Packing XE1. Kernel probes are in `coordination/evidence/A18-maximal-cliques/`.

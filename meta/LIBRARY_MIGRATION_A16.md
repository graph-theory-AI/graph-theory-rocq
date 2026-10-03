# Library Migration A16: Whole-Graph Clique Number

Batch A family A16, on the fixed A15 pin `7612210` (no private union). Registry
`meta/library_primitives/clique-number.json`; spec, hashes and per-row certificates:
`meta/migration_reports/clique_number.{spec.json,md}`; API contracts are in the Rocq doc comments.

- **Contract.** The canonical is upstream `GraphTheory.core.coloring.omega_mem` (notation `ω`), taken at the
  full vertex set, `ω([set: G])`. Chromatic X112's and Minor X121's helpers already are `ω([set: G])` and stay as
  conversions. Chromatic X124's `\max_(S : {set G} | cliqueb S) #|S|` now unfolds to `ω([set: G])`, equal to the
  old body by the new base adapter `omega_setT_maxE`. That adapter is unconditional: the `cliques` subset filter
  always holds on the full vertex set, and `K_0` gives 0. The results are exact natural numbers; no clique-number
  primitive is added.
- **Client.** The public client covers the bigmax presentation, the order bound, `K_0 = 0`, `K_1 = 1`,
  `K_n = n` and a nonempty edgeless graph `= 1`.
- **Rows.** Frozen verbatim at `7612210`: the three helpers, X124's chain `x124_poly_chi_bounded` and the
  current rows:
  - X124 `dreier_torunczyk_merge_width_poly_chi_bounded_statement`: blocked. The merge-width antecedent defect,
    the coefficient-list witness and the class-uniform polynomial are kept. It has no older history, so it is
    also the complete row.
  - X121 `dallard_milanic_storgel_tw_omega_tree_alpha_statement`: full biconditional, class-uniform `f` and
    `k`, unguarded class. The missing hereditary premise is recorded, not repaired.
- **Complete rows.** Four whole-row iffs in total.
  - X112's helper reaches no current row, because C9 moved its chi-bound to the public predicate. Its whole
    corpus row is therefore an original-statement: X112Original copies C9's pre-C9 chi-bound helper, with the
    frozen clique number, and the closure row from C9's baseline `0659592`.
  - X121Original composes the frozen helper with C13's frozen treewidth, decomposition and tree-alpha bodies
    (text at `58d6d60`).

  The complete bridges reuse C9's and C13's certificates. X124's chain bridge keeps the same coefficient list.
- **History.** C9's X112 chi-bound and C13's Minor X121 row still name the live clique numbers. They stay
  byte-for-byte and are documented in the spec. A16's per-row X121 copy keeps C13's live helpers and is documented
  reciprocally in C13's spec. Doc blocks are unchanged.
- **Distinct.** Clique counts, inclusion-maximal cliques and the maximum-clique set predicate are different
  contracts and stay separate.
- **Reproduction.** Build the packages. Run `python3 meta/migration_report.py clique_number --check --kernel`
  and the milestones Chromatic X112 and X124 and Minor X121. Kernel probes are in
  `coordination/evidence/A16-clique-number/`.

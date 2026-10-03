# Library Migration A15: Simple-Graph Triangle-Freeness

Batch A family A15, on the fixed A14 pin `f52251a`. Registry `meta/library_primitives/triangle-free.json`; spec,
hashes and per-row certificates: `meta/migration_reports/triangle_free.{spec.json,md}`; API contracts are in the
Rocq doc comments.

- **Contract.** The existing canonical `GTBase.base.triangle_free G := forall x y z : G, x -- y -> y -- z -> z -- x
  -> False` is unchanged, and no predicate is added. Chromatic X132, X187 and X192 each wrote triangle-freeness as
  `girth_geq G 4`; their helpers now unfold to `triangle_free G`. The bridge `girth_geq4_equiv_triangle_free` is an
  unconditional iff on every simple graph, not a conversion. The `2 < size c` guard of `girth_geq` is what makes it
  hold, and it is untouched.
- **Bridge.** The existing proof of `Topological.foundations.girth.girth_geq4_equiv_triangle_free`, with its
  support lemmas `triangle_ucycle` and `ucycle3_triangle`, moved unchanged into `GTBase.base` after
  `triangle_free`. The three Topological lemmas keep their qualified names and statements and now delegate to
  base; no file imports that module. The independent bridges `Chromatic.grounding_U8.triangle_free_girth` and
  `Extremal.implications_X13.girth_geq4_triangle_free` (edges e063/e075) keep their proofs and types.
- **Client.** The public client covers the bridge, `K_0`, `K_1`, `K_2` and the 4-cycle (triangle-free in both
  readings), `K_3` (in neither), and the size-2 `ucycle` of `K_2` that the guard excludes.
- **Rows.** Frozen verbatim at `f52251a`: the three helpers, X192's chain
  `x192_polytime_additive_chromatic_approx`, and the whole rows:
  - X132 `dvorak_norin_postle_planar_list_flexibility_statement`: one `p/q` with `0 < p <= q` for the 5/4/3 list
    cases;
  - X187 `planar_triangle_free_request_graph_fraction_statement`: disproved; request guards and the exact
    fraction kept; empty request sets and zero totals remain possible;
  - X192 `triangle_free_minor_closed_chromatic_additive_approx_statement`: `alpha` before the class, excluded-minor
    witness only.

  X192's chain bridge reuses the same program and polynomial-cost proof in both directions, converting only the
  triangle-free domain conjunct; both output bounds are untouched and no extensionality is used.
- **Complete rows.**
  - X187 (text at C5's baseline `a6db537`) composes this family's frozen helper with C5's frozen proper
    3-colouring.
  - X192 (text at C11's baseline `6e1a1c4`) composes C11's frozen excluded-minor class with this family's frozen
    chain.

  Each bridge converts the A15 pieces and reuses the earlier certificate.
- **History.** C5's X187 row and C11's X192 row still name the live helpers. They stay byte-for-byte and are
  documented in the spec. A15's per-row copies keep C5's live colouring and C11's live class, and are documented
  reciprocally in those specs. Statement doc blocks are unchanged.
- **Distinct.** These stay separate: the arbitrary-relation `XE2.xe2_triangle_free_rel`, and the Digraph
  underlying, oriented and directed triangle predicates. Statements that already say `girth_geq G 4`, or quantify
  triples inline, are statement text.
- **Reproduction.** Build the packages. Run `python3 meta/migration_report.py triangle_free --check --kernel` and
  the milestones Chromatic X132, X187 and X192. Kernel probes are in `coordination/evidence/A15-triangle-free/`.

# E1-A1 edge-programme audit (second reader, 2026-09-24)

Faithfulness audit of the statement-body repairs, conditional-edge externals,
load-bearing foundation lemmas and suspiciously short edge proofs of the
"prove all implications" programme. Reader: Claude Opus 5 second reader. This was a read-only pass: nothing
was compiled, and no `.v` file was edited. The protocol for each item was:
back-translate the Rocq body without reading the doc block first, then compare it
with the doc block, the corpus row (`meta/statement_doc_rows.py`) and the paper.
The papers were read from arXiv:1610.00876 (full text), arXiv:1310.8441
(full text) and the corpus context of arXiv:2303.11766.

Verdict scale: PASS / PASS-WITH-NOTE / FAIL.

## A. Statement-body changes

### A1. `every_forest_is_multibounding_statement` (chromatic-theory X218.v): PASS-WITH-NOTE
Back-translation: for every forest H there are two functions c and e from nat to nat
such that for every d >= 1, t >= 1 and every graph G with no induced H and no (not
necessarily induced) K_d(t) subgraph, chi(G) <= c(d) * t^(e(d)).
Source (Nguyen-Scott-Seymour VIII, Conjecture 1.6): H is multibounding if for every
d >= 1 there is a polynomial f with chi(G) <= f(t) for all t >= 1 and all H-free G
with no K_d(t) subgraph.
- For a fixed d, c(d) * t^(e(d)) is a polynomial in t whose coefficients do not
  depend on t or G. Conversely, on t >= 1 any polynomial is dominated by
  (sum of |coefficients|) * t^deg. So polynomiality in t for each fixed d is kept.
- The Skolemisation is classically equivalent to the pointwise form (it uses
  countable choice). Constructively it is stronger, and the note says so.
- Grounding lemmas:
  - `x218_multibounding_pointwiseP` spells out the old body and proves
    new => old, so nothing was weakened.
  - `x218_multibounding_K1` is a real non-vacuity witness: 'K_1 is a forest and is
    multibounding with the zero functions.
  - `x218_multipartite_1_edgeless` correctly records that d = 1 is degenerate.
- No vacuity or refutation hazard.
- Note: the corpus `verification_note` of the row still paraphrases the
  pointwise form. This is harmless.

### A2. `mader_delta0_transitive_tournament_statement` (X2.v): PASS-WITH-NOTE
Back-translation: for every k there is an m such that:
- every NON-EMPTY digraph of minimum semidegree >= m contains a subdivision of TT_k
  (injective branch map, nonempty directed paths, interiors avoiding all branch
  vertices and pairwise disjoint);
- m is <= every other such bound.

Paper Conjecture 3 of arXiv:1610.00876: "There exists a least integer
mader_delta0(TT_k) such that every digraph D with delta0(D) >= mader_delta0(TT_k)
contains a subdivision of TT_k."
- The guard `0 < #|D|` is the minimal faithful repair. The pointwise degree
  predicate admits the vertexless host, and that host cannot contain a subdivision
  of the nonempty TT_k.
- `x2_delta0_unguarded_false` spells out the old body inline and refutes it at
  k = 1.
- `x2_delta0_hyps_nonvacuous` uses `dense_dg m`, the loopless complete digraph on
  m+1 vertices, whose semidegree is m.
- Walks rather than paths, and loops in the host, do not matter: a walk contains a
  path whose interior is a subset of the walk's interior, and a loop shifts a
  degree by at most one.
- **NOTE:** the LEAST clause is literal to the paper but constructively
  load-bearing. `mader_delta_zero_bound` is a Prop-valued, upward-closed predicate,
  and taking its least element needs excluded middle. This is exactly why
  gc:e173 (P9 -> this row) is BLOCKED in `implications_X2.v`. The classically
  equivalent body `forall k, exists m, mader_delta_zero_bound (TT k) m` would
  unblock e173.

### A3. `oriented_trees_delta_plus_maderian_statement` (X2.v): PASS
Back-translation: every nonempty oriented tree F (asymmetric, with an underlying
simple graph that is a connected forest) has an m such that every NON-EMPTY digraph
of minimum out-degree >= m contains a subdivision of F. This matches Conjecture 4 of
the paper.
- The guard is the minimal one.
- `x2_delta_plus_unguarded_false` refutes the old body at TT_1.
- `x2_delta_plus_hyps_nonvacuous` and `x2_oriented_tree_TT2` inhabit the
  hypotheses.

Side effect on `delta_plus_maderian_disjoint_union_statement` (Conjecture 7):
PASS-WITH-NOTE. The body is unchanged and inherits the guard. The row goes from
vacuously true (unguarded, every nonempty F failed to be maderian) to the genuine
conjecture. The note in the doc block is accurate.

### A4. `subdivision_of_a_transitive_tournament_in_digraphs_w_statement` (P9.v, OPG row): PASS
Back-translation: there is f : nat -> nat such that for every k, every NON-EMPTY
digraph with all out-degrees >= f(k) contains a subdivision of TT_k in the P9
`subdivides` sense.
- In that sense, the interior is `behead (belast ...)`, which is the path minus its
  last vertex. The interior avoids every branch vertex, and interiors are pairwise
  disjoint.
- This is Mader's conjecture. One f works for every k, as in the source.
- The guard is minimal.
- `p9_subdivision_TT_unguarded_false` and `p9_outdeg_host_nonvacuous` are what they
  claim.

### A5. `oriented_tree_mader_chi_linear_bound_statement` (X52.v): PASS
Back-translation: for every oriented tree T with k vertices, every NON-EMPTY
digraph whose underlying graph has chi >= 2k-2 (truncated subtraction) contains a
subdivision of T. This matches paper Conjecture 11 (mader_chi(T) <= 2k-2, as a
consequence of Burr's Conjecture 10). There is no lower bound on k in the paper.
- At k = 1 the old body failed on the empty host, and the guard repairs it.
- `x52_k1_holds` proves the k = 1 instance, so no `2 <= k` guard is needed.
- `x52_hyps_nonvacuous` inhabits every hypothesis with TT_2 at k = 2 (chi >= 2 via
  omega).

### A6. `behzads_statement` (U5.v, OPG row): PASS
Back-translation: every simple (loopless, injective endpoint map) multigraph with
at least one vertex has Delta+1 <= chi''(G) <= Delta+2, where chi'' is chi of the
total graph.
- The guard `0 < #|G|` removes only the empty multigraph, on which the lower bound
  1 <= 0 fails. That is exactly what `behzads_unguarded_body_refutable` proves
  inline, with `void_graph`.
- `behzads_hypotheses_satisfiable` (`unit_graph`) inhabits the hypotheses.
- The lower bound is the standard theorem. The upper bound is the Total Colouring
  Conjecture.

## B. External theorems (conditional-edge hypotheses)

| external | verdict | decisive reason |
|---|---|---|
| `external_circular_5_flow_statement` (X228) | PASS | chi/2 is a real nowhere-zero flow with modulus in [1,4]. Rounding it to an integer flow (Goddyn-Tarsi-Zhang; already Hoffman/Tutte rounding between floor and ceiling edgewise) keeps the modulus in [1,4]. This is exactly the integrality step and no more. Loops cancel in `iconservative`. |
| `external_five_even_cover_cubic_reduction_statement` (U6) | PASS-WITH-NOTE | A true same-property reduction (cubic => general), so nothing is smuggled. Fleischner splitting preserves bridgelessness, and an even subgraph of the split graph restricts to an even subgraph of the original. Degree-2 vertices are suppressed, and cycle components are covered by (C,C,0,0,0). Loops go into two of the five members, and isolated vertices are harmless. Note: the cited sources state the reduction for the CDC family; Zhang 1997 Ch. 3 is the better pointer for the 5-even-subgraph case. |
| `external_cdc_simple_reduction_statement` (U6) | PASS | Elementary and true. Subdividing every edge twice gives a simple bridgeless graph whose circuits are subdivided circuits of G: a loop becomes a triangle and a digon becomes a 4-cycle, and both map back to `is_circuit` sets (`subdeg` counts a loop twice). |
| `external_steffen_3flow_5graphs_statement` (D1) | PASS-WITH-NOTE | Steffen 2015, end of Sec. 3, verbatim: "Tutte's 3-flow conjecture is equivalent to the statement that F_c(G) <= 3 for every 5-graph G." It is stated there without proof. The direction used is a theorem: 5-edge-connected 5-regular graphs are 5-graphs; F_c <= 3 gives a nowhere-zero 3-flow because F_c is attained (GTZ 1998); and Kochol (JCTB 83, 2001) gives the reduction. A 5-graph cannot have a loop. Note: add Kochol 2001 to the citation. The source row at t = 2 is literally the external's premise, so the edge's whole content is the external. |
| `external_tutte_class1_cubic_statement` (D1) | PASS | A 3-edge-colouring is a nowhere-zero Z2xZ2-flow, hence an integer 4-flow, hence an r-flow for every r > 4. `loopless` + `mreg 3` + `is_class1` means exactly "3-edge-colourable cubic". |
| `external_modular_orientation_to_flow_statement` (D1) | PASS | With the E5 guard `0 < k`, this is Tutte's Z_m => integer m-flow theorem at m = 2k+1, applied to the constant-1 weighting of a modular orientation. The k = 0 refutation is gone. |
| `external_petersen_BF_cover_statement` (U10) | PASS-WITH-NOTE | True. `Pedge` is the ORDERED pair type, so the witness is the 6 perfect matchings, each taken with both orientations. `mut_adj3 Padj` forces three distinct pairwise-meeting supports, which in the triangle-free Petersen graph means a claw. Note: this is a closed finite statement, so it is decidable and can be proved by computation, making the edge verified. |
| `external_whitney_line_inversion_statement` (U11, not registered) | PASS-WITH-NOTE | See below. |

Whitney/Greenwell. The bundled claim is: for simple G, H with |E(G)| >= 4, the
same edge deck and L(G) ≅ L(H), we get G ≅ H. It IS a theorem, but neither paper
states it as a standalone result. It follows in a few lines:
1. The components of L(G) are the line graphs of the non-trivial components of G.
2. Whitney 1932, applied component by component, therefore makes the non-trivial
   parts of G and H agree, except for exchanges of K_3 components for K_{1,3}
   components.
3. By Kelly's lemma for edge decks (sum over e of s(F, G-e) = (m - |E(F)|) s(F, G)
   for |E(F)| < m), the number of triangles is determined by the edge deck as soon
   as m >= 4.
4. K_3 has one triangle and K_{1,3} none, so the number of exchanges is zero.
5. The edge deck gives #|G| = #|H|, so the isolated vertices match too.

This is the argument behind Hemminger 1969 and Greenwell 1971. The four-edge guard
and the edge-deck hypothesis are both needed, and the counterexample in the doc
block (K_3+K_1+K_2 against K_{1,3}+K_2) is correct. I also checked
2K_3+K_{1,3}+K_1 against K_3+2K_{1,3}: 9 edges, line graphs both 3K_3, and the decks
differ, as the claim requires. It is not stronger than the step Greenwell uses, and
it is not smuggling: the premise does not mention reconstruction. It can be
registered as `kind=theorem`. Its claim should spell out the Whitney + Kelly
derivation and add Hemminger (1969) to the citation. Steps 1 and 3-5 are
formalisable in `kelly.v`, which would shrink the external to Whitney's connected
theorem.

## C. Load-bearing foundation definitions

- **`cycle_space.v`.**
  - `has_circuit`: a nonempty edge set in which no vertex has C-degree 1 contains
    an `is_circuit` subset. A circuit is nonempty, 2-regular on its support
    (`subgraph_kregular`: degree 0 or 2) and connected. This is correct, and a loop
    counts as a circuit.
  - `even_circuit_decomposition`: every even subgraph is partitioned by a list of
    circuits (the count of e equals [e in C]).
  - Both say what `cubic_has_circuit` and the U6 edges use them for.
- **`comp_reduce.v`, `five_even_cover_connected_reduce`.** Hypothesis: every
  nonempty connected bridgeless H has 5 even subgraphs double-covering it.
  Conclusion: the same for every nonempty bridgeless G, stated over
  `edge G` itself.
  - `Hc r0` keeps the SAME edge type and collapses one root per component onto
    r0. So the cover it produces is literally a cover of the ORIGINAL edge set.
  - Evenness transports back: at non-roots the degrees are equal, and at a root
    the component degree sum is even.
  - Bridgelessness goes the right way (`Hc_bridgeless : bridgeless G -> bridgeless
    (Hc r0)`): a G-walk avoiding e pushes forward to an Hc-walk avoiding e, so
    collapsing only adds walks.
  - No edge joins two roots, since roots lie in different components.
  - Verdict: correct.
- **`matchings_cuts.v`.**
  - `pm_cut_parity`: if every vertex has M-degree 1 (so M has no loop), then
    |M ∩ cut S| ≡ |S| (mod 2). This is the handshake identity, and it is correct.
  - `class1_pm_partition`: a loopless, k-regular multigraph with chi' = k has its
    edge set partitioned into k perfect matchings. This is correct and is exactly
    what `reg_class1_odd_cut` uses.
- **`minor_dec.v`.** `minorP : reflect (minor G H) minorb` is a Qed reflection, so
  `minorb` means `minor` whatever its unfolding. `minorNN` (double-negation
  elimination for minors) is what the edges use. Correct.
- **`ramsey_small.v`.** `ramsey_bound s a`: there is an N such that any vertex set
  with alpha <= a and no clique of size exactly s has at most N vertices. This is
  finite Ramsey; "exactly s" is equivalent to ">= s" because cliques are
  down-closed. Correct.
- **`choice_number.v`.** `choice_number_ex`: 0 < #|G| -> exists ch,
  `is_choice_number G ch` (choosable, and <= every k for which G is choosable).
  Palette canonicalisation makes the predicate decidable, so `ex_minn` gives
  existence without classical axioms. Correct.
- **`edge_colourings.v`.** `kn_chi_line`: for odd N, chi(L(K_{N+1})) <= N, i.e.
  chi'(K_n) <= n-1 for even n. `kn_edge` has one representative per unordered pair
  (p.1 < p.2, `kn_loopless`), so this is the classical round-robin 1-factorisation.
  Correct.
- **`critical.v`.** `double_critical_del1`: if deleting the two endpoints of any
  edge drops chi by exactly 2, G is connected and #|G| >= 2, then deleting any
  single vertex drops chi. This is the correct weak vertex-criticality used by the
  e228 edge.

## D. Short-proof red flags

Every `Theorem/Lemma .*_implies_|_equiv_` with a proof of at most 2 tactic
sentences was listed. The scan covered the 45 `implications_*.v` / `vocabulary_*.v`
files that are modified or untracked in `git status --short`. None is a `move=> _`
discharge. Each one genuinely instantiates its source:
- Direct instantiations or delegations to a named, genuine helper:
  - U5 `total_list_colouring_delta_plus_two_implies_behzads` (`bz_lower` uses the
    guard; `bz_upper X` uses the source);
  - U8/X218 `forest_free_polynomial_chi_bound_implies_*` and
    `polynomial_gyarfas_sumner_tree_implies_*` (evaluate the source polynomial);
  - X219 `*_five_sixths_*` (source set S, then 7/8 => 5/6);
  - U6 `strong_5_cycle...`, `small_cycle_double_cover...` and `orientable_five...`
    (compositions or external application with the source instance);
  - D1 `circular_flow_numbers_of_r_graphs_implies_three_flow` (source at t = 2
    feeds Steffen's premise);
  - X221 (`x221_no_arrow_ocm` is a 30-line lemma);
  - U12 `r_partite_matching_deletion_tradeoff_implies_rysers`
    (`ryser_by_deletion_aux`);
  - U11 `reconstruction_implies_edge_reconstruction` (kelly.v, genuine);
  - X66, X45, and X1's three edges (the colouring_variants helpers are genuine
    specialisations: k = 2, tournament coercion, and dropping the eulerian
    premise).
- Definitional identities, as expected for vocabulary bridges:
  - U3 `bipartite_rel_equiv_bipartite`;
  - U12 `x6_*_equiv_*`;
  - `vocabulary_hypergraph.v` `*_uniform_equiv_hg_uniform`, `x73_*` and `x117_*`;
  - `vocabulary_packing.v` and `vocabulary_misc.v` equivalences.
- X223 `x223_eps_bounded_implies_x58_epsilon_bounded` is a helper Lemma, not an
  edge.
- X110 `chen_chvatal_metric_lines_equiv_chen_chvatal_guarded_metric_lines`
  (status=verified equiv): the two bodies are textually identical (duplicate
  corpus rows), so the edge is a syntactic identity. This is honest, and the edge's
  cite says so.

## Defects for the main session

1. **X2 row arxiv:1610.00876#00 (`least_mader_delta_zero`).** The LEAST clause is
   classically vacuous but constructively needs excluded middle, and it is the
   sole blocker of gc:e173. Recommendation: re-encode the body as
   `forall k, exists m, mader_delta_zero_bound (TT k) m`, with a grounding lemma
   showing classical equivalence, as was done for X218. This is a decision, not a
   faithfulness fault.
2. **`external_whitney_line_inversion_statement` is not registered.** Register it
   in `meta/external_theorems.json` with `kind=theorem`. Its claim should record the
   Whitney (component by component) + edge-Kelly (triangle count, m >= 4)
   derivation and add Hemminger 1969 to the citation. Optionally, formalise the
   Kelly/triangle and component bookkeeping in `kelly.v`, which would reduce the
   external to Whitney's connected theorem.
3. **`external_steffen_3flow_5graphs_statement` citation.** Steffen states the
   equivalence without proof. Add Kochol, "An equivalent version of the 3-flow
   conjecture", JCTB 83 (2001) 258-261, and Goddyn-Tarsi-Zhang for the attainment
   of F_c.
4. **`external_petersen_BF_cover_statement` is decidable.** Proving it by
   computation (6 explicit edge sets over the 30 ordered Pedges) would turn
   petersen_coloring -> berge_fulkerson from conditional into verified.
5. **`external_five_even_cover_cubic_reduction_statement` citation.** Point to
   Zhang 1997 Ch. 3 for the 5-even-subgraph case. The Jaeger survey states the
   cubic reduction for the CDC family.
6. **Minor: the X218 corpus `verification_note` is stale.** It still paraphrases
   the pointwise form of multibounding.

No FAIL was found.

## E. Addendum (coordinator items, 2026-09-24)

### E1. `fractional_hadwiger_statement` (extremal-graph-theory D2chr.v, OPG row): PASS-WITH-NOTE
Back-translation: for every nonempty finite graph G, let xf be the attained minimum
of a/b over (a:b)-colourings with b > 0, h the largest h with a K_h minor, and hf the
attained maximum of the sum of w_i. Here w_i are non-negative rationals on an indexed
family of NON-EMPTY connected vertex sets B_i, any two distinct indices are joined by
an edge, and every vertex has total weight at most 1. Then xf <= h, chi <= hf and
xf <= hf.

- **Paper definition.** Harvey-Wood, "Parameters tied to treewidth",
  arXiv:1312.3401, Section 3 and the had_f paragraph, after Fox and Pedersen.
  - A bramble is a SET of connected subgraphs that pairwise TOUCH: they share a
    vertex, or an edge has one end in each.
  - had_f is the maximum, over brambles beta and weightings w >= 0 (real) with
    total weight <= 1 at every vertex, of the sum of the w(X).
  - The OPG page gives no definition itself and cites [HW], Fox and Pedersen.
- **The E10 guard.** The guard `B i != set0` is the faithful repair: connected
  subgraphs are non-empty in the source, and the old body was unsatisfiable, so the
  row was vacuous.
- **Adjacent versus touching** (the argument in the Notes is correct; the gap is
  even smaller than the Notes say).
  - Two non-empty connected vertex sets that share a vertex v are joined by an edge
    unless both equal {v}. If one of them has at least two vertices, v has a
    neighbour u inside it, and (u, v) is an edge from one set to the other.
  - A bramble is a SET, and a subgraph on one vertex has no edges, so two distinct
    bramble elements never both have vertex set {v}. Distinct subgraphs with the
    same vertex set of size at least 2 are "adjacent" in the Rocq sense.
  - Hence every bramble with a weighting is directly a feasible Rocq family.
  - Conversely, a Rocq family collapses to its set of distinct vertex sets by
    merging duplicates (weights add, and the vertex constraints are unchanged). This
    is the singleton-merge of the Notes, and `fractional.v` does exactly this
    (`sum_fibres`).
  - Conditions on zero-weight members are harmless: drop them.
  - Vertex sets instead of subgraphs are harmless: the induced subgraph on V(X) is
    connected iff X can be chosen connected, and touching and coverage depend only
    on V(X).
  - Rational instead of real weights: the LP has rational data, so its real optimum
    is attained at a rational point.
- **Grounding lemmas.**
  - `old_is_fractional_hadwiger_unsat` spells out the old body inline and refutes it
    with one empty set of weight |hf| + 1.
  - `frac_clique_minor_le_card` gives had_f <= |V|.
  - `is_fractional_hadwiger_K1` (value 1) and `_K2` (value 2) are genuine attainment
    witnesses.
  - `fractional_hadwiger_instance_K2` pins xf = h = hf = chi = 2 through the
    uniqueness lemmas and checks the conclusion there.
  - NOTE: `fractional_hadwiger_conclusion_has_content` is pure arithmetic (2 <= 1
    fails). It shows only that the conclusion is not a tautology in its numerals, not
    that some graph could violate it. It is weak teeth, but harmless.
- **Attainment.**
  - `atlas fractional.frac_hadwiger_exists` and `frac_chromatic_exists` are stated
    directly on D2chr's `is_fractional_hadwiger` / `is_fractional_chromatic`
    (imported, not local copies). Both predicates are "attained, and bounds every
    feasible value", so existence means the TRUE optimum exists and is the parameter.
  - They are proved from `lp_rational.lp_max_fin`: a feasible, bounded rational LP
    over finite types attains its maximum (Fourier-Motzkin).
  - For had_f, the best bramble is taken by `list_argmax` over all sets of vertex
    sets. For chi_f, the covering-LP optimum is turned into an (a:b)-colouring and
    back.
  - No classical axioms appear in either file (grep).
- **Guard `0 < #|G|`.** Harmless, since the empty graph satisfies all three
  inequalities with every value equal to 0.

### E2. `external_layered_treewidth_planar_statement` (atlas implications_A1.v): PASS-WITH-NOTE
Back-translation: every graph with no K_5 minor and no K_{3,3} minor has a layering
L : G -> nat (|L u - L v| <= 1 on every edge) and a coq-graph-theory `sdecomp` over a
forest in which every bag meets every layer in at most 3 vertices.

- **Vocabulary.** `layered_tw_le` is minor-theory `width_params.layered_tw_le`. It is
  the same predicate used by the source row
  `X228.bounded_layered_treewidth_bounded_queue_number_statement` (minor-theory
  X228.v), so the external composes with the source without translation.
- **Source.** Dujmovic-Morin-Wood (JCTB 127 (2017)) prove that planar graphs have
  layered treewidth at most 3.
  - Layered width is max |bag ∩ layer| in VERTICES, with no -1, so the constant 3
    matches the paper.
  - A forest decomposition is equivalent to a tree decomposition.
  - The paper's BFS layering is a layering in this sense, and nothing more is
    required. So the Prop is not stronger than the theorem.
- **Not refutable.** Trivial cases use a one-bag decomposition.
- **NOTE.** The hypothesis is `wagner_planar`, so the Prop is DMW composed with
  Wagner's theorem (1937). Wagner should be added to the citation.
- **Registry.** I added `reviewed_by`/`review` to its entry.
- **Out of scope.** `external_cdc_cubic_2connected_reduction_statement` appeared in
  the registry during this pass and was NOT reviewed here.

### Additional defects
7. D2chr: `fractional_hadwiger_conclusion_has_content` is arithmetic-only teeth.
   Optional: replace it with an instance where a wrong parameter value would
   falsify the row.
8. Add Wagner 1937 to the citation of `external_layered_treewidth_planar_statement`.
9. `external_cdc_cubic_2connected_reduction_statement` is registered but not yet
   second-read.

### E3. `external_cdc_cubic_2connected_reduction_statement` (cycle-theory implications_U6.v, wave E6): PASS-WITH-NOTE
Back-translation: if every non-empty, loopless, 3-regular multigraph with at least 3
vertices that stays connected after deleting any one vertex has a CDC, then every
bridgeless multigraph with at least one vertex and one edge has a CDC. The
conclusion is literally `cycle_double_cover_statement`.

- **It is a theorem, and weaker than the cited one.** Jaeger 1985 §2 and Zhang 1997
  Ch. 3 show that a minimal CDC counterexample is cubic and 3-connected. So nothing
  is smuggled.
- **Corners** (each covered by the minimal-counterexample argument):
  - A loop is a circuit and is covered twice by itself.
  - A bridgeless graph splits into 2-connected blocks, and every circuit lies inside
    one block.
  - A cycle component is covered by the cycle itself, twice.
  - Degree-2 vertices are suppressed.
  - Degree >= 4 vertices are split using Fleischner's lemma. A circuit through the
    new edge that revisits v becomes an even subgraph, which is decomposed into
    circuits again (`cdc` places no bound on the number of circuits).
  - The theta graph, the only loopless cubic 2-connected multigraph on fewer than 3
    vertices, is excluded by the `3 <= #|G|` guard, but its three digons form a CDC
    directly.
- **Not trivially true, not refutable.** The conclusion is the CDC conjecture itself,
  and the premise class is inhabited (K_4).
- **Note.** `0 < #|G|` in the premise is redundant.

10. (E3) No defect. `reviewed_by`/`review` were added to its registry entry.

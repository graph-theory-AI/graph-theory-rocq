# X211-X229 Faithfulness Audit

Second-reader (blind readback) audits of the statement waves X211-X229.
Each section is appended independently by the reader of that wave; sections are
ordered by append time, not by wave number.


## X216:digraph-theory — second-reader readback (2026-09-23)

Reader: Claude Opus 5 second reader, session 01P75Y6ikkgDyzUzzoef316Z
(distinct from `implemented_by`). Protocol: `magical-snacking-token.md`
"Faithfulness protocol", steps 2 (two-reader source verification), 4 (active
probes) and 7 (adversarial audit).

### Scope

The single row of wave X216 in `digraph-theory`
(`digraph-theory/theories/conjectures/X216.v`, grounding `grounding_X216.v`).
The other X216 sub-waves (`graph-theory-misc`, `infinite-graph-theory`) are
another reader's.

### Outcome

1/1 PASS (PASS-WITH-NOTE). No row blocked. `check_milestone X216 digraph-theory`
ACCEPTED; `vacuity_probe --names weighted_caccetta_haggkvist_statement` 1 probed,
0 flagged.

| row | statement | verdict |
|---|---|---|
| bm_070 | `weighted_caccetta_haggkvist_statement` | PASS-WITH-NOTE |

### Readback

Back-translated from the body alone: *for every finite digraph D with at least
one vertex and no loops, and every rational weight function w that is positive on
the arcs, if D is strongly connected and every vertex has total in-weight ≥ 1 and
total out-weight ≥ 1, then some directed cycle has total arc weight ≥ 1.* This
matches `statement_text` of `bm:bm-070` clause for clause, including the
direction of the conclusion (**at least** 1 — the "at most 1" reading sometimes
attributed to Bollobás–Scott is not the corpus/book text). `x216_win`/`x216_wout`
range only over arcs; `x216_cycle_weight c = \sum_(z <- c) w z (next c z)` counts
each arc of a `dicycle` (`~~ nilp c && cycle arc c && uniq c`) exactly once, so
the implementer's question (4) is answered yes.

### Adversarial checks

- **Rational vs real weights** (implementer's question 1): sound, and in the
  direction that matters. The hypotheses are closed conditions and the negation
  of the conclusion is open, so any real counterexample perturbs *upwards* to a
  rational one (pick rational w' ≥ w with w' − w small: in/out weights stay ≥ 1
  and the finitely many cycle weights stay < 1). Same truth value.
- **Looplessness** (question 2): not literally Bondy–Murty's "digraph", but
  forced — `grounding_X216.x216_loopless_guard_has_teeth` machine-checks the
  loopful two-vertex refutation (loops 3/4, digon arcs 1/4: w⁻ = w⁺ = 1, strongly
  connected, cycle weights 3/4, 3/4, 1/2). An unguarded encoding would be
  refutable, so it cannot be the intended reading.
- **`0 < #|D|`** (question 3): sound; `x216_order_guard_has_teeth` shows the
  empty digraph satisfies everything vacuously and owns no `dicycle`.
- **Vacuity**: the hypothesis block is satisfiable (`x216_dg2_witness`, the digon
  with unit weights) and the conclusion holds there; auto-prove and auto-refute
  ladders both fail.
- **Loops as 1-cycles**: under the guard, `dicycle [:: v]` requires `v --> v`, so
  no degenerate one-vertex cycle can satisfy the conclusion cheaply.

### Notes for the improvement ledger

- `diGraphType` has no parallel arcs, so the row quantifies over *simple*
  loopless digraphs. Merging parallel arcs only raises cycle weights, so a
  hypothetical multi-arc counterexample need not survive the merge: the encoding
  is marginally **weaker** than a multigraph reading of "digraph". This is the
  corpus-wide simple-graph convention; recorded, not blocking.
- Doc-block `Notes:` extended in place with the readback conclusions (comment
  only; the `Definition` body is untouched).

## X221 — second-reader readback (2026-09-23)

Reader: Claude Opus 5 second reader, session 01P75Y6ikkgDyzUzzoef316Z.

### Scope

All 7 rows of wave X221 (`digraph-theory/theories/conjectures/X221.v`, with
`grounding_X221.v` and `implications_X221.v`). Sources consulted directly:
arXiv:2306.04710 (v3 full text), arXiv:2310.04265v2, arXiv:2403.02298,
arXiv:2410.23566, arXiv:2510.11311v1.

### Outcome

**6/7 PASS, 1 FAIL.** `axv_2510_11311_04` moved to `state: "blocked"` with a
`blocked_reason` in `meta/v2_statement_waves.json`, and its doc-block `Notes:`
now records the defect. `check_milestone X221 digraph-theory` still ACCEPTED
(11/11, 7/7 axiom-free); `vacuity_probe --wave X221`: 7 probed, 0 flagged.

| row | statement | verdict |
|---|---|---|
| axv_2306_04710_02 | `delta122_hero_k1_plus_dipath2_free_statement` | PASS |
| axv_2202_13306_00 | `delta122_hero_oriented_complete_multipartite_statement` | PASS |
| axv_2403_02298_00 | `oriented_triangle_free_acyclic_number_theta_statement` | PASS-WITH-NOTE |
| axv_2403_02298_01 | `oriented_triangle_free_dichromatic_theta_statement` | PASS-WITH-NOTE |
| axv_2310_04265_03 | `ordered_twinwidth_clique_and_tww_bound_statement` | PASS-WITH-NOTE |
| axv_2410_23566_05 | `kextension_linear_unavoidability_statement` | PASS-WITH-NOTE |
| axv_2510_11311_04 | `orientation_C4_eulerian_avoidable_statement` | **FAIL → blocked** |

### Row-by-row

- **axv_2306_04710_02 (PASS).** The `oriented_dg` guard the implementer flagged
  as a modelling choice is in fact the paper's stated convention: arXiv:2306.04710
  §1 says verbatim "Throughout this paper, (di)graphs are finite and simple. In
  particular, for digraphs, between every two vertices u and v, at most one of uv
  and vu is present" (corroborated by its "tournaments are exactly the digraphs
  which forbid 2K₁", true only for oriented graphs). χ⃗-finite = "there is a
  constant c such that all F-free digraphs have dichromatic number at most c" =
  `dichromatic_bounded`. `no_induced_arrowK2_K1` is an induced K₁ + P⃗₂;
  `c3sub (TT 1) (TT 2) (TT 2)` is Δ(1,2,2) with the paper's cyclic block
  orientation.
- **axv_2202_13306_00 (PASS).** On an oriented digraph non-adjacency is
  reflexive and symmetric, so transitivity makes it an equivalence whose classes
  are the parts: `x221_oriented_complete_multipartite` is exactly "orientation of
  a complete multipartite graph". Row is `disproved` upstream and no refutation
  is committed, as required.
- **axv_2403_02298_00 / _01 (PASS-WITH-NOTE).** Checked against the paper:
  ā(n) is the **minimum** acyclic number (max order of an acyclic *induced*
  subdigraph) and t̄(n) the **maximum** dichromatic number over oriented
  triangle-free graphs of order n; Conjecture 3 is Θ(√(n log n)) and Conjecture 4
  Θ(√(n/log n)). `x221_alphavec`/`x221_dichro` match those invariants (the
  `minn`-bigop's neutral `#|D|` never inflates the value on a loopless digraph),
  and the triangle guard needs no distinctness clause because `x221_uadj` is
  irreflexive under `oriented_dg`. Discretisation is sound: ⌊log₂ n⌋ ≥ (log₂ n)/2
  for n ≥ 2, nat division and `sqrt_ceil` each cost only a bounded factor, the log
  base is irrelevant inside Θ, and `big_Theta_nat` is the genuine two-sided
  constant-factor-with-threshold form.
- **axv_2310_04265_03 (PASS-WITH-NOTE).** Matches arXiv:2310.04265**v2**
  Conjecture 3.14 verbatim: "There exists a function f, such that for every
  tournament T, there exists an ordering ≺* of V(T) such that ω(T^{≺*}) ≤ f(ω⃗(T))
  and tww((T,≺*)) ≤ f(tww(T))" — one f, one ordering for **both** clauses, and the
  twin-width clause now on f(tww(T)) (the defect of the older
  `conj_3_13_statement`). `bclique p = ω(backedge p)` and `omegabar` is the min of
  that over orderings, i.e. the paper's ω⃗.
- **axv_2410_23566_05 (PASS-WITH-NOTE).** `x221_kextension` is the paper's
  definition verbatim ("An acyclic digraph D is a k-extension of A if there exists
  a set S of k vertices such that D−S = A"), so the acyclicity guard does belong
  to the extension; Conjecture 11 is the quoted sentence.
- **axv_2510_11311_04 (FAIL).** See below.

### Blocked rows

**axv_2510_11311_04 — `orientation_C4_eulerian_avoidable_statement`: too strong
(failure mode 3).** arXiv:2510.11311 defines, for both *avoidable* and
*Eulerian-avoidable*, "there exists d_F : ℕ → ℕ such that every (Eulerian)
digraph of minimum out-degree at least d_F(k) contains an F-free **subdigraph**
of minimum out-degree at least k" — a subdigraph on an arbitrary vertex subset.
`x221_eulerian_avoidable` instead asks for a **spanning** witness: `outsel f` has
vertex type `D`, so `forall v : outsel f, k <= outdeg v` constrains every vertex
of the host. Spanning ⇒ non-spanning, not conversely (the omitted vertices would
each have to be given k out-arcs, which can create copies of F; the source's
notion is satisfied by a witness inside one component of a disjoint union, the
spanning one is not). The doc block's English said "spanning subdigraph", so the
implementer's back-translation was accurate — the mismatch is body vs source.
Fix (not applied; a second reader does not edit bodies): existentially quantify a
vertex subset, e.g. an `induced_digraph S` carrying an out-neighbourhood
selection with the minimum out-degree taken inside `S`. The row's other choices
are faithful: "∃d, ∀k" is the paper's own binding order, F-freeness is
non-induced as in the avoidability literature, and `x221_c4or` is digon-free with
underlying graph C₄, the 16 boolean vectors enumerating the orientations with
harmless repetitions under a universal quantifier.

### Notes for the improvement ledger

- **Corpus-status inconsistency.** Within oriented digraphs, "no induced
  K₁ + P⃗₂" and "non-adjacency transitive" are *equivalent* (both directions
  checked by hand: transitivity kills the induced arc-plus-isolated-vertex, and
  conversely an adjacent pair with a common non-neighbour is such a pattern once
  the degenerate equalities are discharged). So `axv_2306_04710_02` and
  `axv_2202_13306_00` encode logically equivalent Props, yet the corpus lists one
  `open` and the other `disproved`; the `open` status of 2306.04710#02 predates
  Walczak's remark. Not an encoding defect, but a status the corpus should
  reconcile — and a latent tripwire for `check_milestone`'s "no unconditional
  refutation of a non-disproved row" probe if the refutation of 2202.13306#00 is
  ever committed. `implications_X221` proves one direction; the converse is
  equally provable and would be a good additional edge.
- **Realizer-existence lemmas missing** for three relational encodings:
  `x221_abar` / `x221_tbar` (grounding proves functionality and inhabitation only
  at n = 0) and `x221_tww_eq` (twin-width value pinned only for `#|T| <= 1`, via
  `tww_le_small`). Semantically a total realizer always exists, so the statements
  are equivalent to their sources in any model; but a `forall a, realizes a -> …`
  shape is vacuous exactly when no realizer exists, and today nothing in the repo
  rules that out. Suggested: `tww_le T #|T|` for every tournament, and an
  order-n realizer lemma for ā/t̄ (every order-n digraph is isomorphic to one on
  `'I_n`).
- **`unvd`-based linear unavoidability**: the source defines it as "every D ∈ C is
  contained in all tournaments of order c·|V(D)|", the encoding as
  `unvd D N -> N <= C * #|D|`. These agree because N-unavoidability is upward
  closed in N — true, and explicitly *not* proved in `unvd.v`. A monotonicity
  lemma there would close the gap. The encoding also does not restrict `F` to
  classes of *acyclic* digraphs as the source does; harmless (k-extension classes
  of non-acyclic members are empty), but worth a sentence in `unvd.v`.
- The `0 < #|T|` guard on the twin-width row is the file-wide convention of
  `twinwidth_ordered.v`; the empty tournament is either trivially fine or has no
  contraction sequence at all, so nothing open is lost.

## X214:packing-theory — second-reader readback (2026-09-23)

Reader: Claude Opus 5 second reader, session 01P75Y6ikkgDyzUzzoef316Z.

### Scope

The single `packing-theory` row of wave X214
(`packing-theory/theories/conjectures/X214.v`, grounding `grounding_X214.v`).
The `minor-theory` sub-wave is another reader's.

### Outcome

1/1 PASS. `check_milestone X214 packing-theory` ACCEPTED; vacuity probe clean.

| row | statement | verdict |
|---|---|---|
| bm_025 | `spanning_k_connected_bipartite_subgraph_statement` | PASS |

### Readback and adversarial checks

Back-translation from the body: *for every k ≥ 1 and every finite simple graph G
that is 2k-connected there is a set F of vertex pairs such that G with the edges
of F removed (same vertices) is bipartite and k-connected* — the book's f(k) = 2k
form of Thomassen's conjecture, no proxy. The five points the implementer raised
all check out:

1. `del_edge_set G F` with `F : {set {set G}}` ranging freely **is** "spanning
   subgraph of G": vertex type `G`, edges `x -- y && [set x; y] \notin F`, so
   `F = E(G) \ E(H)` realizes any spanning subgraph; non-pair members of `F` are
   never read.
2. `k_connected` is base's Whitney form (`k < #|G|` and `connected ([set: G] :\: S)`
   for all `#|S| < k`); its cardinality clause is free in the conclusion because
   `2k < #|G|` already gives `k < #|G|`, so no hidden strengthening.
3. The `0 < k` guard removes only a provable instance (`k_connected G 0` is just
   `0 < #|G|`, and deleting every edge satisfies the conclusion), so guarded and
   unguarded readings have the same truth value.
4. The conclusion is a single existential over one subgraph that is
   simultaneously bipartite **and** k-connected, as in the source.
5. `forall G : sgraph` is "every finite simple graph".

The asymptotic partial results (Delcourt–Ferber, Yuster: connectivity
O(k² log n)) are correctly *not* part of the statement. `grounding_X214` anchors
the k = 1 instance with an explicit witness (K₃ minus an edge) and shows the free
bipartite witness (delete every edge) fails k-connectivity, i.e. the conjunction
has teeth.

### Notes for the improvement ledger

None specific to this row. (The Whitney-form `k_connected` is shared vocabulary;
its `k < #|G|` clause is worth keeping in mind whenever a conclusion demands
k-connectivity of a *smaller* graph — not the case here.)

## X226 — second-reader readback (2026-09-23)

Reader: Claude Opus 5 second reader, session 01P75Y6ikkgDyzUzzoef316Z.

### Scope

All 4 rows of wave X226 (`packing-theory/theories/conjectures/X226.v`, with
`grounding_X226.v` and `implications_X226.v`). Sources consulted directly:
arXiv:2302.04986 and arXiv:2401.00299.

### Outcome

4/4 PASS. `check_milestone X226 packing-theory` ACCEPTED (4/4 axiom-free);
`vacuity_probe --wave X226`: 4 probed, 0 flagged.

| row | statement | verdict |
|---|---|---|
| axv_2302_04986_00 | `eta_bounded_forest_free_classes_statement` | PASS |
| axv_2302_04986_01 | `eta_bounded_path_free_classes_statement` | PASS |
| axv_2302_04986_04 | `eta_bounded_two_stars_free_classes_statement` | PASS-WITH-NOTE |
| axv_2401_00299_04 | `subcube_partition_count_ratio_subexponential_statement` | PASS |

### The η primitive (shared by the first three rows)

arXiv:2302.04986 abstract, verbatim: "η(G) denotes smallest cardinality of a
hitting set of all maximum stable sets in G", and "a class C of graphs is
η-bounded if there exists a function h : ℕ → ℕ such that η(G) ≤ h(ω(G)) for every
graph G ∈ C". `x226_hitting_set X` quantifies over `maxstabsets [set: G]`, which
in `coloring.v` is `[set S in stabsets H | α(H) <= #|S|]` — the **maximum** stable
sets, not the maximal ones — and requires `S :&: X != set0`; that is exactly "X
meets every maximum stable set", equivalently α(G − X) < α(G). Stating the bound
as `x226_eta_le G b := exists X, hitting X /\ #|X| <= b` is η(G) ≤ b and not a
weakening, because η is a minimum over a finite family.

The `0 < #|G|` guard is *exactly* right rather than merely convenient: for
`#|G| > 0` the whole vertex set is always a hitting set (maximum stable sets are
non-empty), and for `#|G| = 0` the unique maximum stable set is `set0`, which no
set meets, so η is infinite under **either** definition — the hitting-set one and
the α-drop one. `grounding_X226.x226_no_eta_bound_empty` machine-checks it. The
source quantifies over graphs, implicitly non-empty.

### Row-by-row

- **_00 (PASS).** Conjecture 1.8 verbatim; the outer quantifier is over all
  forests H with f allowed to depend on H, which is the body's shape, and
  "forest" is the library's path-uniqueness `is_forest [set: H]`, not an edge
  count.
- **_01 (PASS).** Conjecture 1.13 verbatim (t ≥ 6, f may depend on t; t ≤ 5 is the
  paper's Theorem 1.12). `x226_path_graph t` is P_t on `'I_t`, and
  `implications_X226` *proves* it is a forest — an independent validation of the
  carrier.
- **_04 (PASS-WITH-NOTE).** The source's open problem is "whether the class of
  (S_a ∪ S_b)-free graphs is η-bounded for all a, b ≥ 1". `x226_star a` is the
  star with a **leaves** (a+1 vertices, centre `ord0`); this is the right reading —
  the excluded degenerate cases (a component reduced to a single vertex) are
  already settled by the paper's Theorem 1.14 (H with a vertex incident to all
  edges), so nothing open is lost. `sjoin` is coq-graph-theory's **disjoint**
  union (`join_rel` is `false` across the two sides), not the complete join —
  checked in `sgraph.v`, since a join would have silently changed the object.
- **_04 of 2401.00299 (PASS).** f(d) counts partitions of V(Q_d) whose classes
  span subhypercubes, f_{≤2}(d) those with all classes of dimension ≤ 2, n := 2^{d−1},
  and Problem 1.10 asks whether f(d)/f_{≤2}(d) is subexponential in n — all
  verbatim. The subcube model (partial coordinate assignment, dimension = number
  of free coordinates) is faithful, and the representing assignment of a non-empty
  subcube is unique, so the dimension bound is unambiguous. Q_d is reused from U9
  (`d.-tuple bool`, matching `tnth`) and only its vertex set is used, as in the
  source. The ε = 1/q reduction is exact: "for all ε > 0 the ratio is eventually
  ≤ 2^{εn}" ⟺ "for all q ≥ 1 eventually (f/f₂)^q ≤ 2^n", and cross-multiplying
  gives the division-free `f d ^ q <= 2 ^ (2 ^ d.-1) * f_2 d ^ q` with the asked-for
  q-then-d₀ order. `0 < q` drops only a trivially true instance, and
  `x226_f_dim_le2_gt0` rules out a division-by-zero artefact.

### Notes for the improvement ledger

- `x226_path_graph` and `x226_star` duplicate carriers that exist elsewhere in
  the corpus (X18's path carrier; several packages build stars ad hoc). Candidates
  for `base/theories/common.v` with the `is_forest` proofs of
  `implications_X226` attached as sanity lemmas (WP4b/WP6).
- η itself (hitting set of all maximum stable sets, and η-boundedness of a class)
  is a clean, reusable notion built entirely on `dom.v`/`coloring.v` vocabulary;
  if a second package ever needs it, it belongs in `common.v` rather than in
  `X226.v`.

## X214:minor-theory — second-reader readback (2026-09-23)

Second reader: Claude Opus 5, session 01P75Y6ikkgDyzUzzoef316Z (distinct from the implementer).

### Scope

3 rows of `minor-theory/theories/conjectures/X214.v`: bm-029 (Kelmans-Seymour), bm-041
(Hadwiger), bm-042 (Hajos for k = 5, 6), plus the shared foundation
`minor-theory/theories/foundations/containment.v` and `implications_X214.v`.

### Outcome

3/3 PASS, 0 blocked.  `vacuity_probe.py` ok on all three (neither the statement nor its
negation closes automatically).  `check_milestone.py X214 minor-theory` ACCEPTED.

### Per-row verdicts

| row | formal name | verdict | remark |
|---|---|---|---|
| bm:bm-029 | `kelmans_seymour_k5_subdivision_statement` | PASS | Whitney 5-connectivity, Wagner planarity, non-induced subdivision model |
| bm:bm-041 | `hadwiger_chromatic_clique_minor_statement` | PASS | exact `chi = k`; `minor G 'K_k` is the right orientation |
| bm:bm-042 | `hajos_k5_k6_subdivision_statement` | PASS | `k = 5 \/ k = 6` hypothesis matches the source question |

### Blocked rows

None.

### Notes for the improvement ledger

- `~ wagner_planar G` is the double negation of "K5 minor or K3,3 minor".  Classically the
  same, and the encoded hypothesis is the more inclusive one, so the row can only be stronger
  than the source, never weaker.  A `wagner_nonplanarP` lemma in `base` (the two forms are
  equivalent because `minor` is decidable on finite graphs) would remove the wrinkle for every
  future row that excludes planar graphs.
- `subdiv_model` (containment.v) is a good general primitive: branch injectivity, per-edge
  interior lists with `sdm_pathC` fixing the two orientations, interiors disjoint from branch
  vertices and from each other.  It should be considered for promotion to `base/theories`
  (digraph-theory already has a directed counterpart `contains_subdivision`).
- bm-029 is a `solved` row with no settled-case artifact; the He-Wang-Yu proof is far out of
  reach, so the strongest available check stays the grounding pair (`'K_6` satisfies both
  hypotheses, `'K_4` is Wagner-planar, `'K_3` is not 5-connected).

## X220 (minor-theory) — second-reader readback (2026-09-23)

Second reader: Claude Opus 5, session 01P75Y6ikkgDyzUzzoef316Z (distinct from the implementer).

### Scope

10 rows of `minor-theory/theories/conjectures/X220.v` plus the new vocabulary in
`minor-theory/theories/foundations/{containment,width_params}.v`
(`tw_le`/`tw_ge`/`tree_alpha_le`/`induced_matching`/`tree_mu_le`, `has_induced_copy`,
`is_subdivision_of`, `sline_graph`, `el_graph`) and the local twin-width, clique-width,
shallow-minor, wall, theta, prism, wheel and biclique-number encodings.

### Outcome

10/10 PASS (4 PASS-WITH-NOTE), 0 blocked.  `vacuity_probe.py` ok on all ten.
`check_milestone.py X220 minor-theory` ACCEPTED (16 forbidden shapes tested).
Source papers consulted for the delicate encodings: arXiv:2203.06775v2 (theta, prism, wheel,
line wheel, even wheel, C*_t, Conjecture 1.6) and arXiv:2511.03864v1 (the `H-free` convention,
Questions 5.2 and 5.3, tree-mu, induced biclique number).

### Per-row verdicts

| row | formal name | verdict | remark |
|---|---|---|---|
| arxiv:2008.05504#01 | `bounded_degree_induced_wall_or_line_wall_statement` | PASS-WITH-NOTE | wall indexing convention |
| arxiv:2109.01310#00 | `four_family_free_logarithmic_treewidth_statement` | PASS | four induced exclusions, log envelope |
| arxiv:2203.06775#00 | `theta_prism_even_wheel_free_bounded_treewidth_statement` | PASS-WITH-NOTE | even-wheel encoding differs from the paper's definition but defines the same class here |
| arxiv:2305.16258#01 | `even_hole_kt_free_logarithmic_treewidth_statement` | PASS | one c per t |
| arxiv:2305.16258#00 | `even_hole_diamond_free_bounded_tree_alpha_statement` | PASS | k quantified before G |
| arxiv:2511.03864#00 | `tree_mu_ktt_free_polynomial_tree_alpha_statement` | PASS | induced K_{t,t}-free confirmed verbatim |
| arxiv:2511.03864#01 | `bounded_tree_mu_polynomial_biclique_tree_alpha_statement` | PASS | `x220_ibn` is the maximum, not a bound |
| arxiv:2006.09877#00 | `small_hereditary_class_bounded_twin_width_statement` | PASS-WITH-NOTE | partition contraction sequences faithful; degenerate grounding witness |
| arxiv:2006.09877#01 | `polynomial_expansion_bounded_twin_width_statement` | PASS-WITH-NOTE | shallow minors faithful; degenerate grounding witness |
| arxiv:2001.01607#02 | `triangle_s123_free_bounded_clique_width_statement` | PASS | k-expression semantics checked in Rocq |

### Findings behind the notes

1. **Even wheels (arxiv:2203.06775#00) -- doc block corrected, body kept.**  The paper defines
   a WHEEL (H,w) as a hole plus a vertex with at least three PAIRWISE NONADJACENT neighbours on
   it, a LINE WHEEL as a hole plus a vertex whose neighbourhood on it is the union of two
   disjoint edges, and an EVEN WHEEL as a line wheel, or a wheel with an even number of spokes.
   `x220_even_wheel_free` forbids instead every hole plus outside vertex with an even number
   (at least three) of spokes.  These are different predicates on general graphs, but they
   coincide on the (C_4, diamond)-free graphs the statement quantifies over: given an even
   number k >= 4 of spokes with no three pairwise nonadjacent among them, the spokes form at
   most two maximal arcs of the hole, each of length at most two (two disjoint edges: a line
   wheel) or a single arc of exactly four consecutive hole vertices, whose first three plus the
   centre induce a diamond; three or more arcs, and arcs of five or more vertices, always
   contain three pairwise nonadjacent spokes.  Conversely every line wheel has four spokes and
   every wheel at least three, so both are caught.  The encoded class is therefore exactly
   C*_t.  The doc block's `Notes:` now records the source definitions and this argument.
2. **Theta and prism.**  The paper's verbatim definitions (three internally disjoint paths of
   length at least two between two nonadjacent vertices, pairwise anticomplete interiors; two
   disjoint triangles joined by three paths whose only cross edges are the two triangles)
   match `is_subdivision_of H (KB 2 3)` and the prism model with the six triangle edges
   unsubdivided.  Exactness of `is_subdivision_of` was re-derived: it forbids a chord of a
   subdivision path and an edge between two branch vertices that are nonadjacent in the model
   graph.  Both notions were checked INHABITED in Rocq (K_2,3 is a theta, the 3-prism is a
   prism) -- these two one-line lemmas are not in `grounding_X220.v` and should be.
3. **Twin-width by partitions.**  For graphs (as opposed to trigraphs) the red edges of a
   contraction sequence starting from the singletons are exactly the pairs of parts that are
   neither complete nor anticomplete, and the contraction rule preserves that invariant, so
   `x220_red_pair`/`x220_red_deg` need no separate trigraph type.  Every element of the
   sequence is a genuine partition into nonempty parts, and "at most one part" is the right
   terminal condition (it also covers the empty graph).  `x220_small_class` counts LABELLED
   graphs, and the "every set F of realised adjacency functions" phrasing is the correct
   decidability-free way to bound the number of them.
4. **Clique-width.**  `Print x220_cw_realises` in Rocq confirms the intended four-clause
   conjunction (`injective f`, `f v` in range, every position hit, `u -- v = x220_cw_edge`) --
   the `[/\ _, _, _ & _]` block containing an `exists` does NOT mis-parse into an `exists2`.
   `CwJoin i j` requires `i <> j` in `x220_cw_wf` and adds ALL edges between the two labels;
   the denoted relation is symmetric and irreflexive, so realising it by an isomorphism is
   meaningful.
5. **Vacuous instances.**  `x220_clique_free G 0` is unsatisfiable (the empty set is a clique of
   size 0), `~ has_induced_copy G 'K_0` is false for every G, and `is_subdivision_of W
   (x220_wall 0)` forces W empty; so the t = 0 instances of rows 2 and 3 (and the t = 1
   instances, which force the empty graph) are vacuous.  Harmless -- the sources quantify over
   t > 0 resp. t >= 0 -- but they mean the small-t instances carry no content.

### Blocked rows

None.

### Notes for the improvement ledger

- `grounding_X220.v` uses the class of VERTEXLESS graphs (`X220_Cnull`) as the non-vacuity
  witness for both twin-width rows.  That is the most degenerate admissible witness; the class
  of EDGELESS graphs is hereditary, small (1 labelled graph per n), of polynomial expansion and
  of twin-width 0, and would carry real signal.  Same for the missing inhabitation lemmas of
  `x220_theta` / `x220_prism` (proved in one line by the second reader during this audit).
- `tw_le` / `tw_ge` (width_params.v) and `x27_treewidth_at_most` (X27.v) are two encodings of
  treewidth inside one package.  `implications_X220.v` names this as the obstacle to closing
  three corpus edges (e050, e051, e053).  A bridge lemma, or a migration of X27 onto
  `tw_le`, is a concrete WP6 item.
- `has_induced_copy`, `is_subdivision_of`, `sline_graph`, `el_graph` are general enough for
  `base/theories/common.v`; `sline_graph` is already a verbatim duplicate of the one in
  `reconstruction-theory/.../U11.v`, which carries a `@MOVE-to-base` marker.
- The log envelope `c * (trunc_log 2 #|G|).+1` (rows 2 and 4) and the natural-coefficient
  Horner polynomial `x220_poly_eval` (rows 6, 7, 9) are now used by several waves; both belong
  in a shared asymptotics/arithmetic foundation rather than per-file.

## X228:minor-theory — second-reader readback (2026-09-23)

Second reader: Claude Opus 5, session 01P75Y6ikkgDyzUzzoef316Z (distinct from the implementer).

### Scope

2 rows of `minor-theory/theories/conjectures/X228.v`, the `layering` / `layered_tw_le` /
`queue_number_le` vocabulary of `foundations/width_params.v`, and `implications_X228.v`.

### Outcome

1 PASS + 1 BLOCKED-CONFIRMED.  `vacuity_probe.py` ok on both.
`check_milestone.py X228 minor-theory` ACCEPTED.

### Per-row verdicts

| row | formal name | verdict | remark |
|---|---|---|---|
| arxiv:1810.08314#00 | `bounded_layered_treewidth_bounded_queue_number_statement` | PASS | layering, layered treewidth and queue number all standard; one f before k and G |
| arxiv:2002.00496#02 | `unavoidable_minor_kelly_construction_statement` | PASS (blocked verdict confirmed) | placeholder is a consequence of the ALREADY-KNOWN direction |

### Blocked rows

- `arxiv:2002.00496#02` stays `blocked`.  The left-hand side (`x228_unavoidable`) is faithful:
  one threshold d, then every finite poset whose dimension is not at most d has H as a minor of
  its cover graph.  The right-hand side of Conjecture 6 -- "H is a minor of some graph from
  Kelly's construction" -- is defined in the source only by Figure 2, with the paper saying
  the general order "can be inferred from the figure"; the offered reformulation (gluing K_4's
  along edges "in a path-like way" and subdividing the "horizontal" edges once) is Figure 3 and
  leaves both the gluing pattern and the horizontal edges undetermined.  The triage note in
  `meta/v2_classification.json` asked for that reformulation to be encoded; the second reader
  agrees with the implementer that it cannot be done faithfully from this paper, and that the
  fix is an element-level definition of Kelly's construction taken from the poset-dimension
  literature.
- Sharper than the implementer's own note: of the two directions of Conjecture 6 only "if" is
  conjectural.  "Only if" is already known, because Kelly's construction supplies posets of
  unbounded dimension whose cover graphs are planar of pathwidth 3.  The committed placeholder
  (`unavoidable H -> wagner_planar H /\ tw_le H 3`) follows from that known direction alone, so
  it carries NONE of the row's open content and is, in the literature, a theorem.  A `Notes:`
  sentence saying so was added to the doc block; it must never be read as the conjecture.

### Notes for the improvement ledger

- `queue_number_le` forbids nested edges with strict inequalities `ord a < ord c < ord d < ord
  b`, so edges sharing an endpoint may share a queue -- the standard convention.  Worth a
  sanity lemma in the foundation (the `'K_2` witness in `grounding_X228.v` does not exercise
  nesting at all; a 4-vertex witness with two genuinely nested edges would).
- `layering` is stated without subtraction (`L u <= (L v).+1 /\ L v <= (L u).+1`); good, and
  reusable by any layered-width row in other packages -- candidate for `base`.
- The blocked row's placeholder Definition is a documented proxy.  `CORPUS_STATUS.md` should
  keep it listed among the placeholders whose body is NOT the row, since a reader who meets
  `unavoidable_minor_kelly_construction_statement` by name would otherwise assume it is.

## X215 (extremal-graph-theory) — second-reader readback (2026-09-23)

Reader: Claude Opus 5 second reader, session 01P75Y6ikkgDyzUzzoef316Z (distinct from
`implemented_by`). Protocol: `magical-snacking-token.md` "Faithfulness protocol",
steps 2 (two-reader source verification), 4 (active probes), 7 (adversarial audit).
Method: the five bodies of `extremal-graph-theory/theories/conjectures/X215.v` were
back-translated from the comment-stripped source before any doc block was read, then
diffed against the `bm-0xx` corpus rows.

### Scope

The 5 Bondy–Murty Appendix A rows of wave X215 (`X215.v`, `grounding_X215.v`,
`implications_X215.v`): bm-033, bm-034, bm-037, bm-038, bm-039.

### Outcome

**4/5 PASS, 1 FAIL** (bm-037, already `blocked`; the FAIL is a *new* finding on top of
the implementer's own blocking reason). `check_milestone.py X215 extremal-graph-theory`
ACCEPTED (11/11 checks, 5/5 axiom-free);
`check_statement_docs.py --ignore-baseline extremal-graph-theory`: 0 errors.

| row | statement | verdict |
|---|---|---|
| bm-033 | `erdos_sos_tree_embedding_statement` | PASS |
| bm-034 | `even_cycle_turan_lower_bound_statement` | PASS |
| bm-037 | `constructive_diagonal_ramsey_lower_bound_statement` | **FAIL** (stays `blocked`) |
| bm-038 | `diagonal_ramsey_root_limit_statement` | PASS-WITH-NOTE (labelled placeholder) |
| bm-039 | `burr_erdos_tree_ramsey_statement` | PASS |

### FAIL — bm-037 is axiom-free REFUTABLE

The implementer blocked the row because "constructivity is a property of a proof, not of a
proposition" and described the compiling body as stating "only the underlying inequality,
which is a known theorem". That understates the problem: **the body states a false
proposition.**

The body is `exists p q, [/\ 0 < q, q < p & forall k N, 0 < k -> N * q ^ k < p ^ k ->
~ x215_arrows N k]`. Its guard admits `k = 1`. Instantiating at `k = 1, N = 1` turns the
hypothesis `N * q ^ k < p ^ k` into `q < p`, which the statement itself asserts, so the
body demands `~ x215_arrows 1 1` — while this very wave's `grounding_X215.v` proves
`x215_arrows_1_1 : x215_arrows 1 1` with `Qed`. Mathematically: r(1,1) = 1, so
r(k,k) ≥ c^k with c > 1 is false at k = 1 (the corpus text's own "for all k ≥ 1" is loose;
r(2,2) = 2 already forces c ≤ √2).

Machine-checked: `meta/probe_hints/constructive_diagonal_ramsey_lower_bound_statement.v`
proves `~ constructive_diagonal_ramsey_lower_bound_statement` in four lines and reports
`Closed under the global context`.

Actions taken: the row keeps `state: "blocked"`; its `blocked_reason` and `note` in
`meta/v2_statement_waves.json` now record the falsity as a *second*, independent reason,
and a `Notes:` paragraph was added to the doc block. The body was **not** touched (second
readers do not edit Definition bodies). The minimal repair, if the placeholder is ever
kept, is the guard `1 < k`; the row would still be blocked for wrong-object reasons.

### Row-by-row

- **bm-033 `erdos_sos_tree_embedding_statement` (PASS).** Source: "If G is a simple graph
  on n vertices with m > n(k−1)/2 edges, then G contains every tree with k edges."
  Back-translation: for every G, T, k with `is_tree [set: T]`, `#|E(T)| = k`, `#|T| = k.+1`
  and `#|G| * k < 2 * #|E(G)| + #|G|`, T embeds into G by an injective adjacency-preserving
  map. The guard is exactly 2m > n(k−1) cleared of the division and of nat subtraction.
  The pair `[#|E(T)| = k, #|T| = k.+1]` under `is_tree` selects **exactly** the trees with
  k edges (for a tree the two are equivalent), so it is neither a strengthening nor a
  weakening; the vertex-count half is redundant mathematically and load-bearing formally
  (coq-graph-theory has no |E| = |V| − 1 lemma, and e239 needs it). `has_subgraph G T` is
  `subgraph T G` = injective + `hom_s`, which with irreflexivity is the strong hom, i.e.
  ordinary (non-induced) subgraph containment — the right notion.
  *k = 0 corner:* the guard becomes `0 < 2m + n`, i.e. "G non-empty". A literal reading of
  the source at k = 0 would say every graph contains the one-vertex tree, which is false
  for the empty graph; the encoding silently repairs that corner, and the doc block says so.
  Small cases sanity-checked: k = 1 (m ≥ 1 ⟹ an edge), k = 2 (m > n/2 ⟹ a vertex of
  degree ≥ 2 ⟹ P_3).
- **bm-034 `even_cycle_turan_lower_bound_statement` (PASS).** `p^k * n^(k+1) <= q^k * m^k`
  is exactly `m >= (p/q) n^(1+1/k)` raised to the k-th power, and restricting c to
  rationals is WLOG (the statement is monotone downward in c). Stating a **lower** bound on
  ex(n, C_2k) as "some C_2k-free graph on n vertices has that many edges" is equivalent to
  a lower bound on the (here undefined) maximum. `~ has_subgraph G (cycle_graph (2*k))` is
  "no C_2k **subgraph**", matching the corpus context's definition of ex.
  *Not vacuous:* any O(n)-edge construction (tree, matching, star) fails
  `p^k n^(k+1) <= q^k m^k` for large n, whatever the positive c, so the statement still
  demands the hard algebraic construction; and `n0` is genuinely needed (the bound cannot
  hold at n = 1).
- **bm-038 `diagonal_ramsey_root_limit_statement` (PASS-WITH-NOTE, labelled placeholder).**
  Back-translation: there is a rational L = p/q such that for every rational tolerance a/b
  and all large k, `(L−ε)^k ≤ r(k,k) ≤ (L+ε)^k`, i.e. r(k,k)^{1/k} → L with **L rational**.
  That is strictly different from the row ("does the limit exist, and what is it?"), and
  the doc block says so in as many words. The nat truncation in `p*b - q*a` only softens the
  lower bound when ε > L and is harmless. Not trivially provable (p = 0 fails on the upper
  bound for a < b and large k) and not refutable with present knowledge.
- **bm-039 `burr_erdos_tree_ramsey_statement` (PASS).** N = 2k = 2n − 2 with n = k + 1, and
  the same tree-with-k-edges encoding as bm-033. `0 < k` excludes exactly the n = 1 corner
  where the literal source bound is false (r(K_1,K_1) = 1 > 0 = 2n−2). Checked **tight** at
  k = 3: T = K_{1,3} has r(T,T) = 6 = 2n−2, so the encoding is not accidentally slack.

### Cross-checks

- `implications_X215.v` proves e239 (Erdős–Sós ⟹ Burr–Erdős) with `Qed` by a genuine
  argument (majority colour class of K_{2k}, `card_edge_Kn`, the arithmetic
  `2k·k < k(2k−1) + 2k`). This is a *non-trivial* implication, so it is a real consistency
  signal for **both** tree encodings rather than the red flag a trivially provable edge
  would be.
- `grounding_X215.v` machine-checks non-vacuity of both tree guards, that the Erdős–Sós
  edge guard rejects (K_2, k = 2) *and* that the conclusion genuinely fails there, C_4-
  freeness of K_3, the settled case r(K_2,K_2) ≤ 2 from the statement's own definitions,
  and `x215_arrows 1 1` / `~ x215_arrows 0 1`.

### Notes for the improvement ledger

- **Infrastructure bug (affects every wave audited on this machine):**
  `meta/vacuity_probe.py` hard-codes `SWITCH = "digraph"`, but this checkout has only the
  `default` opam switch, so every `opam exec --switch digraph -- coqc` invocation exits
  non-zero and the probe reports `auto_true=False auto_false=False`, `hint stale-FIX-OK`,
  **0 FLAGGED — for every statement, including one whose refutation demonstrably compiles.**
  `vacuity_probe.py --wave X215` reported "5 probed · 0 FLAGGED" while
  `constructive_diagonal_ramsey_lower_bound_statement` is refutable. The probe must fail
  loudly when its switch is missing (and `--validate`'s recall guard should have caught
  this); until then its "0 FLAGGED" lines in any 2026-09-23 audit section carry no weight.
  This reader re-ran the ladder with plain `coqc` instead.
- Blocked placeholders are not exempt from mode #2. A placeholder whose body is *false*
  can be cited, proved, or used as an implication hypothesis to derive anything. Worth a
  gate rule: every `blocked` row's placeholder body must also survive the refutation probe,
  or the wave must record that it does not.
- `x215_arrows` / `x215_ramsey_number` (diagonal Ramsey arrow + "N is r(k,k)") are clean,
  reusable and already duplicated in spirit by `x195_arrows` / `x195_ramsey_number` in
  X195.v (family version, k colours). The X195 pair subsumes the X215 pair
  (`x215_arrows N k` = `x195_arrows 'K_N 2 (fun _ => 'K_k)` modulo the colour type);
  candidate for a single shared Ramsey foundation (WP4b/WP6).

## X223 (extremal-graph-theory) — second-reader readback (2026-09-23)

Reader: Claude Opus 5 second reader, session 01P75Y6ikkgDyzUzzoef316Z (distinct from
`implemented_by`). Method: comment-stripped back-translation first, then the corpus rows,
then the four source papers (arXiv:2210.16971, 1810.00058, 1912.02342, 2405.05902 — the
paper-local primitives were re-fetched and compared word for word).

### Scope

All 6 rows of wave X223 (`extremal-graph-theory/theories/conjectures/X223.v`, with
`grounding_X223.v` and `implications_X223.v`). The two X223-planned rows
`axv_1708_07369_00/01` were delivered by re-authoring X195.v / X196.v in place and are
audited in their own section below.

### Outcome

**6/6 PASS** (2 with notes; 1 doc-comment correction applied).
`check_milestone.py X223 extremal-graph-theory` ACCEPTED (11/11 checks, 6/6 axiom-free);
`check_statement_docs.py --ignore-baseline extremal-graph-theory`: 0 errors.

| row | statement | verdict |
|---|---|---|
| arxiv:2210.16971#00 | `directed_sidorenko_bipartite_statement` | PASS |
| arxiv:2210.16971#01 | `directed_forcing_cyclic_statement` | PASS-WITH-NOTE (labelled placeholder) |
| arxiv:1810.00058#01 | `triangle_free_eps_bounded_anticomplete_pair_statement` | PASS (doc comment corrected) |
| arxiv:1810.00058#02 | `h_free_eps_bounded_sparse_pair_statement` | PASS |
| arxiv:1912.02342#00 | `vc_dimension_erdos_hajnal_statement` | PASS |
| arxiv:2405.05902#01 | `induced_turan_even_cycle_sparse_statement` | PASS-WITH-NOTE |

### Verbatim source checks

- arXiv:2210.16971 Definition 1.3: "An oriented graph B is said to have the directed
  Sidorenko property if for every oriented graph G, t(B,G) ≥ t(K⃗₂,G)^{e(B)}" — the
  quantification is over **all oriented G**, which `x223_directed_sidorenko` matches.
  Conjecture 1.4 and Conjecture 1.7 as in the corpus rows; Observation 3.1 confirms the
  hom-to-arc hypothesis is necessary, not decorative.
- arXiv:1810.00058: "A graph G is ε-bounded if |N[v]| < ε|G| for all v ∈ V(G)"
  (**closed** neighbourhood, **strict**); "A pair (A,B) of subsets of V(G) is c-sparse if
  A ∩ B = ∅ and |E(A,B)| ≤ c|A||B|"; "if A,B ⊆ V(G) are disjoint, A is anticomplete to B if
  there is no edge between A and B"; Conjecture 1.4 and Conjecture 3.4 both carry the
  |G| > 1 guard, and 3.4's range is the **closed** interval 0 ≤ c ≤ 1.
- arXiv:1912.02342: VC-dimension of the set system of **open** neighbourhoods
  N(v) = {u : uv ∈ E}; S is shattered when for every B ⊆ S some member A satisfies
  A ∩ S = B. Conjecture 4.1 as in the corpus row.
- arXiv:2405.05902: "Γ is (c,t)-sparse if for every pair of vertex subsets A,B ⊂ V(G)
  (**not necessarily disjoint**) with |A|,|B| ≥ t, we have e(A,B) ≤ (1−c)|A||B|", with
  edges inside A ∩ B counted twice; "ex(Γ,𝒫) is the maximum number of edges of a subgraph
  G ⊆ Γ that belongs to 𝒫".

### Row-by-row

- **2210.16971#00 (PASS).** `num_edges` on a `diGraph` is `#|[pred x : G*G | x.1 -- x.2]|`,
  the **ordered arc count**, which is also hom(K⃗₂, D); so
  `e(D)^{e(B)} * |D|^{|B|} <= hom(B,D) * |D|^{2 e(B)}` is exactly
  t(B,D) ≥ t(arc,D)^{e(B)} cross-multiplied. Nothing asymptotic is dropped: the directed
  Sidorenko inequality is exact for every finite D, the graphon form being a reformulation.
  Corners: |D| = 0 with B empty gives 1 ≤ 1; |D| = 0 with B non-empty gives 0 ≤ anything.
  Spot-checks: B = arc gives equality; B = two disjoint arcs gives equality; B = the cherry
  x→y←z gives Cauchy–Schwarz, which holds — so the statement is not refutable on the easy
  members of its hypothesis class. The `x223_bipartite_dg` hypothesis is **redundant**
  (hom-to-arc already 2-colours the underlying graph), but the source states it too, so
  keeping it is the faithful choice.
- **2210.16971#01 (PASS-WITH-NOTE, labelled placeholder).** The hypotheses are faithful —
  `x223_und_cyclic B` (some non-empty S with `#|S| <= ` the number of arcs inside S) is the
  matroid characterisation of "the underlying graph has a cycle", and it is correct
  *because* B is oriented (for a general digraph the two opposite arcs of a single edge
  would satisfy it). The conclusion is the companion row's Sidorenko conclusion, not
  forcing; the doc block says so plainly. **Warning recorded in the doc block:** since
  hom-to-arc ⟹ bipartite, the placeholder's hypotheses are those of #00 plus "has a
  cycle", so **#00 implies this body outright**. It is neither vacuous nor refutable, but
  it carries no content of its own and must never be an independent endpoint of a corpus
  relation edge.
- **1810.00058#01 (PASS; doc comment corrected).** Every clause matches Conjecture 1.4 at
  H = K_3, including |G| > 1, `induced_free G 'K_3` (the CSSS convention "H-free" = no
  induced copy; for K_3 that is triangle-free), and the (εn^ε, εn)-pair rendered as
  `p^d * |G|^p <= d^d * |A|^d` and `p * |G| <= d * |B|`.
  **Correction applied.** The doc block claimed the closed-neighbourhood form "is the
  weaker hypothesis of the two" compared with X58's Δ form. That is the reverse of the
  truth: |N[v]| = deg(v) + 1, so `d * #|N[v]| < p * #|G|` **implies** `d * Δ(G) < p * #|G|`
  — the closed form is the **stronger condition**, hence the statement it guards is the
  **weaker** one, which is precisely why #00 implies this row and not conversely. That is
  also the direction `implications_X223.v` actually proves (it derives the Δ form from the
  closed form via `opn_proper_cln`). The comment now says this.
  *Degeneracy check:* the hypothesis class is never empty for p < d (any edgeless graph on
  n > d/p vertices qualifies), so no choice of p, d buys a vacuous win; and p = d is
  self-defeating (it would force |A| ≥ n and |B| ≥ n for disjoint A, B).
- **1810.00058#02 (PASS).** Conjecture 3.4 verbatim, including the **closed** range
  0 ≤ c ≤ 1: the `a = 0` instance admitted by `[0 < b, a <= b]` is in the source too, and
  is trivially satisfiable (A = `set0`, B = `setT`), so it neither strengthens nor weakens.
  `x223_edges_between` is the ordered-pair count, which equals |E(A,B)| on the **disjoint**
  A, B that `x223_sparse_pair` requires — matching the source's c-sparse definition.
  Restricting ε to p/d and s to a nat is WLOG: the statement is monotone downward in ε
  (smaller ε shrinks the hypothesis class *and* weakens the conclusion) and downward in
  c^s, so a larger nat s is implied by any real s.
- **1912.02342#00 (PASS).** `x223_shattered` is the standard shattering condition on the
  **open**-neighbourhood set system, exactly as the paper defines it, and
  `x223_vc_dim_leq G d` = "no shattered set exceeds d". ε(d) = 1/q with q a positive nat is
  WLOG because |S| ≥ n^ε is monotone decreasing in ε and every positive real ε dominates
  some 1/q. Corners n = 0 and n = 1 are consistent. Not trivially provable: for bounded
  VC-dimension the best known homogeneous set is e^{(log n)^{1−o(1)}}, far below n^{1/q}
  for fixed q, so the polynomial conclusion carries the conjecture's real content.
  (The manifest records this row as `solved`; the statement is nevertheless an
  open-problem node, and no proof is committed — `check_milestone`'s exact-type probes pass.)
- **2405.05902#01 (PASS-WITH-NOTE).** The **ordered**-pair convention of
  `x223_edges_between` is the source's own: (c,t)-sparseness is stated for A, B *not
  necessarily disjoint*, with edges inside A ∩ B counted twice — so `b * e(A,B) <=
  (b−a) * (|A|*|B|)` is exactly e(A,B) ≤ (1−c)|A||B|. The reduction of ex(Γ,𝒫) ≤ X to
  spanning subgraphs is sound: an arbitrary subgraph G ⊆ Γ is the spanning subgraph with
  the same edges plus isolated vertices, and isolated vertices change neither the edge
  count nor the presence of an induced C_{2l} (a C_{2l} vertex has degree 2). The exponent
  clearing `m^l <= C^l * (t^{l−1} * n^{l+1})` is exactly m ≤ C t^{1−1/l} n^{1+1/l}.
  *Note:* `0 < l` admits l = 1, where the source writes C_{2l} and means l ≥ 2; that
  instance reduces to m ≤ C n² with C > 1 and is trivially true, so it neither strengthens
  nor weakens the statement. *Note:* Conjecture 6.1's own printed text could **not** be
  re-fetched (Section 6 is truncated in every HTML rendering reachable from here); the two
  primitives it is built from were verified verbatim, and the paper's abstract confirms the
  (c,t)-sparse setup, but the conjecture wording rests on the corpus review quotation.

### Cross-checks

- `implications_X223.v` proves e076 (X58's `epsilon_bounded_h_free_anticomplete_pair` ⟹
  this row's K_3 case) with `Qed`, and the proof step that converts closed-neighbourhood
  ε-boundedness into the Δ form is the machine-checked witness for the correction above.
- e160 (X195 ⟹ X196) is also proved here, see the X195/X196 section.
- `grounding_X223.v` covers, per row: non-vacuity of the arc hypotheses and teeth for
  hom-to-arc and for `oriented`; teeth and inhabitation for `x223_und_cyclic`;
  satisfiability of the triangle-free ε-bounded guard and its failure on K_1;
  the empty pair as a c-sparse witness and an adjacent pair as a non-0-sparse one;
  `x223_vc_dim_leq 'K_1 2` with `~ x223_shattered [set: 'K_1]`; and
  `x223_ct_sparse (compl 'K_2) 1 1 1` with `~ x223_ct_sparse 'K_2 1 1 1`.

### Notes for the improvement ledger

- `x223_eps_bounded` (closed form) and X58's `x58_epsilon_bounded` (Δ form) are two
  encodings of the same source notion living in two files of the same package, with one
  implication proved between them. They belong together in
  `extremal-graph-theory/theories/foundations/` with the implication as a sanity lemma;
  the doc-comment error corrected here is exactly the kind of mistake that duplication
  invites.
- `x223_anticomplete` duplicates `x58_anticomplete` verbatim; `x223_edges_between`
  (ordered-pair e(A,B)) is a genuinely reusable primitive and a natural
  `base/theories/common.v` candidate, but it needs a sanity lemma pinning the
  disjoint-case identity `x223_edges_between A B = #|E(A,B)|`, since two rows of this very
  wave rely on *different* halves of that fact (one on the disjoint identity, one on the
  double-counting).
- `x223_bipartite_dg` duplicates `base`'s `bipartite` at the `diGraph` level; the
  duplicate-suffix warning of the doc gate should be extended to directed variants.

## X229:extremal-graph-theory — second-reader readback (2026-09-23)

Reader: Claude Opus 5 second reader, session 01P75Y6ikkgDyzUzzoef316Z (distinct from
`implemented_by`). The paper-local vocabulary was re-fetched from arXiv:2309.04460 and
compared against the implementer's transcription, as the wave entry asked.

### Scope

The single row of wave X229 in `extremal-graph-theory`
(`extremal-graph-theory/theories/conjectures/X229.v`, grounding `grounding_X229.v`,
new vocabulary in `extremal-graph-theory/theories/foundations/edge_colourings.v`).

### Outcome

**1/1 PASS.** `check_milestone.py X229 extremal-graph-theory` ACCEPTED (11/11 checks,
1/1 axiom-free); `check_statement_docs.py --ignore-baseline extremal-graph-theory`:
0 errors.

| row | statement | verdict |
|---|---|---|
| arxiv:2309.04460#01 | `expander_proper_colouring_two_connected_palettes_statement` | PASS |

### Definition 3.1, verbatim

Re-fetched and matched word for word against the doc block's transcription:

> "A graph G on n ≥ 1 vertices is called a robust sublinear expander if for every
> 0 ≤ ε ≤ 1 and every non-empty subset U ⊆ V(G) of size |U| ≤ n^{1−ε} the following holds.
> For every subset F ⊆ E(G) of |F| ≤ (ε/3)·d(G)·|U| edges, we have
> |N_{G−F}(U)| ≥ (ε/3)·|U|."

The Notation paragraph confirms **both** load-bearing readings: the neighbourhood of a
vertex set U is "the set of vertices in V(G)∖U that are adjacent to a vertex in U" (so
`x229_ext_neigh = NS(U) :\: U` is right, and a closed-neighbourhood reading would have been
a wrong-object bug), and "we denote the **average** degree of a graph G by d(G)" (so
d(G) = 2|E|/n is right, and a minimum-degree reading would have been another).

### The three nat clearings

With ε = a/b, 0 ≤ a ≤ b, 0 < b:

| source | Rocq | check |
|---|---|---|
| \|U\| ≤ n^{1−ε} | `#\|U\| ^ b <= #\|G\| ^ (b - a)` | raise to the b-th power; nat subtraction safe since a ≤ b |
| \|F\| ≤ (ε/3)·d(G)·\|U\| | `3*b*(#\|G\| * #\|F\|) <= 2*a*(#\|E(G)\| * #\|U\|)` | multiply by 3bn, using d(G) = 2\|E\|/n |
| \|N_{G−F}(U)\| ≥ (ε/3)·\|U\| | `a * #\|U\| <= 3*b*#\|N\|` | multiply by 3b |

**Restricting ε to the rationals loses nothing.** For fixed U and F the admissible real ε
form an interval [lo, hi] with lo = 3|F|/(d(G)|U|) — a **rational** number, all quantities
being integers — and hi = min(1, 1 − log_n|U|). The conclusion |N| ≥ (ε/3)|U| is a closed
inequality between integers, so it holds at hi iff it holds for all rational ε < hi; and
when lo = hi, lo being rational makes hi rational and attained. Hence the rational
instances already force the real definition. (Had the lower endpoint been irrational, the
rational restriction could have made the expander condition strictly easier and thus the
statement — which has it as a *hypothesis* — strictly stronger.)

*Corners.* a = 0 forces |F| = 0 and a vacuous conclusion; a = b forces |U| = 1 and
"the vertex still has a neighbour after deleting ≤ d(G)/3 edges", which is the source's own
remark that no one-vertex graph is a robust sublinear expander — machine-checked as
`not_rse_K1`, with `rse_K2` for inhabitation. A 0-vertex G is vacuously an expander here
(the `0 < #|U|` guard bites) but the conclusion is then vacuously true, so nothing leaks.
`F \subset E(G)` is the source's own restriction and is also harmless to drop: a set with
non-edges deletes the same edges with a larger cardinality, so its instance is implied by
the instance of F ∩ E(G).

### The average-degree guard

`forall L, 2 ^ L <= #|G| -> C * (#|G| * L) <= 2 * #|E(G)|` says d(G) ≥ C·⌊log₂ n⌋. Since C
is **existentially** quantified, this is equivalent to the source's "average degree at
least C log n" in both directions: log₂ n ≥ ln n gives one direction with the same C, and
⌊log₂ n⌋ ≥ (log₂ n)/2 for n ≥ 2 gives the other with C/2 (n = 1 is degenerate on both
sides, and is not an expander anyway). Teeth are machine-checked: K_2 meets the guard at
C = 1 and fails it at C = 3.

### The conclusion

"Decomposed into two spanning connected subgraphs such that every colour appears on only
one of them" is rendered as a predicate P on an arbitrary colour `finType` plus
`connected [set: colour_class col P]` and `connected [set: colour_class col (predC P)]`.
`colour_class` keeps G's vertex type, so both parts are automatically **spanning**, and
`card_edges_colour_class_split` (in `edge_colourings.v`) proves their edge sets partition
E(G) — so "every colour on only one of them" is exact, not approximated. The degenerate
split P = `pred0` cannot cheat: an edgeless spanning subgraph is disconnected as soon as
|G| > 1. `proper_ecolouring col` is the standard condition (two edges sharing a vertex get
distinct colours), with `proper_ecolouring_id` and `not_proper_ecolouring_const_K3` as
inhabitation/teeth.

*Not vacuous by construction:* for any C, large complete graphs are robust sublinear
expanders with d(G) = n − 1 ≥ C log n and are properly edge-colourable, so no choice of C
empties the hypothesis class. (This is an argument, not a machine-checked lemma; the
grounding stops at K_2.)

### Caveat

**Question 10.2 itself could not be re-fetched.** Section 10 is truncated in every HTML
rendering of arXiv:2309.04460 reachable from here, so the conjecture wording was checked
only against the corpus review quotation ("Does there exist a constant C > 0 such that the
edges of any n-vertex properly edge-coloured robust sublinear expander G with average
degree at least C log n can be decomposed into two spanning connected subgraphs in such a
way that every colour appears on only one of them?"), which the body matches clause by
clause. Definition 3.1 and the d(G)/N(U) notation — the parts the wave entry flagged as
risky — *were* verified at the source.

### Notes for the improvement ledger

- `x229_robust_sublinear_expander` is a paper-local primitive with real faithfulness risk
  (external vs closed neighbourhood, average vs minimum degree, the ε interval). It now has
  two grounding lemmas; it deserves a `faithfulness_mutation.py` canary each for (a) the
  `:\: U` of `x229_ext_neigh`, (b) the `2 *` of the average-degree reading, and (c) the
  `0 < #|U|` guard — all three are single-token mutations that `not_rse_K1` / `rse_K2`
  would plausibly *survive*.
- `edge_colourings.v` (`colour_class`, `mono_copy`, `proper_ecolouring`,
  `card_edges_colour_class_split`, `majority_colour`) is well-built and already shared by
  X215, X229 and X195; `proper_ecolouring` and `colour_class` in particular duplicate
  nothing in `base` yet are not extremal-specific — promote to `base/theories/common.v`
  (WP4b) before a second package re-invents them.
- The "d(G) ≥ C·⌊log₂ n⌋" idiom for "average degree ≥ C log n" is reusable and subtle
  enough (the floor, the base change, the direction of the existential) that it should live
  in `GTBase.asymptotics` with the equivalence argument attached, not be re-derived per row.

## X195 / X196 (extremal-graph-theory) — second-reader readback of the re-authored rows (2026-09-23)

Reader: Claude Opus 5 second reader, session 01P75Y6ikkgDyzUzzoef316Z (distinct from
`implemented_by`). These two rows were re-encoded **in place** during the X223 pass, under
their existing formal names, after the 2026-07-17 blocked-retargeting audit
(`meta/BLOCKED_RETARGETING_AUDIT.md`) rejected the 2026-07-16 encoding.

### Scope

`extremal-graph-theory/theories/conjectures/X195.v` (row arxiv:1708.07369#00, Question 1.1)
and `X196.v` (row arxiv:1708.07369#01, Conjecture 1.5), plus the shared vocabulary
`x195_contains_forest`, `x195_arrows`, `x195_ramsey_number`, `x195_k_nice` in X195.v and
`mono_copy` in `foundations/edge_colourings.v`. Source: arXiv:1708.07369, "Ramsey-nice
families of graphs".

### Outcome

**2/2 PASS.** `check_milestone.py X195 extremal-graph-theory` and
`check_milestone.py X196 extremal-graph-theory` both ACCEPTED (11/11 checks, 1/1
axiom-free each); `check_statement_docs.py --ignore-baseline extremal-graph-theory`:
0 errors.

| row | statement | verdict |
|---|---|---|
| arxiv:1708.07369#00 | `ramsey_nice_forest_family_eventual_statement` | PASS |
| arxiv:1708.07369#01 | `ramsey_nice_forest_family_infinite_statement` | PASS |

### The recovered definitions, verbatim

Both paper-local notions were re-fetched from the source and match the implementer's
transcription word for word:

> R_k(ℱ) is "the smallest integer n for which every k-coloring of the edges of the complete
> graph K_n yields a monochromatic copy of some F ∈ ℱ";
> "ℱ is k-nice if for every graph G with χ(G) = R_k(ℱ) and for every k-coloring of E(G)
> there exists a monochromatic copy of some F ∈ ℱ".

Mapping, clause by clause:

- `x195_arrows Host k Fam := forall col : {set Host} -> 'I_k, exists i c,
  mono_copy (Fam i) col c` — "every k-colouring of E(Host) yields a monochromatic copy of
  some member". The colourings take values in `'I_k`, so **k is load-bearing**, which is
  precisely what the 2026-07-17 audit found missing (the old `x195_k_nice` hard-coded two
  colours and ignored its `k` argument, which made X196's "for infinitely many k" vacuous).
  `mono_copy F col c` is an *injective adjacency-preserving* map with `col [set emb x;
  emb y] = c` on every edge — a (not necessarily induced) monochromatic copy, the right
  Ramsey notion; `mono_copyP` relates it to `has_subgraph (colour_class col (pred1 c)) F`,
  an independent re-encoding that is proved equivalent.
- `x195_ramsey_number k Fam n := x195_arrows 'K_n k Fam /\ forall m < n,
  ~ x195_arrows 'K_m k Fam` — "n is the **least** n with K_n → (ℱ)_k", i.e. n = R_k(ℱ).
- `x195_k_nice k Fam := forall n, x195_ramsey_number k Fam n -> forall G,
  χ([set: G]) = n -> x195_arrows G k Fam` — quantifies over **all** graphs of chromatic
  number R_k(ℱ), as the source does. A family whose Ramsey number does not exist is
  vacuously k-nice, exactly as in the source, where "for every G with χ(G) = R_k(ℱ)"
  presupposes it. (R_k(ℱ) is unique when it exists, so taking it as a hypothesis rather
  than as a function is not a weakening.)
- "finite family" as `Fam : 'I_r -> sgraph` (repeats allowed, harmless) and "contains at
  least one forest" as `exists i, is_forest [set: Fam i]` (`is_forest` is the library's
  path-uniqueness notion, not an edge count) are faithful. `0 < r` is redundant —
  `x195_contains_forest` already exhibits an index in `'I_r` — but harmless.
- Question 1.1 is `exists k0, forall k >= k0, k-nice`; Conjecture 1.5 is
  `forall k0, exists k >= k0, k-nice`, the standard finite rendering of "for infinitely
  many k".

### Adversarial checks

- **k = 0**: `'I_0` is empty, so `x195_arrows Host 0 Fam` is vacuously true for every Host,
  R_0(ℱ) = 0, and 0-niceness holds trivially. Harmless: both statements only assert
  k-niceness for *large* k.
- **Degenerate families**: ℱ = {K_1} gives R_k = 1 for k ≥ 1 and k-niceness for every
  k ≥ 1 (χ(G) = 1 means G edgeless and non-empty); ℱ = {the empty graph} gives R_k = 0;
  ℱ = {K_2} gives R_k = 2 and k-niceness for every k. None of these produces a
  counterexample, so the statements are not refutable on the easy members of the
  hypothesis class.
- **Non-vacuity of the inner quantifier**: R_k(ℱ) ≥ 1 for any family with a non-empty
  member, and K_{R_k} itself has chromatic number R_k, so `forall G, χ(G) = n -> ...` is
  never an empty quantifier — the conjecture's content is exactly about the *other* graphs
  of that chromatic number.
- **e160 is genuinely proved** (`implications_X223.v`, `Qed`,
  `exists (maxn k0 k1)`): eventually ⟹ infinitely often. The protocol treats trivially
  provable edges as red flags; here the triviality is the *correct* logical relation
  between Question 1.1 and its explicitly weaker companion Conjecture 1.5, and — this is
  the point — it is only non-vacuous **because** `x195_k_nice` now depends on k. Under the
  2026-07-16 encoding the same edge would have been provable for the wrong reason.

### Notes for the improvement ledger

- `x195_arrows` / `x195_ramsey_number` (family, k colours) strictly subsume
  `x215_arrows` / `x215_ramsey_number` (diagonal, 2 colours) written in the *same package*
  on the *same day*: `x215_arrows N k` is `x195_arrows 'K_N 2 (fun _ => 'K_k)` modulo the
  colour type. One shared Ramsey foundation (arrow relation, Ramsey number as "least n",
  monochromatic copy) belongs in `extremal-graph-theory/theories/foundations/`, with the
  two specialisations derived — and it would immediately have exposed the k = 1 corner that
  refutes X215's bm-037 placeholder.
- This row is a good argument for making the "recovered paper-local definition" case a
  first-class artefact: the 2026-07-16 encoding was blocked for a *missing* definition and
  then re-authored from one fetched at authoring time, with no record in the repo of the
  fetched text beyond a doc comment. A `meta/recovered_definitions/<row>.md` holding the
  quoted source paragraph would make the next readback a diff instead of a re-fetch —
  which matters, since Question 10.2 of X229 could **not** be re-fetched at all.

## X216/X217/X225/X227/X228 (misc, hypergraph, homomorphism, topological, infinite) — second-reader readback (2026-09-23)

Reader: Claude Opus 5 second reader, session 01P75Y6ikkgDyzUzzoef316Z (distinct
from `implemented_by`). Protocol: `magical-snacking-token.md` "Faithfulness
protocol", steps 2 (two-reader source verification), 4 (active probes) and 7
(adversarial audit). Nine wave entries, 19 rows, read back from the Rocq bodies
before the doc blocks; the two new foundations (`graph-theory-misc/theories/
foundations/cops.v`, `hypergraph-theory/theories/foundations/hypergraph.v`) were
read in full. Papers fetched where the encoding turned on a convention:
arXiv:2206.13635 (Steiner, hypergraph minors), arXiv:2307.15512 (hypergraph cop
game), arXiv:2208.06858 (AFKK, `eps**` and `K(n)`), arXiv:2202.07746 (Campion
Loth–Mohar, Conjecture 4).

### Outcome

**18/19 PASS, 1 FAIL.** One row is moved to `state: "blocked"`:
`axv_2202_07746_00` / `random_embedding_expected_faces_third_statement`
(X228:topological-graph-theory) is **refutable as written**.

| wave | row | statement | verdict |
|---|---|---|---|
| X216:graph-theory-misc | bm_021 | `second_hamilton_cycle_cubic_polytime_statement` | PASS (blocked verdict confirmed) |
| X216:graph-theory-misc | bm_022 | `internally_disjoint_odd_paths_conp_statement` | PASS-WITH-NOTE (blocked; one further defect found) |
| X217:graph-theory-misc | oth_meyniels_conjecture | `meyniel_cop_number_sqrt_statement` | PASS |
| X227:graph-theory-misc | axv_1812_09752_00 | `hat_guessing_degree_degeneracy_bounds_statement` | PASS |
| X227:graph-theory-misc | axv_2107_05995_00 | `hat_guessing_degeneracy_bounded_statement` | PASS |
| X227:graph-theory-misc | axv_2208_06858_04 | `independent_set_binomial_gap_statement` | PASS-WITH-NOTE |
| X227:graph-theory-misc | axv_2208_06858_03 | `independent_set_correlated_gap_statement` | PASS (blocked verdict confirmed) |
| X227:graph-theory-misc | axv_2208_06858_00 | `levine_hat_intersecting_success_vanishes_statement` | PASS (blocked verdict confirmed) |
| X227:graph-theory-misc | axv_2208_06858_01 | `levine_hat_monotone_success_vanishes_statement` | PASS (blocked verdict confirmed) |
| X217:hypergraph-theory | axv_2307_15512_00 | `hypergraph_cop_number_sqrt_n_over_k_statement` | PASS |
| X225 | axv_2206_13635_00 | `kt_minor_free_hypergraph_chromatic_three_halves_statement` | PASS |
| X225 | axv_2206_13635_01 | `k3_minor_free_hypergraph_three_colourable_statement` | PASS |
| X225 | axv_2401_00359_01 | `kpartite_hypergraph_turan_exponent_dmax_statement` | PASS-WITH-NOTE |
| X225 | axv_2401_00359_02 | `latin_square_hypergraph_turan_exponent_statement` | PASS |
| X227:homomorphism-theory | axv_2208_06858_02 | `kneser_cartesian_power_independence_ratio_statement` | PASS |
| X228:topological-graph-theory | axv_2103_05036_00 | `random_embedding_expected_faces_linear_statement` | PASS-WITH-NOTE |
| X228:topological-graph-theory | axv_2202_07746_00 | `random_embedding_expected_faces_third_statement` | **FAIL → blocked** |
| X216:infinite-graph-theory | bm_003 | `halin_hypomorphic_infinite_subgraph_statement` | PASS |
| X228:infinite-graph-theory | axv_2506_08810_03 | `infinite_tournament_induced_saturation_statement` | PASS |

### The FAIL: `random_embedding_expected_faces_third_statement` (Conjecture 4)

The body is `forall G : sgraph, 3 * x228_total_faces G <= (#|G| + 3) * x228_nrot G`,
with no connectedness hypothesis. Take **four disjoint edges**: every vertex has
degree ≤ 1, so the graph has exactly one rotation system (`x228_nrot_deg1`, the
identity) and its face permutation is the dart involution, whose orbits are the
four edges. Hence `n = 8`, `nrot = 1`, `total_faces = 4`, and the body asserts
`12 <= 11`. A `Qed`-closed, `Print Assumptions`-clean witness is deposited at
`meta/probe_hints/random_embedding_expected_faces_third_statement.v` (it proves
`4 <= x228_total_faces M8` from four pairwise distinct `porbit`s, so it needs no
`vm_compute` on a `finType` and no new axiom).

Why the source is not refuted by this: Campion Loth–Mohar average over **2-cell
embeddings**, which exist only for a *connected* graph, and their extremal
example (a chain of triangles joined by cut edges) is connected. `E[F] ≤ n/3 + 1`
has an additive constant **per connected component**, so a disjoint union of `k`
components satisfies only `E[F] ≤ n/3 + k`. The encoding silently extended the
domain to all simple graphs, where the "+ 1" is false. Everything else in the
row checks out (the rotation-system enumeration is the verbatim boolean form of
`surface.v`'s two record fields, `x228_faces` is `surface_embedding_faces`, and
the cleared division `3 * total <= (n + 3) * nrot` is the right clearing of
`E[F] ≤ n/3 + 1`), so the fix is exactly one guard: `connected [set: G]`.

Two consequences recorded: (a) the `status=verified` edge `gc:e125` in
`topological-graph-theory/theories/conjectures/implications_X228.v` is now an
implication out of a false hypothesis and is no longer a consistency signal;
(b) the companion `O(n)` row is **not** affected — rotation systems multiply and
face counts add over connected components, so its universal form follows from the
connected case with the same constant (noted in its doc block).

### Blocked rows (verdicts confirmed, no faithfulness claimed)

- `bm_021`, `bm_022` (X216:graph-theory-misc) — "is this problem in P / co-NP?"
  are verdicts about a model of computation; `GTBase.complexity` fixes one
  interpreter and one encoding. For `bm_022` the reader adds a **fourth** defect
  to the three recorded: `x216_odd_xy_path` constrains only the first and last
  vertex, so internal vertices may lie in `X` or `Y` — not the standard
  `(X,Y)`-path convention. Added to the doc block.
- `axv_2208_06858_03` — `alpha*(G)` needs correlated distributions with
  Bernoulli(1/2) marginals over `V(G)^r`; the placeholder body IS the binomial
  companion and says so.
- `axv_2208_06858_00`, `_01` — `p_intersecting`/`p_monotone` need a probability
  layer over families of subsets of the cube; the class label is inert, so the
  two bodies are literally the same proposition and both are refutable. The
  refutation is split across two grounding lemmas (`x227_half_levine`,
  `x227_half_not_to_zero`) so no theorem of type `~ <stmt>` is committed — legal
  for `blocked` rows, and disclosed, but recorded here.
- `axv_2202_07746_00` — newly blocked, see above.

### Adversarial checks that passed

- **Cops-and-robbers (both packages).** The two games are independent but
  structurally identical, and both match their sources clause for clause: cops
  place first and the robber answers (`exists C0, forall r0`), cops move first
  each round, both sides may pass (the reflexive disjunct in `cop_move` /
  `robber_move` / `hg_move`), and a cop landing on the robber ends the play
  before he answers. arXiv:2307.15512 §1.1 confirms "cops move first", "not every
  piece must be moved in every turn" and "the cops win if at some point a cop
  occupies the same vertex as the robber"; the `others:meyniels-conjecture`
  `context_text` says the same for graphs. The bounded-horizon existential is the
  standard winning condition on a finite position space (`cops_capture_mono` /
  the `hg_win` fixpoint), and `cop_number_le G k := exists j <= k, cops_win j` is
  `c(G) <= k` without needing monotonicity in the number of cops.
- **`k <= #|T|` in the hypergraph row** has teeth and is not a hidden weakening:
  the edgeless one-vertex hypergraph is vacuously `k`-uniform for *every* `k` and
  connected, with cop number 1, so without the guard the body would say
  `k <= C^2` for all `k`; and any hypergraph with a hyperedge satisfies `k <= n`.
- **Steiner's minor convention** (the highest-risk item of X225) was settled from
  the paper, not only from the `h(2)` cross-check: Steiner defines `H − v` as the
  *induced* subhypergraph (the vertex **and every hyperedge containing it** are
  deleted) and minors by deletions plus hyperedge contraction. Hence a branch set
  can only be contracted through hyperedges lying entirely inside it — exactly
  `hg_connected_on` on `hg_restrict` — and the joining hyperedge must lie inside
  the union of the two branch sets. Under the alternative (trace) reading every
  loopless hypergraph with a hyperedge would have a `K_2` minor and `h(2)` would
  be 1, contradicting the paper's own lower bound. The paper also assumes
  globally that hyperedges have ≥ 2 vertices, so `hg_loopless` is its convention
  and not an added guard.
- **`d_i` / `d_max`** (Conjecture 6.2): the corpus `context_text` pins the
  reading — "the 1-skeleton of `H_L` is `K_{d,d,d}`" matches `hg_skeleton E 1` =
  the 2-sets inside a hyperedge, and "`d_1(H_L), d_2(H_L) = Θ(d)`" matches the
  degeneracies of those skeletons (2d and d for `H_L`). `F != set0` with
  `2 <= k` forces `d_max >= 1`, so the cleared exponent is never divided by 0.
- **Turán algebra**: `ex^dmax * n^ck <= K * n^{k*dmax}` ⟺ `ex <= K' n^{k−ck/dmax}`
  and `n^{3d} <= ex^d n^a` / `ex^d n^b <= n^{3d}` ⟺ `n^{3−a/d} <= ex <= n^{3−b/d}`;
  directions, guards (`2 <= d`) and the outermost `a, b` all check out.
- **Kneser double limit**: the outer limit is the strong `exists T, forall t >= T`
  and the inner one is a `limsup` (`exists n0, forall n >= n0`), so nothing is
  smuggled in about the existence of the inner limit; `K(n)` is on the *whole*
  cube, matching the paper's "graph on vertex set {0,1}^n, edge iff disjoint
  support".
- **Hat guessing**: locality is over the open neighbourhood, winning is "one
  correct guess on *every* colouring", `HG >= q` / `HG <= m` are the bare
  existential / universal (no maximisation, no monotonicity in `q`), part (iii)
  is the *exact* minimum degree as the source says, and `f3 → ∞` is
  `forall M, eventually (M <= f3 d)`.
- **Halin**: the asymmetry is deliberate and correct — "isomorphic to a subgraph"
  is non-induced containment, the hypomorphism clause uses induced vertex-deleted
  subgraphs, both graphs are required infinite, and the conclusion is the
  conjunction. The row is `disproved` upstream and no unconditional refutation is
  committed in the package.
- **Infinite tournaments**: the nonemptiness clause of the perturbation is
  load-bearing (without it `S` perturbs itself and the conjecture is
  self-contradictory); "locally finite" per vertex on `nat` is exactly finiteness
  of the changed set at that vertex, and constraining only the out-arcs also
  constrains the in-arcs because both relations are tournaments.
- **Vacuity / probes**: `meta/vacuity_probe.py` over all 19 statements of the
  nine waves reports **19 probed, 1 FLAGGED** — the auto ladder settles neither
  polarity of any statement, and the single flag is
  `random_embedding_expected_faces_third_statement`, where the newly deposited
  hint `settles` it (the FAIL above). The probe had to be re-run with
  `SWITCH = "default"`, because the hard-coded `digraph` switch does not exist on
  this machine and every `coqc` call then fails silently — see the ledger note
  below.

### Notes for the improvement ledger

- **`meta/vacuity_probe.py` hard-codes `SWITCH = "digraph"`.** On a machine whose
  only opam switch is `default`, every `coqc` invocation fails and *every*
  statement is reported `ok` — a silent false green. The switch should come from
  an environment variable (or the probe should abort when the toolchain call
  fails for a reason other than a Rocq error).
- **`x228_nrot G >= 1` is assumed, not proved.** The cleared division is only
  faithful because a finite graph always has at least one rotation system; the
  committed lemma covers only maximum degree ≤ 1. A general
  `0 < x228_nrot G` (product of `(deg v − 1)!`) belongs in the foundation, and
  would also make the two X228 statements provably non-vacuous for every `G`.
- **Face count of an edgeless graph is 0, not 1.** `x228_faces` counts dart
  orbits, so an isolated vertex (or the empty graph) contributes no face where
  the topological count would give one sphere face. Harmless for both rows as
  encoded, but a foundation-level comment would prevent a future row from
  inheriting the discrepancy.
- **Connectedness is the recurring missing guard in embedding rows.** Anything
  whose source quantity is defined through a 2-cell embedding needs
  `connected [set: G]`; X228's Conjecture 4 is the second instance in the corpus
  after the `euler_genus` disconnected-understatement recorded in
  `FAITHFULNESS_CHECKS.md`. Worth a checklist item in the wave template.
- **Inert labels in placeholders.** `x227_family_class` makes two `blocked` rows
  the *same* proposition. That is honest but brittle: a later reader could
  mistake the pair for two distinct encodings. Consider a naming convention
  (e.g. a `_placeholder` suffix, or a single shared `Definition`) for bodies that
  carry no row content.
- **Two foundations now own a cops-and-robbers game** (`cops.v` on `sgraph`,
  `hypergraph.v` on `{set {set T}}`), with no bridge. Closing `gc:e243`
  (hypergraph conjecture ⟹ Meyniel at `k = 2`) needs that bridge; it is the
  natural WP6 item, and would also cross-validate both encodings.
- **`hg_connected` name clash with `Hypergraph.conjectures.U12`** (vertex- vs
  Berge edge-connectivity) is already flagged in the foundation header; it is a
  real WP6 hazard because the two differ exactly on hypergraphs with isolated
  vertices, which is the degenerate case the X217 guard is about.
- **`independent_set_binomial_gap_statement` encodes the source's displayed
  restatement, not its headline `eps**(alpha) > 0`.** The two differ by one
  uniformity (an `eps` valid for every ratio ≥ α, equivalently the monotone
  `eps**`). The doc block's original justification ("the infimum over the smaller
  alphas") was wrong in direction and has been corrected. If WP6 ever wants the
  headline form, it is `forall a b, exists e, forall G, ratio(G) >= a/b -> ...`
  with `ratio(G)` on the right-hand side.


## X212 (cycle-theory) — second-reader readback (2026-09-23)

Reader: Claude Opus 5 second reader, session 01P75Y6ikkgDyzUzzoef316Z
(distinct from `implemented_by`). Protocol: `magical-snacking-token.md`
"Faithfulness protocol", steps 2 (two-reader source verification), 3/4
(grounding + active probes) and 7 (adversarial audit).

### Scope

The eight Bondy–Murty rows of wave X212 in `cycle-theory`
(`cycle-theory/theories/conjectures/X212.v`, grounding `grounding_X212.v`,
implications `implications_X212.v`), plus the shared foundations they rest on
(`cycle-theory/theories/foundations/connectivity.v`, `U6.v`).

### Outcome

**6/8 PASS; 2 rows FAIL and are now `blocked`** (`bm-013`, `bm-026`).
One of the two failures is an **axiom-free refutation**, machine-checked and
committed as `meta/probe_hints/small_cycle_double_cover_statement.v`.

| row | statement | verdict |
|---|---|---|
| bm_011 | `barat_thomassen_tree_decomposition_statement` | PASS |
| bm_013 | `small_cycle_double_cover_statement` | **FAIL — refutable** (blocked) |
| bm_016 | `linear_arboricity_regular_statement` | PASS-WITH-NOTE |
| bm_026 | `orientable_five_cycle_double_cover_statement` | **FAIL — wrong hypothesis** (blocked) |
| bm_062 | `kotzig_unique_k_path_statement` | PASS |
| bm_064 | `smith_two_longest_cycles_statement` | PASS |
| bm_065 | `bondy_linear_cycle_cubic_statement` | PASS |
| bm_066 | `birmele_long_cycle_transversal_statement` | PASS-WITH-NOTE |

### The two blockers

#### A. `bridgeless` is a DIRECTED predicate (affects bm-013, bm-026, and X228)

`connectivity.v` defines

```coq
Definition is_bridge (G : mgraph) (e : edge G) : Prop :=
  eseparates (source e) (target e) [set e].
Definition bridgeless (G : mgraph) : Prop := forall e : edge G, ~ is_bridge e.
```

and coq-graph-theory's `eseparates x y E := forall w, walk x y w -> exists2 f, f \in E & f \in w`
quantifies over `walk`, which is **directed**
(`walk x y (e :: w) = (source e == x) && walk (target e) y w`, `mgraph.v:981`).
So `bridgeless G` says: *every arc `u -> v` has an alternative **directed** route
`u -> ... -> v`* — not "no cut edge". The file's own comments record the
directedness (`grounding_X212.v:131-133` even notes that the antiparallel digon
`Gd` fails it) but treat it as a harmless caveat. It is not, and the "just pick a
good orientation (Robbins)" rescue does **not** work: a cyclically oriented
triangle is *not* bridgeless (the only arc out of a vertex is the one to be
avoided), and neither is any other orientation of a cycle.

Two consequences were proved during the readback, `Qed` and *Closed under the
global context* (scratch proof, reproduced here for the ledger):

```coq
Lemma bridgeless_outdeg2 (G : mgraph) (e : edge G) :
  bridgeless G -> source e != target e ->
  exists2 f : edge G, f != e & source f == source e.
Lemma bridgeless_indeg2 (G : mgraph) (e : edge G) :
  bridgeless G -> source e != target e ->
  exists2 f : edge G, f != e & target f == target e.
```

(The first: if `e` is the only arc leaving `source e`, every directed walk from
`source e` must begin with `e`, and the empty walk is excluded by
`source e != target e`, so `e` *is* a bridge. The second is the same argument on
the last arc of the walk, via an auxiliary `walk_last`.)

Corollaries, elementary from those two lemmas:

* a **simple** carrier in the class has `mdeg v >= 4` at every non-isolated
  vertex (two distinct out-arcs and two distinct in-arcs, all distinct because
  the graph is loopless): **minimum degree at least 4**;
* in a **cubic** loopless multigraph, `outdeg v + indeg v = 3` with each of them
  `0` or `>= 2`, so every vertex is a pure source or a pure sink; every arc then
  goes source → sink, a detour has length 1, hence every arc needs a parallel
  partner, hence the graph is a disjoint union of **triple-edge dipoles**.

So the hypothesis class of `bm-026` contains no cycle, no cubic simple graph, no
Petersen graph and no snark: it omits the entire content of the orientable
5-CDC conjecture. This is failure mode 4 (too weak / proxy) at a scale that
makes the row not a rendering of its source, so PASS-WITH-NOTE was rejected and
the row is `blocked`.

**Inherited, not introduced by this wave.** The same predicate underlies the
already committed `cycle_double_cover_statement` (`U6.v`), `five_flow_statement`
(`D1.v`) and `cubic_bridgeless` (`U10.v`) — the last one being, by the corollary
above, satisfied *only* by disjoint unions of triple-edge dipoles. Those rows are
outside this readback's mandate and are flagged for a user decision. The repair
is one line: state `is_bridge` with the **undirected** `uwalk` that
`GTBase.base` already provides (`base.v:320-326`) and re-verify the dependents.

#### B. `simple_mgraph` does not exclude doubled edges — bm-013 is refutable

`U6.simple_mgraph G := loopless G /\ forall x y, #|edges x y| <= 1`, and
`mgraph.edges x y = [set e | (source e == x) && (target e == y)]` is **directed**.
A pair of *antiparallel* edges between `x` and `y` therefore passes the test,
although the underlying undirected multigraph has a doubled edge. Bondy's small
cycle double cover conjecture is false for multigraphs, and the `n - 1` bound
makes the gap exploitable:

*Counterexample.* The complete symmetric digraph on three vertices — vertex type
`option bool`, edge type `V * bool`, one arc per ordered pair. It is
`simple_mgraph` (one arc per ordered pair, loopless) and `bridgeless` (every arc
`u -> v` detours through the third vertex). With `#|G| = 3` the row demands a
`cdc` of at most `2` members; but `size L <= 2` plus the exact-count condition
`count (e \in C) L = 2` forces *every* edge into *every* member, so a member is
the whole edge set, whose degree at a vertex is `4` — not `0` or `2`, so it is
not a `is_circuit`. (The slower count: six edges covered twice need twelve
circuit slots, and no circuit of a three-vertex graph exceeds three edges, so
four members are needed.)

Committed as `meta/probe_hints/small_cycle_double_cover_statement.v`:
`Lemma refuted : ~ small_cycle_double_cover_statement.` — `Qed`,
`Print Assumptions` → *Closed under the global context*. By the probe's
convention this hint **must stop compiling** once the row is repaired
(`hint-stale-FIX-OK`).

Repair for bm-013: a genuinely simple carrier (an `sgraph`, or a `simple_mgraph`
that bounds `#|edges x y| + #|edges y x|`) **and** an undirected `bridgeless`.

### The six faithful rows

* **bm_011** (Barát–Thomassen). Back-translation: *for every nonempty tree `T`
  there is `k` such that every `k`-edge-connected simple graph whose edge count
  is divisible by `e(T)` has a list of edge sets, each the image edge set of an
  injective adjacency-preserving `T -> G`, covering every edge exactly once and
  no non-edge.* Matches `statement_text` clause for clause; the divisibility is
  the right way round (`#|E(T)| %| #|E(G)|`); "copy" as a non-induced subgraph
  isomorphic to `T` is the standard reading; the exact-count condition is
  simultaneously "covers" and "edge-disjoint". `k_edge_connected` is
  `GTBase.common`'s undirected `sgraph` notion, unaffected by blocker A. The
  degenerate `T = K_1` case (`e(T) = 0`, hence `e(G) = 0`, empty decomposition)
  is consistent. PASS.
* **bm_016** (linear arboricity). The equality reading is right (the source says
  "*has* linear arboricity ⌈(k+1)/2⌉"), and is encoded as achievability plus
  minimality. Adversarial checks: `x212_linear_arboricity_at_most` is upward
  closed (pad with an empty colour class), so "the minimum" is well defined;
  `'I_0` is empty while `{set G}` never is, so the encoded value is `>= 1` and
  the `k = 0` case gives `1 = ceil_div 1 2`; the guard `0 < #|G|` is load-bearing
  for exactly that reason; the colouring is total on `{set G}` but only its
  values on genuine edges enter `x212_edge_colour_rel`; "linear forest" =
  `is_forest` + `Delta <= 2` is a disjoint union of paths. PASS-WITH-NOTE: the
  encoded `la` differs from the classical one on exactly one family — edgeless
  graphs, where the classical linear arboricity is `0` and the encoded value is
  `1`. That is the *only* divergence (any graph with an edge has classical
  `la >= 1`), and it is what makes the `k = 0` instance come out true, whereas
  the source's formula `⌈(k+1)/2⌉ = 1` is literally false for the edgeless
  graph. So the encoding silently repairs a degenerate falsehood in the source
  sentence instead of guarding `1 <= k`; honestly documented in the doc block,
  but it is a (benign) mode-5 divergence and should be recorded as such.
* **bm_062** (Kotzig). The distinct-pairs reading is not merely convenient, it is
  *forced*: with `x = y` allowed, no `p` of size `k >= 3` can satisfy
  `uniq (x :: p)` and `last x p = x`, so the unique-path property would be
  unsatisfiable and the statement vacuously true (mode 1). The `1 < #|G|` guard
  is likewise load-bearing (on `#|G| <= 1` the property holds vacuously and the
  statement would be false). "Length `k`" = `size p = k` = `k` edges. PASS.
* **bm_064** (Smith). `ucycleb` on more than two vertices is the genuine-cycle
  convention; `k_connected G k` with `k >= 2` forces `#|G| >= 3` and a cycle, so
  the hypotheses are satisfiable (non-vacuous). `implications_X212.v` proves the
  body equivalent to the studies row `X10.smith_longest_cycles_r_connected_statement`
  — an independent-re-encoding cross-check in the sense of
  `FAITHFULNESS_CHECKS.md` §3. PASS.
* **bm_065** (Bondy, linear-length cycles in cubic graphs). `exists p q, 0 < p /\
  0 < q /\ ... p * #|G| <= q * size c` is `|c| >= (p/q) n`; every positive real
  constant can be lowered to a positive rational one, so the existential over
  rationals is equivalent to the source's existential over reals. Cyclic
  4-edge-connectivity by vertex bipartitions whose two sides both contain a cycle
  has the same minimum as the edge-set definition (given a cyclic edge cut `F`,
  the side decomposition gives a bipartition with `δ(S) ⊆ F`). `K_4` is in the
  class vacuously (no bipartition has cycles on both sides) and satisfies the
  conclusion. PASS.
* **bm_066** (Birmelé–Bondy–Reed). PASS-WITH-NOTE. "A set of `k` vertices" is
  read as "at most `k`", which is the form the row's own review records
  ("*a set of at most ℓ vertices meeting all cycles of length at least ℓ*") and
  which is the only sensible reading when `#|G| < k`. The added guard `3 <= k` is
  load-bearing: for `k <= 2` the hypothesis degenerates to "any two cycles meet",
  true in `K_5`, while no `<= 2` vertices meet all cycles of `K_5`. The guard
  makes the Rocq statement formally *weaker* than the literal corpus sentence —
  deliberately, because that sentence is false; noted in the doc block.

### Probes and grounding

* `vacuity_probe --wave X212` (re-run with a working switch, see the caveat):
  **8 probed, 1 FLAGGED** — `small_cycle_double_cover_statement`
  (`auto=T False, auto=F False, hint: settles`), i.e. the auto ladder closes
  neither polarity for any row and the only signal is the curated refutation
  above, exactly as intended for the blocked row.
  **Caveat:** `meta/vacuity_probe.py` hard-codes `SWITCH = "digraph"`, and no
  such opam switch exists on this machine (only `default`), so every `coqc` call
  it makes fails and *every* statement comes back "ok" regardless. The probe was
  re-run with `SWITCH` monkey-patched to `default` to obtain a real signal; the
  hard-coded switch is a ledger item (`make probe` is currently a no-op).
* `grounding_X212.v` machine-checks non-vacuity and guard-has-teeth for all eight
  rows and is `Print Assumptions`-clean. Note that its two multigraph witnesses
  (`U`, one vertex no edges; `G2p`, two parallel *co-oriented* edges) are exactly
  the degenerate corner that blocker A leaves in the hypothesis class — the
  grounding is consistent with the definitions but cannot detect their defect.
* `check_milestone.py X212 cycle-theory`: ACCEPTED.

### Ledger items

1. **`is_bridge`/`bridgeless` must use the undirected `uwalk`** —
   `cycle-theory/theories/foundations/connectivity.v`. Affects `bm-013`,
   `bm-026`, X228 `axv_2511_02892_06` (all now blocked) and, for a user decision,
   the committed `cycle_double_cover_statement` (U6), `five_flow_statement` (D1)
   and `cubic_bridgeless` (U10). Add a `faithfulness_mutation.py` canary once
   fixed.
2. **`U6.simple_mgraph` must bound `#|edges x y| + #|edges y x|`** (or the row
   must move to an `sgraph` carrier). The refutation hint is the fix-verification
   artifact.
3. `meta/vacuity_probe.py` `SWITCH = "digraph"` does not exist here; the probe
   silently passes everything. Make the switch configurable / fail loudly.
4. `x212_cycle`, `x212_cycle_vertices`, `x212_longest_cycle` duplicate
   `X10.v`/`U2.v` vocabulary — candidates for `base/theories/common.v` (WP4b).


## X228:cycle-theory — second-reader readback (2026-09-23)

Reader: Claude Opus 5 second reader, session 01P75Y6ikkgDyzUzzoef316Z
(distinct from `implemented_by`). Protocol: `magical-snacking-token.md`
"Faithfulness protocol", steps 2, 4 and 7.

### Scope

The single flow row of wave X228 in `cycle-theory`
(`cycle-theory/theories/conjectures/X228.v`, grounding `grounding_X228.v`,
implications `implications_X228.v`). The other X228 sub-waves
(`topological-graph-theory`, `infinite-graph-theory`, `minor-theory`) are other
readers'.

### Outcome

**0/1 PASS — the row FAILS and is now `blocked`.**

| row | statement | verdict |
|---|---|---|
| axv_2511_02892_06 | `half_flow_pair_statement` | **FAIL — wrong hypothesis** (blocked) |

### Readback

Back-translated from the body alone: *for every finite multigraph `G` with at
least one edge in which no edge is a bridge, there are integer edge weightings
`phi2`, `phi4` that are Kirchhoff-conservative at every vertex, with
`|phi2 e| <= 1` and `|phi4 e| <= 3`, such that `|phi4 e| >= 2` on every edge
where `phi2 e = 0`.* Compared with `statement_text` of `arxiv:2511.02892#06`
("Each bridgeless graph admits a 2-flow φ₂ and a 4-flow φ₄ such that for any
edge e, if φ₂(e)=0, then |φ₄(e)|≥2") and its `context_text`.

### What is faithful

* **`k`-flow with zeros allowed** (`x228_kflow`, deliberately weaker than
  `D1.has_nz_kflow`) is the right reading, and the source's own context confirms
  it arithmetically: with `|φ₂| <= 1` and `|φ₄| <= 3`, `5φ₂ + φ₄` has absolute
  value in `[2, 8]` — nowhere zero *precisely* because `|φ₄| >= 2` wherever
  `φ₂ = 0` — which is what makes `(5φ₂ + φ₄)/2` a circular 5-flow. A
  nowhere-zero reading of "2-flow" would make the compatibility clause vacuous
  and the conjecture trivially different.
* The bound `|phi e| <= (k.-1)%:R` is the standard `|φ| <= k - 1`.
* Orientations absorbed into the sign on the intrinsic source→target direction
  is the D1 convention and is orientation-invariant (reorienting an edge negates
  `φ` there, preserving conservation, the absolute value and the `= 0` test).
* The guard `0 < #|edge G|` is **inert** (an edgeless graph satisfies the
  conclusion with `φ = 0`), so it neither helps nor harms.

### What fails: the `bridgeless` hypothesis

Identical to blocker A of the X212 section above (see there for the two
readback-proved lemmas `bridgeless_outdeg2` / `bridgeless_indeg2`, `Qed`, closed
under the global context). `bridgeless` reads `is_bridge` through
coq-graph-theory's `eseparates`, which quantifies over the **directed** `walk`,
so it demands an alternative *directed* route `u -> ... -> v` for every arc
`u -> v`. Consequences:

* a simple carrier in the hypothesis class has minimum degree `>= 4`;
* a cubic loopless multigraph in it is a disjoint union of triple-edge dipoles.

So **no snark is in the hypothesis class** — while the source's entire evidence
for the conjecture is "verified computationally for all cyclically
4-edge-connected snarks up to 34 vertices", and its entire *point* is that it
implies the 5-flow conjecture, whose hard core is exactly the snarks. The
encoded statement retains the conjecture's *conclusion* while discarding the
graphs it is about: failure mode 4 (too weak / proxy), beyond what a
PASS-WITH-NOTE can carry.

The same defect also drains the corpus edge `e174` proved in
`implications_X228.v`: its target `five_flow_statement` (`D1.v`) carries the
identical restricted hypothesis, so the implication is a consistency check
between two equally-crippled statements, not evidence of faithfulness. (The
implication's explicit external hypothesis — an integer circulation with
`2 <= |χ| <= 8` yields a nowhere-zero 5-flow — is itself a fair denominator-free
rendering of the Goddyn–Tarsi–Zhang circular-to-integer step, and is *not* the
reason for the block.)

Repair: restate `is_bridge` with the **undirected** `uwalk` of `GTBase.base`
(`base.v:320-326`) and re-verify `five_flow_statement` and the rest of D1/U6/U10.

### Probes and grounding

* `vacuity_probe --files cycle-theory/theories/conjectures/X228.v`, re-run with
  `SWITCH` patched to `default` (see the switch caveat in the X212 section):
  **1 probed, 0 FLAGGED** — the auto ladder closes neither polarity. The row's
  defect is in its hypothesis, which no automation layer can see; it was found
  by readback, not by probing.
* `grounding_X228.v` is `Print Assumptions`-clean; like `grounding_X212.v`, its
  multigraph witnesses are the degenerate corner that survives the defective
  `bridgeless`, so the grounding is consistent with the definitions without
  being able to detect them.
* `check_milestone.py X228 cycle-theory`: ACCEPTED.

### Ledger items

1. Same as X212 item 1 (`is_bridge` must use `uwalk`); this row is the sharpest
   illustration, since the source names snarks explicitly.
2. When the foundation is repaired, `implications_X228.v` (edge `e174`) should be
   re-checked: the implication's proof may depend on the restricted hypothesis.


## X211 (hamiltonicity-theory) — second-reader readback (2026-09-23)

Reader: Claude Opus 5 second reader, session 01P75Y6ikkgDyzUzzoef316Z
(distinct from `implemented_by`). Protocol: `magical-snacking-token.md`
"Faithfulness protocol", steps 2, 3/4 and 7.

### Scope

The seven Bondy–Murty Hamiltonicity rows of wave X211
(`hamiltonicity-theory/theories/conjectures/X211.v`, grounding
`grounding_X211.v`, implications `implications_X211.v`).

### Outcome

**6/6 PASS on the rows that claim faithfulness; `bm-080` stays `blocked`
(verdict confirmed and sharpened). No row newly blocked.**

| row | statement | verdict |
|---|---|---|
| bm_079 | `matthews_sumner_four_connected_claw_free_statement` | PASS |
| bm_080 | `barnette_simple_four_polytope_hamiltonian_statement` | blocked (confirmed) |
| bm_085 | `cantoni_planar_cubic_three_hamilton_cycles_statement` | PASS |
| bm_088 | `thomassen_vertex_transitive_all_but_finitely_many_statement` | PASS-WITH-NOTE |
| bm_089 | `chvatal_toughness_hamiltonian_statement` | PASS-WITH-NOTE |
| bm_090 | `hypohamiltonian_minimum_degree_four_statement` | PASS-WITH-NOTE |
| bm_091 | `grotschel_no_bipartite_hypotraceable_statement` | PASS-WITH-NOTE |

### Readbacks

* **bm_079.** *Every finite simple graph that is 4-connected (more than four
  vertices, and removal of fewer than four leaves it connected) and has no
  induced `K_{1,3}` has a Hamilton cycle.* Matches `statement_text` exactly.
  `induced_free G 'K_1,3` is the INDUCED reading — the subgraph-containment
  reading would be a strictly stronger, wrong hypothesis. `k_connected G 4`
  forces `4 < #|G|`, so the documented digon convention (`hamiltonian 'K_2`
  holds) cannot cheapen the conclusion. PASS.
* **bm_080.** Correctly `blocked`, and the doc block, the wave note and the
  definition's own comment all say so loudly: the geometric hypothesis ("the
  graph of a simple 4-dimensional convex polytope") has no formalisation in
  coq-graph-theory 0.9.7 or GTBase, and the compiling placeholder
  `regular G 4 /\ k_connected G 4` is strictly weaker than it. **Sharpening
  found by this readback:** the placeholder is not merely over-strong, it is
  *false* — "every 4-regular 4-connected graph is Hamiltonian" is
  Nash-Williams' conjecture, refuted by the Meredith graph (70 vertices,
  4-regular, 4-connected, non-Hamiltonian). So the definition must never be
  promoted to `done`, and anyone who later builds the Meredith graph could
  commit `~ barnette_simple_four_polytope_hamiltonian_statement`, which
  `check_milestone.py`'s exact-type probe would then flag on a non-`disproved`
  row. A `Notes:` sentence recording this was added.
* **bm_085.** *Let `G` be planar (no `K_5` and no `K_{3,3}` minor) and cubic. If
  the set of edge sets of its Hamilton cycles has exactly three members, then
  `G` has three pairwise adjacent vertices.* Matches. Three adversarial checks:
  (i) identifying a Hamilton cycle with `{{x, next c x} : x ∈ c}` quotients
  exactly by rotation and reflection — the standard "3H graph" convention, and
  two seqs have the same edge set iff they describe the same cycle;
  (ii) ranging `c` over `(#|G|).-tuple G` loses no Hamilton cycle, because
  `hamiltonian_cycle` already forces `size c = #|G|`; (iii) `wagner_planar` is
  exactly planarity for simple graphs (Wagner), axiom-free and embedding-free,
  and the statement needs no embedding. The hypothesis class is inhabited:
  `K_4` is planar, cubic, has exactly three Hamilton cycles and contains a
  triangle. PASS.
* **bm_088.** *There is `n0` such that every connected vertex-transitive graph
  on at least `n0` vertices is Hamiltonian.* The threshold form is equivalent to
  "all but finitely many" over finite graphs (finitely many isomorphism types per
  order, Hamiltonicity iso-invariant), and vertex-transitivity via all
  automorphisms (rather than a group action) is the intended notion.
  PASS-WITH-NOTE: the digon convention makes `hamiltonian 'K_2` true, so the
  encoding recognises only four of the five known exceptions the `context_text`
  lists (`K_2`, Petersen, Coxeter and the two truncations). Inert here — any
  `n0 >= 3` absorbs it — but it would matter for a future row that *counts* or
  *names* the exceptions. Noted in the doc block.
* **bm_089.** *There is a positive integer `k` such that every graph on more
  than two vertices in which `k * c(G - S) <= |S|` for every `S` leaving at
  least two components is Hamiltonian.* The corpus `statement_text` itself says
  "positive integer `k`", so the integer reading is not an approximation; the
  rational form is anyway equivalent (round a rational `t0` up). The cleared
  form `k * c(G-S) <= |S|` over all `S` with `c(G-S) >= 2` is precisely
  "`|S| >= t·c(G-S)` for every vertex cut `S`". Adversarial checks: the
  statement does not collapse for large `k` (for `n >= 2k+2` non-complete
  `k`-tough graphs exist), and it is not settled (Bauer–Broersma–Veldman give
  `(9/4−ε)`-tough non-Hamiltonian graphs, so `k <= 2` fails and `k >= 3` is
  open — matching the review). PASS-WITH-NOTE: the `2 < #|G|` guard is an added
  hypothesis, load-bearing because `K_1` is vacuously `k`-tough for every `k`
  and is not Hamiltonian (`grounding_X211.tough_complete` /
  `chvatal_guard_has_teeth` machine-check exactly this).
* **bm_090.** *There is a graph in which every vertex has at least four
  neighbours, which has no Hamilton cycle, and all of whose vertex-deleted
  subgraphs have one.* The source is a **question**; rendering it as the
  existence statement it asks about is a judgement call, consistent with corpus
  practice, and the review confirms the row is open. Degenerate witnesses are
  excluded: the empty graph *is* Hamiltonian under `hamiltonian_cycle` (the
  empty seq is a `ucycle` of size `0 = #|G|`), so `~ hamiltonian G` rules it out,
  and minimum degree `>= 4` forces `4 < #|G|`, so no vertex-deleted subgraph is
  a digon. An independent brute force (this readback, not the implementer's) over
  *all* graphs on at most 7 vertices, with the Rocq semantics of `hamiltonian`
  (digon convention included) and of `induced ([set: G] :\ v)`, found **no**
  witness. PASS-WITH-NOTE (question-as-existence).
* **bm_091.** *No bipartite graph on more than two vertices has no Hamilton path
  while every vertex-deleted subgraph has one.* Matches. PASS-WITH-NOTE: the
  `2 < #|G|` guard is an added hypothesis and is load-bearing — the edgeless
  graph on two vertices is bipartite and literally hypotraceable (no Hamilton
  path; each one-vertex subgraph has one), machine-checked as
  `hypotraceable_edgeless2` / `grotschel_guard_has_teeth`. An independent brute
  force over all graphs on at most 7 vertices found **no other** bipartite
  hypotraceable graph, so the guard is exactly the source's implicit
  "nontrivial graph" assumption and not an over-restriction. (The smallest known
  hypotraceable graphs have 34 vertices, so the search cannot reach a real
  counterexample; it only confirms no further degenerate corner.)

### Probes and grounding

* `vacuity_probe --wave X211`, re-run with `SWITCH` patched to `default` (same
  switch caveat as in the X212 section — `SWITCH = "digraph"` does not exist on
  this machine, so the shipped probe silently passes everything):
  **7 probed, 0 FLAGGED**, auto ladder closes neither polarity on any row.
* `grounding_X211.v` is thorough and `Print Assumptions`-clean: non-vacuity
  witnesses (`K_5` for bm-079/090, `K_4` for bm-085, `K_n` for bm-088/089),
  guard-has-teeth lemmas for both added guards (`chvatal_guard_has_teeth`,
  `grotschel_guard_has_teeth`) and `hamilton_cycle_edge_sets_K1 = 0`.
* `check_milestone.py X211 hamiltonicity-theory`: ACCEPTED (16 forbidden shapes
  tested).
* `implications_X211.v` proves the easy direction of the confirmed corpus
  equivalence `gc:e234` (Matthews–Sumner ⟹ `opg:hamiltonian_cycles_in_line_graphs`)
  via the `Qed` lemma `line_graph_claw_free` — a genuine cross-check, not a
  trivial edge.

### Ledger items

1. `grounding_X211.ham_cycle_sets_K4_nonempty` only proves
   `0 < #|x211_hamilton_cycle_edge_sets 'K_4|`. The settled instance of bm-085 is
   `#|... 'K_4| = 3`; proving the equality would be a real "settled-case"
   anchor (`FAITHFULNESS_CHECKS.md` §2) for the edge-set counting convention,
   which is the row's main modelling choice.
2. `x211_graph_automorphism` / `x211_vertex_transitive` are byte-identical to
   `U2.graph_automorphism` / `U2.vertex_transitive`, and `x211_cycle_edges` to
   `U2.cycle_edges`; `x211_min_degree_geq` is the dual of base's `Delta`. All
   are flagged `@MOVE-to-base` in the file — WP4b/WP6 items.
3. The digon convention of `GTBase.common.hamiltonian` (`hamiltonian 'K_2`
   holds) disagrees with the standard literature on `K_2`. It is inert for every
   row of this wave, but it is a corpus-wide convention that should be stated in
   `base/theories/common.v`'s header and re-examined before any row that counts
   small non-Hamiltonian graphs.

## X213 (chromatic-theory, Bondy–Murty colouring rows) — second-reader readback (2026-09-23)

Reader: Claude Opus 5 second reader, session 01P75Y6ikkgDyzUzzoef316Z
(distinct from `implemented_by`). Protocol: `magical-snacking-token.md`
"Faithfulness protocol", steps 2, 3/4 and 7.

### Scope

The six Bondy–Murty Appendix-A colouring rows of wave X213
(`chromatic-theory/theories/conjectures/X213.v`, grounding `grounding_X213.v`,
implications `implications_X213.v`).

### Outcome

**5/6 PASS; `bm-053` newly `blocked` (the encoded hypothesis is the wrong
surface and the body is false on it).**

| row | formal name | verdict |
|---|---|---|
| bm_045 | `erdos_lovasz_tihany_statement` | PASS |
| bm_046 | `el_zahar_erdos_statement` | PASS |
| bm_050 | `triangle_free_induced_tree_chi_bounded_statement` | PASS-WITH-NOTE (infinite → finite) |
| bm_053 | `albertson_toroidal_delete_three_statement` | **FAIL → blocked** |
| bm_057 | `one_factorization_conjecture_statement` | PASS-WITH-NOTE (weaker of the two thresholds) |
| bm_060 | `vizing_kempe_interchange_statement` | PASS-WITH-NOTE (χ′ avoided by quantifying over every achievable `m`) |

### Readbacks

* **bm_045.** *If χ(G) = k, every clique of G has fewer than k vertices, and
  k + 1 = k₁ + k₂ with k₁, k₂ ≥ 2, then G has disjoint vertex sets A, B with
  χ(G[A]) = k₁ and χ(G[B]) = k₂.* Matches `statement_text`. Two checks: (i)
  "no k-clique" is `∀S, clique S → |S| < k`, i.e. ω(G) < χ(G), which also rules
  the hypothesis out for k ≤ 2 (a singleton, an edge) — the hypothesis block is
  inhabited from k = 3 (C₅), and `grounding_X213.x213_erdos_lovasz_tihany_guard_excludes_K3`
  machine-checks that the clique guard has teeth; (ii) the "exactly k_i on
  induced subgraphs" reading is equivalent to the source's "vertex-disjoint
  k_i-chromatic subgraphs" in both directions — an induced subgraph is a
  subgraph, and conversely χ drops by at most one per deleted vertex, so a
  subset of A with χ exactly k₁ exists and disjointness survives shrinking.
  Not covering V is also harmless (extend to a partition; χ only grows). PASS.
* **bm_046.** *There is f : ℕ → ℕ → ℕ such that every G with χ(G) ≥ f(r,k) has a
  clique of size exactly r, or two anticomplete sets each of chromatic number
  exactly k.* Matches. `x3_anticomplete A B` (disjoint, no A–B edge) is exactly
  "the induced subgraph on A ∪ B is the disjoint union of the two sides", and
  `χ = k` versus `χ ≥ k` is again equivalent by vertex deletion (a subset of an
  anticomplete set stays anticomplete). The function is quantified before
  r, k and G, which is the source's "does there exist a function f". Degenerate
  instances exist (r ≤ 1, or k = 0, where `set0`/`set0` settles the right
  disjunct) but are inert, and the statement as a whole is not vacuous: χ is
  unbounded over finite graphs, so the hypothesis is satisfiable for every f.
  PASS.
* **bm_050.** *For every finite tree T there is c with χ(G) ≤ c for every
  triangle-free G with no induced T.* The source quantifies over infinite graphs
  ("every triangle-free graph of infinite chromatic number contains every finite
  tree as an induced subgraph"); the finite form is equivalent in both
  directions — De Bruijn–Erdős upward, and downward by taking the disjoint union
  of finite counterexamples of unbounded χ, which is legitimate exactly because
  T is connected (`is_tree`), so an induced copy would live inside one
  component. The bound depends on T only. `implications_X213` proves the
  Gyárfás–Sumner row implies this one (Qed, `gc:e229`), the expected consistency
  signal. PASS-WITH-NOTE.
* **bm_053.** **FAIL.** Two independent defects in the single hypothesis
  `surface_embeddable 2 G`:
  1. **Wrong surface.** `surface_euler_genus` is `(2 + E − V − F) %/ 2`; by
     Euler's formula that is *g*, the ORIENTABLE GENUS, not the Euler genus
     (the torus has V − E + F = 0, so the numerator is 2 and the value is 1).
     `meta/STATEMENT_IMPROVEMENTS.md` already records for X164/X210 that
     `surface_euler_genus` computes the orientable genus. So
     `surface_embeddable 2` is "embeds in the genus-two orientable surface", a
     strictly larger class than "toroidal", and the body is **false** on it:
     K₈ has genus two (⌈(8−3)(8−4)/12⌉ = 2) and deleting any three of its
     vertices leaves K₅, of chromatic number five.
  2. **No connectivity guard.** The Euler characteristic is computed once for
     the whole graph, although `base/theories/surface.v` explicitly asks
     consumers to keep a connected guard. For c components of genera g_i the
     value is (2 − 2c + 2Σg_i)/2, so three disjoint copies of K₆ evaluate to 1
     and pass the hypothesis while needing genus three; three deletions leave a
     K₅ inside one copy.
  Faithful hypothesis: `surface_embeddable 1 G /\ connected [set: G]`. Row set
  to `blocked`; a `Notes:` sentence was added to the doc block. (The
  `Definitions:` clause of the block still describes `surface_embeddable 2` as
  "Euler genus at most two, i.e. the torus" — it must be corrected when the body
  is re-authored; this reader edits `Notes:` only.)
* **bm_057.** *Every d-regular simple graph on a positive even number n of
  vertices with n ≤ 2d is d-edge-colourable.* Matches `statement_text` exactly
  (`d ≥ n/2` cross-multiplied). PASS-WITH-NOTE: the `context_text` says the
  conjecture is *usually* stated with the sharper Chetwynd–Hilton threshold
  `d ≥ 2⌈n/4⌉ − 1`, which is a strictly stronger conjecture; the row encodes the
  weaker `n/2` form, and the doc block says so. Both guards have teeth: without
  `n ≤ 2d` the Petersen graph (3-regular, n = 10) refutes the body, and without
  the evenness guard K₅ does. The local edge-colouring predicate is a genuine
  proper edge colouring (symmetric, and distinct on two distinct edges sharing
  an endpoint), machine-checked non-vacuous on K₂ and refuted on K₃ with one
  colour.
* **bm_060.** *From every proper k-edge-colouring, for every achievable m ≤ k,
  a sequence of Kempe changes reaches a proper colouring using at most m
  colours.* Quantifying over every achievable m is equivalent to naming χ′(G),
  the least such m (the m = χ′ instance is the source; larger m follow). The
  Kempe step is taken on a line-adjacency-CLOSED set of {a,b}-coloured edges;
  closure at a vertex is all-or-nothing, so such a set is a union of components
  of the two-coloured subgraph, the swap of a union is the composition of the
  single-component swaps, and properness is automatically preserved at every
  intermediate colouring (no separate hypothesis needed). Reachability is a
  `nat`-indexed fixpoint with the number of steps existentially quantified.
  PASS-WITH-NOTE. Note that the row is corpus-`solved` (Narboni 2023), so a
  proof is legitimate future work rather than a red flag.

### Probes and grounding

* `vacuity_probe --wave X213`: 6 probed, 0 flagged — **but the first run was
  meaningless**: at the time `meta/vacuity_probe.py` hard-coded
  `SWITCH = "digraph"`, which does not exist in this environment, so every
  `coqc` call failed and every statement was reported `ok` (and every curated
  hint `stale-FIX-OK`). The figures above come from a copy with
  `SWITCH = "default"`; the harness was repaired by another agent later in the
  same session (`SWITCH = os.environ.get("ROCQ_OPAM_SWITCH", "")`), and the
  X219 numbers below were re-confirmed with the repaired script.
* `check_milestone.py X213 chromatic-theory`: ACCEPTED, 11/11, 6/6 axiom-free
  (re-run after the row was blocked).

## X218 (chromatic-theory, χ-boundedness / multibounding / clustered) — second-reader readback (2026-09-23)

Reader: Claude Opus 5 second reader, session 01P75Y6ikkgDyzUzzoef316Z.

### Scope

The six rows of wave X218 (`chromatic-theory/theories/conjectures/X218.v`,
`grounding_X218.v`, `implications_X218.v`), of which one was already `blocked`
by the implementer.

### Outcome

**5/5 PASS on the rows that claim a verification tuple; `arxiv:2308.15721#00`
stays `blocked`, with both blocked reasons confirmed against the paper and one
of them resolved (against the placeholder).**

| row | formal name | verdict |
|---|---|---|
| axv_2202_10412_00 | `every_forest_is_good_statement` | PASS-WITH-NOTE (normal form `c·ω^d`) |
| axv_2302_08922_00 | `path_induced_rooted_tree_polynomial_chi_bound_statement` | PASS |
| axv_2302_08922_01 | `polynomial_gyarfas_sumner_tree_statement` | PASS-WITH-NOTE (normal form) |
| axv_2303_11766_00 | `every_forest_is_multibounding_statement` | PASS |
| axv_2308_15721_00 | `odd_minor_free_defective_clustered_treedepth_statement` | blocked (confirmed + sharpened) |
| axv_2601_15245_04 | `kr_free_degenerate_fractional_chromatic_sublinear_statement` | PASS |

### Readbacks

* **axv_2202_10412_00 / axv_2302_08922_01.** *For every forest (resp. tree) H
  there are c, d with χ(G) ≤ c·ω(G)^d for every H-free G.* The shared
  `poly_chi_bounded` normal form is equivalent to "some polynomial": over ℕ a
  polynomial is dominated by (sum of coefficients)·t^d for t ≥ 1, and ω = 0 only
  for the empty graph, where χ = 0 ≤ c·0^d for d ≥ 1. Bounding data depend on H
  only. `implications_X218` proves the tree row implies U8's Gyárfás–Sumner and
  the forest row implies the multibounding row, both Qed — two independent
  consistency signals. PASS-WITH-NOTE (normal form is a documented modelling
  choice; note that X65's `arxiv:2202.05557#00` encodes the same mathematical
  conjecture with an explicit coefficient list, so the corpus now carries three
  near-duplicate encodings of "polynomial Gyárfás–Sumner").
* **axv_2302_08922_00.** Checked against the paper's own wording (arXiv
  abstract): "G contains a subgraph H isomorphic to T that is path-induced —
  for some distinguished vertex r, every path of H with one end at r is an
  induced path of G". `x218_path_induced_copy` is exactly that, clause for
  clause: `phi` injective and edge-preserving (a not necessarily induced
  subgraph copy), and the image of every `path (--) r p` with `uniq (r :: p)` is
  an `x218_induced_run`. The run predicate says no two entries at distance ≥ 2
  are adjacent, which together with the path and uniqueness gives "induced
  path"; its `nth` default (`phi r`, an element of the run) is only reachable at
  out-of-range indices, which the guard `i.+1 < j < size s` excludes. The root
  is universally quantified, as it must be for "for every rooted tree". Passing
  from "polynomial in the clique bound t" to the instance t = ω(G) is an
  equivalence because the bound is monotone in t. PASS.
* **axv_2303_11766_00.** *For every d ≥ 1 there are c, e with χ(G) ≤ c·t^e for
  every t ≥ 1 and every H-free G with no K_d(t) SUBGRAPH.* Matches the
  `context_text` clause for clause, including the quantifier order (d, then the
  polynomial, then t and G) and the guards d ≥ 1, t ≥ 1. `has_subgraph G H`
  unfolds to `subgraph H G` = an injective adjacency-preserving `H → G`, so
  K_d(t) is excluded as a subgraph and not as an induced subgraph, as the source
  requires; `x218_complete_multipartite d t` on `'I_d * 'I_t` with "parts
  differ" is K_d(t). PASS.
* **axv_2601_15245_04.** *For every r ≥ 4 and every q > 0 there is d₀ such that
  every d-degenerate G with ω(G) < r and d ≥ d₀ has χ_f(G) ≤ d/q.* The
  o_r(d) unfolding is faithful: the family {ε = 1/q} is cofinal in the positive
  reals and the condition is antitone in ε, so "for every q" is equivalent to
  "for every ε > 0"; the threshold depends on r and q only. K_r-free is ω < r
  (the same thing for a complete graph). `x130_frac_chi_le G d q` carries its own
  `0 < b` guard, and its attainedness caveat is documented in X130. PASS.
* **axv_2308_15721_00 (blocked).** Both blocked reasons confirmed, and the paper
  settles the second one **against** the placeholder: the paper defines the
  connected tree-depth as *"the minimum vertex-height of a rooted tree T with
  V(T) = V(G) such that G is a subgraph of the closure of T"* — the same vertex
  set, no new vertices — whereas `x218_connected_treedepth_at_most` allows any
  connected supergraph. Additionally, the current arXiv version states
  Conjecture 2 as "χ⋆(𝒢_H^odd) ≤ 2·td̄(H) − 2 **and** χ_Δ(𝒢_H^odd) = td̄(H) − 1",
  not as the single equality `χ_Δ = χ_⋆ = td̄(H) − 1` that the corpus
  `statement_text` records, so the corpus row itself needs re-checking against
  the paper version before the row is re-authored. The doc block says BLOCKED
  loudly and the placeholder cannot be mistaken for the conjecture. Blocked
  reason extended in the waves file and in the doc block's `Notes:`.

### Probes and grounding

* `vacuity_probe --wave X218` (patched switch): 6 probed, 0 flagged.
* `check_milestone.py X218 chromatic-theory`: ACCEPTED, 11/11, 6/6 axiom-free.

## X219 (chromatic-theory, list colouring / surfaces / planar degeneracy) — second-reader readback (2026-09-23)

Reader: Claude Opus 5 second reader, session 01P75Y6ikkgDyzUzzoef316Z.

### Scope

The seven rows of wave X219 (`chromatic-theory/theories/conjectures/X219.v`,
`grounding_X219.v`, `implications_X219.v`), of which one was already `blocked`.

### Outcome

**2/6 PASS. Four rows newly `blocked`, one of them with a committed,
machine-checked refutation; `arxiv:2407.18800#02` stays blocked (confirmed, and
a second defect found).** This is the weakest wave audited in this batch.

| row | formal name | verdict |
|---|---|---|
| axv_2407_18800_00 | `toroidal_five_choosability_critical_iff_six_critical_statement` | **FAIL → blocked** (wrong surface) |
| axv_2407_18800_01 | `toroidal_five_choosable_iff_five_colourable_statement` | **FAIL → blocked** (wrong surface + refutable) |
| axv_2407_18800_02 | `toroidal_edge_width_four_five_choosable_statement` | blocked (confirmed; 2nd defect) |
| axv_2004_07457_01 | `asymmetric_bipartite_list_colouring_statement` | **FAIL → blocked (REFUTED, Qed)** |
| axv_1902_07018_00 | `list_chromatic_index_even_clique_statement` | PASS-WITH-NOTE |
| axv_2009_12189_00 | `planar_fractional_vertex_arboricity_two_statement` | **FAIL → blocked** (∀b should be ∃b) |
| axv_1709_04036_01 | `triangle_free_planar_five_sixths_two_degenerate_statement` | PASS-WITH-NOTE |

### Readbacks

* **axv_2004_07457_01 — REFUTED.** Condition (ii) of the encoded Conjecture 7
  is `C * trunc_log 2 DB <= kA` and `C * trunc_log 2 DA <= kB`. At
  DA = DB = 1 both floors are 0, so for **every** C the hypotheses reduce to
  `0 <= kA`, `0 <= kB`, and the body claims that every bipartite graph of
  maximum degree one is (1,1)-choosable. `'K_2` with `A = [set ord0]`, palette
  `unit` and `L v = [set: unit]` refutes it. The witness is committed as
  `meta/probe_hints/asymmetric_bipartite_list_colouring_statement.v`
  (`Lemma refuted : ~ asymmetric_bipartite_list_colouring_statement`, `Print
  Assumptions` → closed under the global context), and the patched vacuity probe
  now reports `hint=settles` ⇒ FLAGGED. The paper's Conjecture 7 was fetched and
  inherits the same degenerate corner — its abstract says the conditions hold
  "provided Δ_A and Δ_B are large enough", so the repair is a guard (a Δ₀
  threshold as in condition (i), or `2 <= DA`, `2 <= DB` in (ii) and (iii)),
  documented as a modelling choice. Everything else on this row survived the
  readback: the three rearrangements were re-derived and are correct
  (`DA <= kA^q` for `kA ≥ DA^(1/q)`; and raising `kB ≥ C(D/log D)^(1/kA) log D`
  to the power kA gives `kB^kA ≥ C^kA · D · (log D)^(kA−1)`), naturalising the
  real constant C is harmless because the conditions are antitone in C, and
  flooring the logarithm is absorbed by C for D ≥ 2 — it is exactly D ≤ 1 that
  is fatal. Condition (iii) survives on its own (its C is existential and can be
  taken ≥ 2, which kills the D ≤ 1 corner); condition (i) is guarded by D₀.
* **axv_2009_12189_00 — the quantifier is wrong.** `x219_frac_vertex_arboricity_le_two`
  asks, **for every** b > 0, for 2b induced forests covering every vertex b
  times. The admissible b are closed under addition (union of two families), so
  "for every b" is equivalent to its b = 1 instance, i.e. to "V(G) splits into
  two induced forests" — the INTEGRAL vertex-arboricity being at most two. The
  source paper itself says "it is straightforward to show that planar graphs have
  vertex-arboricity at most three, and **there exist planar graphs with
  vertex-arboricity three**", so the body is false, and it is in any case
  strictly stronger than Conjecture 1.1. The faithful cleared form is the
  existential one the corpus already uses for fractional chromatic number
  (`X130.x130_frac_chi_le`): there EXISTS b ≥ 1 and 2b induced forests covering
  every vertex at least b times (the covering LP has rational data, so the
  optimum is attained). Fix = replace `forall b` by `exists b`. The rest of the
  row (Wagner planarity, `is_forest` on a vertex set = the induced subgraph is a
  forest) is fine.
* **axv_2407_18800_00 / _01 / _02 — "toroidal" is the wrong surface.**
  `surface_euler_genus` halves `2 + E − V − F`, so its value is the orientable
  genus: the torus is `surface_embeddable 1`, and `surface_embeddable 2` is the
  genus-two surface. All three rows use 2, so each asserts its conjecture for a
  strictly larger class than the source's "drawn on the torus". For row _01 this
  is not merely over-strong but **false**: the Euler characteristic is computed
  once for the whole graph with no connectivity guard, so padding any graph of
  genus g with g disjoint copies of K₂ drives the computed value to 0; taking a
  complete bipartite graph K_{m,m} whose choice number exceeds five yields a
  graph with χ = 2 that is not 5-choosable and satisfies `surface_embeddable 2`,
  refuting the biconditional. Row _00 is immune to the connectivity defect
  (criticality forces connectivity: if P fails on one component, deleting a
  vertex of another leaves P failing, so neither side of the ⇔ can hold on a
  disconnected graph) — its only defect is the surface index. The criticality
  machinery itself was checked against the paper and is faithful: the paper's
  "critical for 5-choosability" is "not 5-choosable but every proper subgraph
  is", the paper's "6-critical" is "inclusionwise minimal with χ ≥ 6", and for
  subgraph-monotone properties the two elementary deletions
  (`induced ([set: G] :\ v)`, `del_edges [set u; v]` — which removes exactly the
  edge uv) generate all proper subgraphs. Row _02's blocked reason is exact (the
  paper defines edge-width as the length of the shortest non-contractible cycle
  of the drawing, and girth ≥ 4 is strictly stronger); its blocked reason was
  extended with the surface-index defect so that both are fixed together.
* **axv_1902_07018_00.** *For every positive even n, K_n is (n−1)-edge-choosable.*
  The corpus row is the open question "is R_ℓ(K_{1,2},k) equal to k+1 or k+2 for
  odd k"; the row's own `context_text` states that this case is *equivalent* to
  the List Colouring Conjecture for cliques of even order, and the body is that
  determinate form. Stating only the upper bound is right (χ′_ℓ ≥ χ′ = n−1 is a
  theorem). `x219_edge_choosable` is a genuine list edge colouring: symmetric
  lists, symmetric colouring, a colour from each edge's own list, and distinct
  colours on two distinct edges sharing an endpoint. PASS-WITH-NOTE (the
  substitution of an asserted-equivalent statement for the source question is
  the modelling choice; it is recorded in the doc block).
* **axv_1709_04036_01.** *Every triangle-free planar G has S with 6|S| ≥ 5|V(G)|
  inducing a 2-degenerate subgraph.* The source is a methodological remark ("we
  believe the argument can be strengthened to give a bound 5/6"); the
  mathematical content extracted is α₂(G) ≥ 5n/6, which is precisely the 5/6
  weakening of the paper's Conjecture 1.1 (7/8, encoded in X32). The paper's
  proved bound is 4/5, so 5/6 is strictly between the theorem and the
  conjecture, as intended; `implications_X219` proves the 7/8 row implies this
  one (Qed). Cross-multiplication avoids `nat` division. PASS-WITH-NOTE
  (remark-as-proposition).

### Probes and grounding

* `vacuity_probe --wave X219` (patched switch): 7 probed, **1 FLAGGED**
  (`asymmetric_bipartite_list_colouring_statement`, `hint=settles`), which is
  the intended behaviour of the curated-witness layer: the hint must stop
  compiling once the row is repaired.
* `check_milestone.py X219 chromatic-theory`: ACCEPTED, 11/11, 7/7 axiom-free
  (blocking rows does not disturb the gate; the exact-type probes stay green
  because the refutation lives in `meta/probe_hints/`, outside `theories/`).
* Grounding gaps worth recording: `grounding_X219` proves
  `x219_frac_va_sunit`/`x219_frac_va_covers`, neither of which exercises b = 1
  on a graph with edges — which is exactly where the arboricity row breaks; and
  `x219_toroidal_guard_K1` only witnesses that the toroidal guard is
  *satisfiable*, never that it excludes anything, which is why the surface-index
  defect survived the implementer's own net.

### Notes for the improvement ledger (X213 / X218 / X219)

- **`surface_embeddable <n>` is the ORIENTABLE GENUS, not the Euler genus.**
  Every row that names a concrete surface must use `1` for the torus, not `2`.
  Four rows in this batch got it wrong (bm-053, `arxiv:2407.18800#00/#01/#02`);
  the existing rows that quantify over all surfaces are unaffected. The
  primitive's name is the trap: `surface_euler_genus` divides by two. Rename it
  (`surface_orientable_genus`), or add a `surface_euler_genus_is_twice` comment
  plus a sanity lemma (`surface_embeddable 0 'K_5 → False` would be the ideal
  canary), and give `base/theories/surface.v` a `toroidal` abbreviation so no
  row has to pick a number.
- **The missing connected guard is now a corpus-wide pattern** (the X228 reader
  flagged the same thing). `surface_euler_genus` computes `(2 + E − V − F) %/ 2`
  once for the whole graph, so for c components the value is
  `(2 − 2c + 2Σg_i)/2` and *any* graph can be padded with disjoint planar
  components until it passes. That is strong enough to refute statements, not
  just weaken them (row `arxiv:2407.18800#01` above). Either bake
  `connected [set: G]` into a `toroidal`/`surface_embeddable` wrapper, or make
  the wave template require the guard for every embedding row.
- **Fractional parameters must be existential in the denominator.** X130's
  `x130_frac_chi_le` (∃ a b) is right; X219's `x219_frac_vertex_arboricity_le_two`
  (∀ b) is wrong and collapses to the integral parameter. A shared
  `frac_cover_le` in `base/theories/common.v`, used by both, would have
  prevented this; it is a concrete WP4b/WP6 item.
- **Asymptotic conditions transcribed literally inherit the source's degenerate
  corners.** Conjecture 7 of `arxiv:2004.07457` is refutable at Δ = 1 in the
  paper too. Whenever a source condition involves `log Δ`, `Δ^ε` or `o(d)`, the
  encoding needs an explicit threshold guard, documented as a modelling choice —
  the same lesson as U4's `t = 0`. Worth a checklist line in the wave template
  and a `faithfulness_mutation.py` canary (drop the `2 <= D` guard, expect the
  probe hint to compile).
- **`meta/vacuity_probe.py` was inert in this environment** (hard-coded
  `SWITCH = "digraph"`, an opam switch that does not exist here, so every `coqc`
  call failed, every statement was reported `ok` and every curated hint
  `stale-FIX-OK` — a silently green probe; the X228 reader reported the same
  symptom). **Fixed during this session** by another agent
  (`SWITCH = os.environ.get("ROCQ_OPAM_SWITCH", "")`), and the X219 run was
  re-confirmed against the repaired script. Remaining item: the probe should
  still ABORT when a toolchain call fails for a reason other than a Rocq error,
  otherwise the same class of silent green can come back.
- **Duplicated vocabulary.** (i) "Polynomially χ-bounded" now exists three
  times: `chi_bounding.poly_chi_bounded` (X218, two rows), X65's coefficient-list
  encoding of the same conjecture, and `x3_polynomially_chi_bounded`/
  `x124_poly_chi_bounded` already on the ledger — X218's two rows and X65's row
  are the *same* mathematical statement for two different papers, which is worth
  an `implications` equivalence rather than three parallel encodings.
  (ii) `x213_proper_edge_colouring`/`x213_edge_colourable` and
  `x219_edge_choosable` are the simple-graph edge-colouring pair that
  `base`'s multigraph `chromatic_index` cannot serve; they belong together in
  `common.v` (with `x219_edge_choosable` refining the X213 predicate), and
  `x219_bipartition` duplicates `common.complete_bipartite`'s side condition.
  (iii) `x218_connected_treedepth_at_most` should be replaced by the paper's
  own definition (rooted tree on the same vertex set) when the odd-minor row is
  re-authored.
- **Settled cases not yet machine-checked.** bm-060 is corpus-`solved`
  (Narboni 2023) and bm-057 is proved for all large n, but neither wave carries
  a settled-case artifact; `x219_edge_choosable_K2` (the n = 2 instance of the
  even-clique row) is the only one in the batch. The Kempe vocabulary of X213
  would support a real settled case (every proper 2-edge-colouring of a path
  reaches a χ′-colouring), which would also exercise `x213_kempe_reach` beyond
  reflexivity.

### Appendix (X215 / X223 / X229 / X195 / X196) — active probe results, 2026-09-23

`meta/vacuity_probe.py` is unusable on this checkout (it hard-codes the missing opam switch
`digraph`, so every compile fails and every statement is reported `ok`; see the X215 ledger
note). The reader therefore re-ran the probe's own tactic ladder with plain `coqc` against
the `default` switch, on both polarities of all 14 statements of these waves:

```
erdos_sos_tree_embedding_statement                        auto_true=False auto_false=False
even_cycle_turan_lower_bound_statement                    auto_true=False auto_false=False
constructive_diagonal_ramsey_lower_bound_statement        auto_true=False auto_false=False   <- but see the curated hint
diagonal_ramsey_root_limit_statement                      auto_true=False auto_false=False
burr_erdos_tree_ramsey_statement                          auto_true=False auto_false=False
directed_sidorenko_bipartite_statement                    auto_true=False auto_false=False
directed_forcing_cyclic_statement                         auto_true=False auto_false=False
triangle_free_eps_bounded_anticomplete_pair_statement     auto_true=False auto_false=False
h_free_eps_bounded_sparse_pair_statement                  auto_true=False auto_false=False
vc_dimension_erdos_hajnal_statement                       auto_true=False auto_false=False
induced_turan_even_cycle_sparse_statement                 auto_true=False auto_false=False
expander_proper_colouring_two_connected_palettes_statement auto_true=False auto_false=False
ramsey_nice_forest_family_eventual_statement              auto_true=False auto_false=False
ramsey_nice_forest_family_infinite_statement              auto_true=False auto_false=False
```

Layer 2 (curated witness): `meta/probe_hints/constructive_diagonal_ramsey_lower_bound_statement.v`
compiles and reports `Closed under the global context`, settling
`constructive_diagonal_ramsey_lower_bound_statement` in the negative. This is exactly the
recall gap the hint layer exists for: the generic ladder cannot find the k = 1, N = 1
instantiation, and `check_milestone`'s exact-type probes only reject *committed*
refutations, not refutable statements. Once (if) that placeholder is repaired, the hint
must stop compiling (`hint-stale-FIX-OK`).


## Re-read after the bridgeless/simple_mgraph repair (2026-09-23)

Reader: Claude Opus 5 second reader, session 01P75Y6ikkgDyzUzzoef316Z. Second
pass over the six rows whose MEANING changed when
`cycle-theory/theories/foundations/connectivity.v` and `U6.simple_mgraph` were
repaired. **No statement body changed**; every verdict below comes from
back-translating the unchanged body against the *new* definitions.

### What the repair actually says

```coq
(* connectivity.v *)
Definition ueseparates (G : mgraph) (x y : G) (E : {set edge G}) : Prop :=
  forall w : seq (edge G), uwalk x y w -> exists2 f, f \in E & f \in w.
Definition is_bridge (G : mgraph) (e : edge G) : Prop :=
  ueseparates (source e) (target e) [set e].
(* U6.v *)
Definition simple_mgraph (G : mgraph) : Prop :=
  loopless G /\ forall x y : G, (#|edges x y| + #|edges y x| <= 1)%N.
```

Back-translated independently: `is_bridge e` = *every **undirected** walk
between the ends of `e` uses `e`* = *`e` is a cut edge* (its removal separates
its ends). `bridgeless` = *no cut edge*. ✔ `simple_mgraph` = loopless, and for
every ordered pair the **total** number of arcs in both directions is ≤ 1, i.e.
at most one edge between any two vertices, undirectedly. ✔ (At `x = y` the bound
reads `2·#|edges x x| ≤ 1`, i.e. no loop, consistent with `loopless`.) Both
notions now match the textbook ones, and the grounding teeth lemmas
(`x212_bridgeless_Tri`, `x212_not_bridgeless_G1`, `x212_not_simple_Gd`,
`x212_small_cdc_hypotheses_Tri`) check exactly the right corners. The earlier
`bridgeless_outdeg2`/`bridgeless_indeg2` pathology is gone.

### Verdicts

| row | statement | before | after |
|---|---|---|---|
| bm_013 | `small_cycle_double_cover_statement` (X212) | FAIL, blocked | **PASS — unblocked** |
| bm_026 | `orientable_five_cycle_double_cover_statement` (X212) | FAIL, blocked | **FAIL — stays blocked (new, independent reason)** |
| axv_2511_02892_06 | `half_flow_pair_statement` (X228) | FAIL, blocked | **PASS — unblocked** |
| — | `cycle_double_cover_statement` (U6, OPG, leg `done`) | inherited caveat | **FAIL — newly found refutable** (audit-only) |
| — | `five_flow_statement` (D1, OPG, leg `done`) | inherited caveat | **PASS** (audit-only) |
| — | `the_berge_fulkerson_statement`, `petersen_coloring_statement`, `intersecting_two_perfect_matchings_statement` (U10, OPG, `cubic_bridgeless`) | inherited caveat | **PASS** (audit-only) |

### A SECOND, independent defect: `subdeg` counts a loop once

`connectivity.mdeg v = #|edges_at v|` and
`connectivity.subdeg H v = #|edges_at v :&: H|` count the edges **incident** to
`v`, so a **loop contributes 1, not 2**. In every standard convention a loop
contributes 2 — which is exactly what makes a loop a cycle: a single loop is an
element of the cycle space and a circuit of length 1. Under the encoding it is
neither: `U6.even_subgraph [set e]` fails (`subdeg = 1` is odd) and
`U6.is_circuit [set e]` fails (`subgraph_kregular … 2` wants 0 or 2).

The one-vertex, one-loop multigraph `Lp := mgraph.add_edge (unit_graph tt) tt tt tt`
is `mconnected` and `bridgeless` (a loop is never a cut edge —
`connectivity.loop_not_bridge`), hence `two_edge_connected`. Its single edge
must be covered, and every candidate member equals `[set: edge Lp]`, whose
`subdeg` at the vertex is 1. Therefore:

* **bm_026 is refutable.** `Lemma refuted_orientable5 : ~ orientable_five_cycle_double_cover_statement.`
  — `Qed`, *Closed under the global context*, committed as
  `meta/probe_hints/orientable_five_cycle_double_cover_statement.v`. The row
  **stays blocked**; its `blocked_reason` in `meta/v2_statement_waves.json` was
  replaced with this one (the bridgeless reason is obsolete).
* **`cycle_double_cover_statement` (U6) is refutable by the same graph**, through
  `is_circuit` instead of `even_subgraph`. Recorded here only, per instructions —
  it is a committed OPG row with statement leg `done`:

```coq
Lemma refuted_cdc : ~ cycle_double_cover_statement.
Proof.
move=> H.
have v1 : (0 < #|Lp|)%N by rewrite card_Lp.
have e1 : (0 < #|edge Lp|)%N by rewrite card_edge_Lp.
have [L [circ cnt]] := H Lp v1 e1 bridgeless_Lp.
have : 0 < count (fun C : {set edge Lp} => (None : edge Lp) \in C) L by rewrite cnt.
rewrite -has_count => /hasP[C CL hC].
have [_ reg _] := circ C CL.
by have := reg tt; rewrite (subdeg_C_Lp hC); case.
Qed.
(* Print Assumptions refuted_cdc.  ->  Closed under the global context *)
```

Both conjectures plainly **hold** on `Lp` (cover the loop twice), so this is
failure mode 2 (refutable), not a true negative. The exact-type probe of
`check_milestone.py` cannot see it, because no refutation is *committed* in the
package.

**Rows guarded by `loopless` are NOT affected**: `small_cycle_double_cover_statement`
(via `simple_mgraph`), the three `U10` rows (via `cubic`). Flow rows are not
affected either: on `Lp` the loop sits on **both** sides of Kirchhoff, so every
weighting is `iconservative`.

**Repair options** (foundation, not mine to make): make `mdeg`/`subdeg` count a
loop twice — the textbook degree, which would also make `is_circuit` accept a
loop and `cubic` unchanged — or add an explicit `loopless` hypothesis to
`cycle_double_cover_statement` and `orientable_five_cycle_double_cover_statement`.
The first is preferable: it fixes the *notion* rather than narrowing the rows,
and `even_subgraph`/`is_circuit`/`two_factor`/`is_matching` all inherit it.

### Row-by-row re-readback

* **bm_013 `small_cycle_double_cover_statement` — PASS, unblock.**
  *Every loopless multigraph with at least one vertex in which any two vertices
  are joined by at most one edge and no edge is a cut edge has a list of
  circuits covering every edge exactly twice, with at most n−1 members.*
  Matches `statement_text` ("Every simple graph on n vertices without cut edges
  has a cycle double cover consisting of at most n−1 cycles") clause for clause.
  The refutation hint `meta/probe_hints/small_cycle_double_cover_statement.v` no
  longer compiles (`stale-FIX-OK`) — verified directly. Adversarial re-checks:
  `n = 1` (loopless + simple ⇒ edgeless, empty cover, bound 0 ✔); `n = 2` (a
  single edge is a cut edge, so bridgeless forces edgeless ✔); disconnected
  carriers are fine (Σ(nᵢ−1) = n−c ≤ n−1); `K_4` is a settled instance (its three
  4-cycles are a CDC of size 3 = n−1). Non-vacuous with a genuine graph:
  `x212_small_cdc_hypotheses_Tri`.
* **bm_026 `orientable_five_cycle_double_cover_statement` — FAIL, stays blocked.**
  The hypothesis is now exactly 2-edge-connectivity and the class contains every
  cubic graph, the Petersen graph and every snark — the repair did its job. The
  orientability encoding (balanced orientation per member, opposite directions on
  the two covering members) was already verified against `context_text` and is
  still orientation-invariant. But the loop defect above refutes it.
* **axv_2511_02892_06 `half_flow_pair_statement` — PASS, unblock.**
  *Every multigraph with at least one edge and no cut edge carries a
  Kirchhoff-conservative integer weighting of absolute value ≤ 1 and one of
  absolute value ≤ 3 such that the second has absolute value ≥ 2 wherever the
  first vanishes.* Matches Conjecture 6.1. The flow content was already
  faithful; the hypothesis now is. Snarks are back in the class, which is what
  the source's computational evidence and the implication to the 5-flow
  conjecture are about, so the `e174` edge in `implications_X228.v` is now
  between two correctly-scoped statements. Not vacuous: `φ₂ ≡ 0` only works when
  the graph carries a conservative flow with all values in ±{2,3}, which is not
  automatic (e.g. it forces evenness when one tries `2φ` for a 2-flow `φ`).
* **`cycle_double_cover_statement` (U6) — FAIL, newly found.** See above. Apart
  from the loop defect the body reads correctly against the OPG text: *every
  bridgeless multigraph with at least one vertex and one edge has a list of
  circuits covering every edge exactly twice.*
* **`five_flow_statement` (D1) — PASS.** *Every multigraph with at least one edge
  and no cut edge has a nowhere-zero 5-flow* (`iconservative` + `1 ≤ |φ| ≤ 4`).
  This is Tutte's conjecture, and the hypothesis class is now the right one
  (previously it excluded every snark, i.e. the whole hard core). Loops are
  harmless here, as shown. `iconservative` is the correct Kirchhoff law
  (out-sum = in-sum, loop cancels).
* **U10 `cubic_bridgeless` rows — PASS.** `cubic_bridgeless = cubic ∧ bridgeless`
  with `cubic = loopless ∧ ∀v, mdeg v = 3` now denotes exactly *loopless
  3-regular multigraph with no cut edge* — the textbook bridgeless-cubic class
  (`K_4`, `K_{3,3}`, Petersen, every snark, the triple dipole). Under the old
  reading this class collapsed to **disjoint unions of triple-edge dipoles
  only**, so Berge–Fulkerson, Petersen colouring and Fan–Raspaud were all
  near-vacuous; that is now fixed. Their conclusions use perfect matchings,
  line-graph adjacency and odd edge cuts — no `is_circuit`/`even_subgraph` — so
  the loop defect cannot reach them, and `cubic` forces looplessness anyway.

### Ledger items (supersede items 1–2 of the X212 section)

1. **CLOSED**: `is_bridge`/`bridgeless` now use the undirected `uwalk`;
   `U6.simple_mgraph` now bounds the undirected multiplicity. Both have teeth
   lemmas in `grounding_X212.v`. The `small_cycle_double_cover_statement` hint is
   stale, as designed.
2. **OPEN, new**: `connectivity.mdeg`/`subdeg` give a loop degree 1. Fix to 2
   (textbook) and re-verify `even_subgraph`, `is_circuit`, `two_factor`,
   `is_matching`, `subgraph_kregular` and every row built on them. Until then
   `orientable_five_cycle_double_cover_statement` is blocked and
   `cycle_double_cover_statement` (committed, `done`) is refutable — **a user
   decision**. Add a `faithfulness_mutation.py` canary for the loop convention
   once fixed.

### Probe output (re-read)

`python3 meta/vacuity_probe.py --names small_cycle_double_cover_statement,orientable_five_cycle_double_cover_statement,half_flow_pair_statement,cycle_double_cover_statement,five_flow_statement,the_berge_fulkerson_statement,petersen_coloring_statement,intersecting_two_perfect_matchings_statement`
(the probe is now switch-aware and uses the `coqc` on PATH — the
`SWITCH = "digraph"` ledger item is closed):

```
statement                                            auto=T auto=F hint           verdict
orientable_five_cycle_double_cover_statement         False  False  settles        *** FLAGGED ***
cycle_double_cover_statement                         False  False  none           ok
five_flow_statement                                  False  False  none           ok
half_flow_pair_statement                             False  False  none           ok
intersecting_two_perfect_matchings_statement         False  False  none           ok
petersen_coloring_statement                          False  False  none           ok
small_cycle_double_cover_statement                   False  False  stale-FIX-OK   ok
the_berge_fulkerson_statement                        False  False  none           ok
8 probed · 1 FLAGGED
```

`small_cycle_double_cover_statement` reports **`stale-FIX-OK`** — the repair is
verified by the very artifact that refuted the row. The single flag is the new
`orientable_five_cycle_double_cover_statement` hint.

**Read the `ok` on `cycle_double_cover_statement` as "not probed", not as
"clean":** the auto ladder cannot find the one-vertex one-loop counterexample,
and per instructions no hint was committed for that OPG row. The refutation
above is real and reproducible from the snippet; if the user wants it enforced,
drop the same `Lp` construction into
`meta/probe_hints/cycle_double_cover_statement.v` and the probe will flag it.

## Re-read of the five repaired chromatic rows (2026-09-23)

Reader: Claude Opus 5 second reader (faithfulness auditor), session
01P75Y6ikkgDyzUzzoef316Z. This is the **re-read after the 2026-09-23 fix
pass**, not a new first reading: each row below was `blocked` by the readbacks
recorded above, repaired by the fix agent, and left `awaiting second-reader
re-read`.

### Scope

Five rows, all in `chromatic-theory`:

| row | formal name | repair under review |
|---|---|---|
| `X213` / `bm_053` | `albertson_toroidal_delete_three_statement` | `surface_embeddable 1 G -> connected [set: G] ->` (was `surface_embeddable 2`, unguarded) |
| `X219` / `axv_2407_18800_00` | `toroidal_five_choosability_critical_iff_six_critical_statement` | same torus repair |
| `X219` / `axv_2407_18800_01` | `toroidal_five_choosable_iff_five_colourable_statement` | same torus repair |
| `X219` / `axv_2009_12189_00` | `planar_fractional_vertex_arboricity_two_statement` | fold parameter `b` made EXISTENTIAL |
| `X219` / `axv_2004_07457_01` | `asymmetric_bipartite_list_colouring_statement` | existential `D0 > 1` degree threshold in (ii) and (iii) |

### Outcome

**5/5 accepted: 2 PASS, 3 PASS-WITH-NOTE. No row goes back to `blocked`; no new
refutation was found.**

| row | verdict | decisive reason |
|---|---|---|
| bm_053 | PASS-WITH-NOTE | the guard is now exactly "toroidal" for connected graphs, and the connectivity restriction loses no mathematical content |
| axv_2407_18800_00 | PASS | surface index correct; the connectivity guard is provably inert (criticality forces connectivity) |
| axv_2407_18800_01 | PASS-WITH-NOTE | padding refutation dead; connectivity restriction is componentwise harmless |
| axv_2009_12189_00 | PASS | `exists b` is the attained-LP form, and the repair did not trivialise it (`~ … 'K_5` machine-checked) |
| axv_2004_07457_01 | PASS-WITH-NOTE | the guards provably force `2 <= kA`, `2 <= kB`; the encoded (ii)/(iii) are the paper's asymptotic, not literal, content |

### What `surface_embeddable` actually means (checked, not assumed)

`base/theories/surface.v` was re-derived line by line before any row was judged.

* A `surface_dart` is an ordered adjacent pair, so `#|dart| = 2E` and
  `surface_embedding_edges = #|dart| %/ 2 = E` exactly (simple graph, no loops).
* `surface_erot_vertex` forces the rotation to be a **single cycle on the darts
  out of each vertex**, i.e. a genuine rotation system; such a permutation
  exists for every finite graph, so `surface_embedding` is inhabited for every
  `G` and `surface_embeddable g G` is never empty for trivial reasons.
* `surface_embedding_vertices = #|porbits erot|` counts **only the vertices that
  carry a dart**: isolated vertices are invisible to the count.
* `surface_face_perm = erot * edge_perm` (mathcomp's `(f*g) x = g (f x)`), the
  standard face tracing, so `F` is the face count of the orientable embedding
  the rotation system describes.
* Therefore `surface_euler_genus = (2 + E − V − F) %/ 2` is the **orientable
  genus** of that embedding. For a **connected** graph with at least two
  vertices, `V` is the true vertex count, Euler gives `2 + E − V − F = 2g` with
  `g ≥ 0` an integer, so the `nat` subtraction never truncates and the `%/ 2` is
  exact; minimising over rotation systems gives the orientable genus of `G`
  (Duke's interpolation theorem makes the attained set an interval starting at
  it). **`surface_embeddable 1 G /\ connected [set: G]` is exactly "G is
  toroidal".** This is the single fact all three surface rows rest on.
* **Isolated-vertex wrinkle (new, machine-checked).** Because `V` skips
  dartless vertices, an **edgeless** graph gets `V = F = E = 0` and computed
  genus `(2+0−0−0)/2 = 1`. The reader proved
  `~ surface_embeddable 0 'K_1` (Qed, `Print Assumptions` → closed under the
  global context). Consequences: (a) at index 1 this is harmless — `K_1` is
  toroidal, so no false positive, and every connected graph with ≥ 2 vertices is
  unaffected; (b) `surface_embeddable 0` is **not** planarity and must never be
  used as such (it fails on `K_1`); (c) the only machine-checked inhabitant of
  the repaired toroidal guard, `x213_toroidal_guard_K1`, is accepted through
  this wrinkle rather than through a real embedding — see the grounding gaps
  below.
* "Does the source's *toroidal* include disconnected graphs?" **Decided: it does
  not matter, and the guard is right.** Under the standard convention the genus
  of a disconnected graph is the sum of its component genera
  (Battle–Harary–Kodama–Youngs), so a disconnected toroidal graph is one
  genus-≤1 component plus planar components. All three conclusions
  (χ after ≤ 3 deletions, 5-choosability, χ ≤ 5) are componentwise, so the
  connected case implies the disconnected one — using the Four Colour Theorem
  for bm-053 and Thomassen's 5-choosability of planar graphs for _01, both
  theorems. Conversely the guard is **indispensable**, because GTBase's count
  applies one Euler formula to the whole graph: for `c` components of genera
  `g_i` it returns `1 − c + Σ g_i`.

### Readbacks

* **bm_053 — `albertson_toroidal_delete_three_statement`. PASS-WITH-NOTE.**
  Back-translation (body first, doc block after): *for every finite simple graph
  `G` that carries a rotation system of computed orientable genus at most one
  and is connected, there is a vertex set `S` with `#|S| ≤ 3` and
  `χ(V(G) \ S) ≤ 4`.* Corpus `statement_text`: "Every toroidal graph has three
  vertices whose deletion leaves a 4-colourable graph"; the local review
  `graph-conjectures/data/bondy_murty_reviews/bm-053.json` spells it "every
  toroidal graph can be made 4-colourable by deleting **at most** three
  vertices", which is `#|S| ≤ 3` and not `#|S| = 3` — the encoding is the right
  one (and `= 3` would be unsatisfiable for graphs on fewer than three
  vertices). `χ([set: G] :\: S)` is the chromatic number of the induced
  subgraph on the complement of `S`, as required. The `Definitions:` clause now
  names the right notion ("rotation system of ORIENTABLE genus at most one") and
  the `Notes:` arithmetic was re-checked: γ(K₈) = ⌈(8−3)(8−4)/12⌉ = 2 and
  deleting three of its vertices leaves K₅ with χ = 5, so the old
  `surface_embeddable 2` body was indeed false; three disjoint copies of K₆
  evaluate to `1 − 3 + 3 = 1` and passed the old hypothesis.
  **The note.** The added `connected` is a restriction the source does not make
  (Albertson asks about every graph embeddable on S₁); it is harmless
  mathematically (see above) but it does mean the Rocq body is formally weaker
  than the corpus sentence, and that should stay visible in the doc block — it
  is.
  **Grounding gap (not a defect).** `x213_connected_guard_has_teeth` exhibits
  only the two-vertex edgeless graph, which is toroidal anyway, so it shows the
  guard *excludes something* but not that the unguarded body is *false*. The
  decisive witness is **two disjoint copies of K₇**: each has a genus-1
  embedding (V=7, E=21, F=14), so the union gives `2 + 42 − 14 − 28 = 2`,
  computed genus 1, while any three deletions leave a complete graph on at least
  six vertices, χ ≥ 6 > 4. It is not machine-checkable here because no genus-one
  rotation system for K₇ exists in the development.
* **axv_2407_18800_00 — `toroidal_five_choosability_critical_iff_six_critical_statement`. PASS.**
  Back-translation: *for every connected graph of computed orientable genus ≤ 1,
  `G` is critical for 5-choosability iff `G` is critical for "χ ≤ 5"*, where
  critical means the property fails on `G` but holds on `induced ([set: G] :\ v)`
  for every `v` and on `del_edges [set u; v]` for every edge `uv`. Corpus: "A
  graph drawn on the torus is critical for 5-choosability if and only if it is
  6-critical." Criticality for "χ ≤ 5" is 6-criticality: χ(G) > 5 while every
  one-vertex deletion has χ ≤ 5 forces χ(G) = 6, since deleting a vertex lowers
  χ by at most one. Both properties are subgraph-monotone, so the two elementary
  deletions generate all proper subgraphs and the encoding matches the paper's
  "every proper subgraph". `del_edges [set u; v]` removes exactly the edge `uv`
  (the hypothesis `u -- v` gives `u ≠ v`).
  **The connectivity guard is provably inert here**, which is why this row is a
  clean PASS: both properties hold on a disjoint union iff they hold on every
  component, so if the property fails on `G` it fails on some component, and
  deleting a vertex of another component leaves it failing — a critical graph is
  connected. The guard is kept only so that every embedding row of the wave
  reads the same way, as the doc block says.
* **axv_2407_18800_01 — `toroidal_five_choosable_iff_five_colourable_statement`. PASS-WITH-NOTE.**
  Back-translation: *for every connected graph of computed orientable genus ≤ 1,
  `G` is 5-choosable iff χ(G) ≤ 5.* Corpus: "A toroidal graph is 5-choosable if
  and only if it is 5-colorable." Exact match modulo the connectivity
  restriction, which is again componentwise harmless (both sides of the
  biconditional are componentwise, and planar components are 5-choosable by
  Thomassen and 5-colourable). The previous reader's refutation is dead: it
  padded a high-choice-number `K_{m,m}` with disjoint copies of `K_2`, and a
  padded graph is disconnected. **No connected refutation exists**, because for
  a connected graph the computed value *is* the orientable genus, and
  `K_{m,m}` has genus ⌈(m−2)²/4⌉ > 1 for m ≥ 5, so the graphs that refuted the
  old body are no longer in the hypothesis. The note is the same as on bm_053:
  the restriction is not in the source, and the toroidal guard's only
  machine-checked inhabitant is the dart-free `K_1`.
* **axv_2009_12189_00 — `planar_fractional_vertex_arboricity_two_statement`. PASS.**
  Back-translation: *every graph with no K₅ and no K₃,₃ minor admits some
  `b ≥ 1` and a family of `2b` vertex sets, each inducing a forest, such that
  every vertex lies in at least `b` of them.* Corpus: "Every planar graph has
  fractional vertex-arboricity at most two." The existential form is the
  faithful cleared form of `va_f(G) ≤ 2`: the fractional covering LP has
  rational data, so its optimum is attained at a rational point and scales to an
  integral `(a:b)`-cover with `a ≤ 2b`, which is padded to exactly `2b` forests
  with copies of the empty forest. Repetitions among the `F i` are allowed, as a
  fractional cover requires. `wagner_planar` is planarity by Wagner's theorem;
  `is_forest (F i)` is "the subgraph induced on `F i` is a forest".
  **Active probe — the repair did not trivialise the predicate.** The reader
  machine-checked (Qed, axiom-free)
  `~ x219_frac_vertex_arboricity_le_two 'K_5`: an induced forest of `K₅` has at
  most two vertices (else `forest3` on `induced S` produces two non-adjacent
  vertices of a complete graph), so double counting gives
  `5b ≤ Σ_v #|{i : v ∈ F i}| = Σ_i #|F i| ≤ 4b`, contradiction for `b > 0`.
  This is exactly the grounding gap the previous readback flagged ("neither
  lemma exercises a graph with edges"), and it now has an answer.
  `x219_frac_va_b0_vacuous` is a correct but weak teeth lemma (its second
  conjunct `0 <= #|…|` is `leq0n`); the content it records — that `b = 0`
  satisfies the body for every graph — is nevertheless right.
* **axv_2004_07457_01 — `asymmetric_bipartite_list_colouring_statement`. PASS-WITH-NOTE.**
  Back-translation of the three conjuncts against the corpus `statement_text`
  (which carries the paper's Conjecture 7 verbatim):
  (i) *for every `q > 0` there is `D0` such that every bipartite `G` with side
  `A` of max degree ≤ `DA`, side `~: A` of max degree ≤ `DB`, `DA, DB ≥ D0`,
  `DA ≤ kA^q` and `DB ≤ kB^q` is `(kA,kB)`-choosable* — the source's
  `kA ≥ ΔA^ε` with `ε = 1/q`, `Δ0 = Δ0(ε)` quantified after ε and before the
  graph, exactly as in the paper. Restricting ε to the reciprocals `1/q` is not
  a loss: every real ε > 0 dominates some `1/q` and the condition is antitone in
  ε, so the `q`-family is the stronger (hence sufficient) one.
  (ii) and (iii) are the source's conditions with the real constant `C`
  naturalised, `log` replaced by `trunc_log 2`, and (iii) cleared by raising
  `kB ≥ C(Δ/log Δ)^{1/kA} log Δ` to the power `kA`, giving
  `kB^kA ≥ C^kA · Δ · (log Δ)^{kA−1}` — re-derived a third time and correct,
  with both disjuncts and their symmetry intact.
  **The floor and the base of the logarithm are both absorbed by the
  existential `C`**: `⌊log₂ D⌋ ≥ (log₂ D)/2` for `D ≥ 4`, and a base change
  multiplies the bound by `1.44^{kA}`, which is exponential in `kA` exactly like
  `C^{kA}` — so the transcription is implied by the paper's condition with a
  doubled constant. It is `D ≤ 1` alone that was fatal.
  **The repair has teeth (machine-checked).** The reader proved (Qed,
  axiom-free) that `1 < C`, `1 < D0`, `D0 ≤ DA`, `D0 ≤ DB` together with the two
  list-size hypotheses force `2 ≤ kA` and `2 ≤ kB` (because
  `trunc_log 2 D ≥ 1` as soon as `D ≥ 2`, `trunc_log_gt0`). The old refutation
  needed `kA = kB = 1`, so it is unreachable; and indeed the curated witness
  `meta/probe_hints/asymmetric_bipartite_list_colouring_statement.v` no longer
  compiles (`vacuity_probe` reports `stale-FIX-OK`).
  **The note.** Conditions (ii) and (iii) as encoded are **strictly weaker than
  the paper's literal (ii) and (iii)**, which carry no threshold. This is
  unavoidable — the literal conditions are false over the positive integers at
  `ΔA = ΔB = 1` in the paper too — and the doc block says so loudly under
  `MODELLING CHOICE`. Two precisions on the doc block's justification: the
  abstract's phrase "provided `ΔA` and `ΔB` are large enough" was checked on
  arXiv and is genuine, but there it is attached to the ε-conjecture, i.e. to
  condition (i), not to (ii)/(iii); and the English statement in the doc block
  says "base-two logarithm" where the body uses its **floor** (the `Notes:`
  clause does say `trunc_log`). Consequence for the proof leg: discharging this
  Rocq body would establish the asymptotic content of (ii)/(iii), not their
  literal form.
  A further observation, harmless because `C` is existential: condition (iii)
  with `C = 1`, `D0 = 2` is **false** (take `kA = 1`, `D = 2`, `A = {a₁,a₂}`
  with lists `{1}`, `{2}`, one `B`-vertex adjacent to both with list `{1,2}`:
  `C^1·D·L⁰ = 2 ≤ kB = 2` holds and the graph is not `(1,2)`-choosable). Any
  admissible constant must therefore be `≥ 2`; the existential quantifier
  supplies that, as the previous readback already noted.

### Probes

* `python3 meta/vacuity_probe.py --names albertson_toroidal_delete_three_statement,toroidal_five_choosability_critical_iff_six_critical_statement,toroidal_five_choosable_iff_five_colourable_statement,planar_fractional_vertex_arboricity_two_statement,asymmetric_bipartite_list_colouring_statement`
  → **`5 probed · 0 FLAGGED`**, with
  `asymmetric_bipartite_list_colouring_statement … hint stale-FIX-OK` (the
  curated refutation no longer compiles, which is the intended post-repair
  reading) and `none` for the other four.
* Three new axiom-free probes were written and compiled against the package
  (scratch only — none is a refutation, so nothing was added to
  `meta/probe_hints/`): `~ x219_frac_vertex_arboricity_le_two 'K_5`,
  `~ surface_embeddable 0 'K_1`, and the `2 ≤ kA /\ 2 ≤ kB` consequence of the
  repaired asymmetric guards. All three end in `Qed` with
  `Print Assumptions` → *Closed under the global context*.
* `grounding_X213.v` and `grounding_X219.v` were recompiled directly: 12 and 15
  `Print Assumptions` lines respectively, **all** "Closed under the global
  context". The grounding lemmas were read, not trusted by name;
  `x219_asym_needs_degree_guard` really does refute the *unguarded* condition
  (ii) on `complete 2` with the palette `unit`, and `x213_surface_embeddable_no_dart`
  really does only cover dart-free graphs.
* `make chromatic-theory -j4` → exit 0;
  `check_milestone.py X213 chromatic-theory` → ACCEPTED, 11/11, 6/6 axiom-free;
  `check_milestone.py X219 chromatic-theory` → ACCEPTED, 11/11, 7/7 axiom-free;
  `check_statement_docs.py chromatic-theory` → 142 targets, 142 documented,
  **0 errors**, reverse coverage 141/141.

### Items for the improvement ledger

1. **`surface_embeddable 0` is not planarity.** `~ surface_embeddable 0 'K_1`
   is now a machine-checked fact: the Euler count ignores dartless vertices, so
   every edgeless graph computes genus one. Any future row that wants "planar"
   from the surface layer must not write `surface_embeddable 0`. The clean fix
   is to add the isolated vertices back into
   `surface_embedding_vertices` (`#|porbits erot| + #|{v | no dart at v}|`) and
   to ship the canary as a lemma in `base/theories/surface.v`.
2. **The toroidal guard still has no machine-checked inhabitant with an edge.**
   `x213_toroidal_guard_K1` witnesses `surface_embeddable 1` on a graph with no
   dart, i.e. through the wrinkle of item 1. A `surface_embeddable 0 'K_2`
   witness (rotation = identity, one face) and, better, a genus-one rotation
   system for `K_5` or `K_7`, would make the three surface rows demonstrably
   non-vacuous; without them every non-vacuity claim about them rests on
   Euler's formula as read by a human, not by the kernel.
3. **Guard-has-teeth lemmas should refute the unguarded body, not merely
   exclude a graph.** `x213_connected_guard_has_teeth` excludes two isolated
   vertices, which are toroidal anyway; the honest witness (two disjoint `K_7`)
   is unavailable for want of item 2. Worth a template line: *a teeth lemma
   names a graph on which the unguarded statement is FALSE.*
4. **Asymptotic source conditions keep needing thresholds.** This is the second
   row in the batch (after U4's `t = 0`) where the paper's own condition is
   false at the smallest parameter. The repair shape used here — an existential
   `D0 > 1` quantified beside the constant, mirroring the source's own
   condition (i) — is worth promoting to the wave template, together with the
   `faithfulness_mutation.py` canary the previous readback asked for (drop the
   `1 < D0` guard, expect the probe hint to compile again).


## Re-read after the loop-degree repair (2026-09-23)

Reader: Claude Opus 5 second reader (faithfulness auditor), session
01P75Y6ikkgDyzUzzoef316Z. Third pass over cycle-theory, this time over the rows
whose MEANING changed when `Cycle.foundations.connectivity.subdeg` was repaired
to count ARC ENDS. **No statement body changed**; every verdict below comes
from back-translating the unchanged bodies against the *new* definitions,
blind (Rocq first, doc block second, corpus text third).

### Scope

`orientable_five_cycle_double_cover_statement` (X212, bm_026),
`cycle_double_cover_statement` (U6, OPG, audit-only),
`small_cycle_double_cover_statement` (X212, bm_013),
`m_n_cycle_covers_statement` (U6, OPG, audit-only),
`five_flow_statement` (D1, OPG), and the two D1 `mreg`/`mDelta` rows
(`circular_flow_numbers_of_r_graphs_statement`,
`circular_flow_number_of_regular_class_1_graphs_statement`) which use `mdeg`
with no `loopless` guard.

### The repair, back-translated

```coq
Definition ends_at (G : mgraph) (H : {set edge G}) (b : bool) (v : G) : {set edge G} :=
  [set e in H | endpoint b e == v].
Definition subdeg (G : mgraph) (H : {set edge G}) (v : G) : nat :=
  #|ends_at H false v| + #|ends_at H true v|.
Definition mdeg (G : mgraph) (v : G) : nat := subdeg [set: edge G] v.
```

`subdeg H v` = *the number of ends of `H`-arcs at `v`*. Reversing an arc swaps
its two contributions, so the count is symmetric in `source`/`target` (the
package's carrier convention), and a loop, having both ends at `v`, contributes
2 — the textbook degree. The two bounding lemmas are correct as stated:
`subdegE : subdeg H v = #|edges_at v :&: H| + #|loops of H at v|` (*degree =
incidences + loops*) and `subdeg_loopless : loopless G -> subdeg H v =
#|edges_at v :&: H|`. The derived notions inherit the right meaning: a single
loop is an `even_subgraph` and an `is_circuit` (degree 2, connected by the empty
walk), `is_matching` rejects it (degree 2 > 1), `eulerian` is unchanged (2 is
even), `cubic`/`simple_mgraph` are unchanged (both force `loopless`).

### Probes

```
$ python3 meta/vacuity_probe.py --names orientable_five_cycle_double_cover_statement,\
cycle_double_cover_statement,small_cycle_double_cover_statement,\
m_n_cycle_covers_statement,five_flow_statement
statement                                            auto=T auto=F hint           verdict
--------------------------------------------------------------------------------------------
cycle_double_cover_statement                         False  False  stale-FIX-OK   ok
five_flow_statement                                  False  False  none           ok
m_n_cycle_covers_statement                           False  False  none           ok
orientable_five_cycle_double_cover_statement         False  False  stale-FIX-OK   ok
small_cycle_double_cover_statement                   False  False  stale-FIX-OK   ok
--------------------------------------------------------------------------------------------
5 probed · 0 FLAGGED
```

The three `stale-FIX-OK` lines are the fix-verification signal: the committed
refutations of the previous two passes no longer compile.

### Verdicts

| row | file | before | after |
|---|---|---|---|
| bm_026 `orientable_five_cycle_double_cover_statement` | X212 | FAIL, blocked | **PASS — UNBLOCKED** |
| — `cycle_double_cover_statement` | U6 (OPG) | FAIL (refutable) | **PASS** |
| — `m_n_cycle_covers_statement` | U6 (OPG) | FAIL (third victim, undiagnosed) | **PASS** |
| bm_013 `small_cycle_double_cover_statement` | X212 | PASS | **PASS (unmoved)** |
| — `five_flow_statement` | D1 (OPG) | PASS | **PASS (unmoved)** |
| — `circular_flow_numbers_of_r_graphs_statement` | D1 (OPG) | PASS | **PASS — and now machine-checked to be loopless-guarded** |
| — `circular_flow_number_of_regular_class_1_graphs_statement` | D1 (OPG) | PASS | **DEFECT — reported, not repaired** |

### Readbacks

* **bm_026 `orientable_five_cycle_double_cover_statement` — PASS, unblock.**
  Blind back-translation of the unchanged body: *for every multigraph with at
  least one vertex that is connected and has no cut edge, there are five edge
  sets `C : 'I_5 -> {set edge G}` and five orientations `d`, such that every
  `C i` is an even subgraph, every `d i` orients `C i` so that each vertex is
  the tail of as many `C i`-edges as it is the head of, every edge lies in
  exactly two of the five, and the two members containing an edge give it
  opposite directions.* The corpus text is *"Every 2-edge-connected graph has an
  orientable double cover by five even subgraphs"* with the context sentence
  *"A double cover by even subgraphs is orientable if each even subgraph can be
  oriented so that every edge of the graph is traversed once in each
  direction."* — clause for clause the same. Quantifier order, hypotheses
  (connected + no cut edge; loops and parallel edges allowed, as in the source's
  multigraph setting), the exactness of "five" (`'I_5`, repetitions allowed as
  in a list), "exactly two" (`#|[set i | e \in C i]| = 2`) and orientability all
  check out. `x212_balanced` is well behaved on loops (a loop is its own tail
  and its own head, so it contributes 1 to each side).
  The loop defect is gone: the one-vertex one-loop multigraph `Lp` is now a
  genuine INSTANCE, with the conclusion exhibited. Each grounding lemma was
  checked by STATEMENT: `x212_mdeg_Lp : forall v : Lp, mdeg v = 2`,
  `x212_even_subgraph_Lp : even_subgraph [set: edge Lp]`,
  `x212_orientable_5_hypotheses_Lp` (`0 < #|Lp|` /\ `two_edge_connected Lp` /\
  `0 < #|edge Lp|`) and `x212_orientable_5_Lp :
  x212_orientable_5_even_double_cover Lp` — the last built from
  `x212_Lp_cover` (loop in `ord0` and `ord_max`, the other three empty),
  `x212_Lp_dir` (`i == ord0`), and the four component lemmas, all of which say
  what their names say. The refutation hint no longer compiles.
  *Adversarial re-probing* (each conclusion exhibited by hand, then checked
  against the definitions): two parallel loops at one vertex — `C0 = C1 =
  {e1}`, `C2 = C3 = {e2}`, `C4 = 0`, degrees 2 and 0, orientations `true`/
  `false`; the digon — `C0 = C1 =` both parallel edges, oriented as a directed
  2-cycle and as its reverse, both balanced; the cyclically oriented triangle —
  same trick on the whole edge set; the edgeless one-vertex graph — all five
  members empty, the "exactly two" clause vacuous; `K_4` — its four triangles,
  each edge in exactly two, orientable as the face boundaries of the spherical
  embedding. *A loop plus a pendant edge is not a counterexample, because a
  pendant edge IS a cut edge* and the graph is excluded. **Not trivialised
  either**: taking `C0 = C1 = [set: edge G]` only works on carriers all of whose
  degrees are even, and on cubic carriers every `mdeg` is 3, so the full edge
  set is not an `even_subgraph` and the whole snark core of the conjecture
  survives inside the encoding.
* **`cycle_double_cover_statement` (U6, OPG) — PASS.** Body: *every multigraph
  with at least one vertex and at least one edge in which no edge is a cut edge
  has a list of circuits covering every edge exactly twice*; corpus text: *"For
  every graph with no bridge, there is a list of cycles so that every edge is
  contained in exactly two."* `is_circuit C = C != set0 /\ subgraph_kregular C 2
  /\ subgraph_connected C` is a single circuit (2-regular *and* connected rules
  out disjoint unions and figure-eights, and admits a digon, which is right for
  multigraphs). The loop is now a circuit of length 1, `cdc_Gloop` realises the
  conclusion on it, and the hint is stale.
  The row's `Definitions:`/`Notes:` doc block now describes the convention
  **correctly**: it says `subdeg` counts ARC ENDS "so that a LOOP contributes 2
  and a single loop is a circuit of length 1", carries the `LOOP-DEGREE REPAIR
  (2026-09-23, main session)` paragraph, and correctly points at
  `grounding_U6.mdeg_Gloop` / `is_circuit_Gloop` / `cdc_Gloop` — all three of
  which say what they are cited for.
* **bm_013 `small_cycle_double_cover_statement` — PASS, unmoved.**
  `simple_mgraph` forces `loopless`, so `subdeg_loopless` makes the repair a
  no-op on this row; the readback of the previous pass stands verbatim.
* **`m_n_cycle_covers_statement` (U6, OPG) — PASS; the "third victim" claim is
  CONFIRMED.** Body: *every multigraph with at least one vertex and at least one
  edge and no cut edge has a list of exactly five even subgraphs covering every
  edge exactly twice*; corpus text: *"Every bridgeless graph has a
  (5,2)-cycle-cover."* — faithful, with the standard even-subgraph reading of
  "cycle" (documented as a modelling choice in the row's `Notes:`).
  The repair agent's claim that this row was a **third** victim of the loop
  defect is correct, and the argument is independent of the two hints (neither
  spelled it out): `Lp` is `bridgeless` with `0 < #|Lp|` and `0 < #|edge Lp|`,
  its single edge must occupy exactly two of the five list positions, every set
  containing that edge is `[set: edge Lp]`, and under the old convention
  `subdeg [set: edge Lp] tt = #|edges_at tt :&: [set: edge Lp]| = 1` is odd, so
  no member containing the loop was an `even_subgraph` — the conclusion was
  unsatisfiable although the conjecture plainly holds there. It is now realised:
  `grounding_X212.x212_m_n_cover_Lp` was read by STATEMENT and is literally the
  conclusion of `m_n_cycle_covers_statement` instantiated at `Lp`
  (`size L = 5`, all members `even_subgraph`, every edge counted twice), with
  `L = [:: setT; setT; set0; set0; set0]`.
  *Documentation gap (minor):* unlike its two siblings, this row's `Notes:`
  carries no `LOOP-DEGREE REPAIR` paragraph, although the repair is what makes
  it non-refutable; only the `Definitions:` line records the convention. Worth a
  sentence from the main session.
* **`five_flow_statement` (D1) — PASS, unmoved.** It does not mention `mdeg`,
  and a loop cancels on both sides of `iconservative`.

### The D1 `mreg` / `mDelta` decision

The source notion in both rows is the degree of a **graph without loops**: the
OPG text of the class-1 row defines *"A graph with maximum vertex degree k is a
class 1 graph if its edge chromatic number is k"*, and a graph with a loop has
no proper edge colouring at all, so the source's class-1 graphs are loopless;
likewise an *r-graph* is loopless. So the question for each row is whether the
encoding lets loopful carriers in.

* **`circular_flow_numbers_of_r_graphs_statement` — PASS.** `is_2t1_graph G t`
  **forces looplessness**, so the carrier class is exactly the source's and the
  loop convention is immaterial. This is not a reading but a theorem, and it is
  now machine-checked, `Qed`, *Closed under the global context*:

  ```coq
  Definition loops_at (G : mgraph) (v : G) : {set edge G} :=
    [set e | (source e == v) && (target e == v)].

  Lemma mdeg_cut (G : mgraph) (v : G) :
    mdeg v = (#|cut [set v]| + (#|loops_at v| + #|loops_at v|))%N.
  Proof.
  rewrite /mdeg subdegE setIT.
  have -> : [set e in [set: edge G] | (source e == v) && (target e == v)]
          = loops_at v by apply/setP => e; rewrite !inE.
  have := cardsUI (cut [set v]) (loops_at v).
  rewrite cutU_loops cutI_loops cards0 addn0 => ->.
  by rewrite addnA.
  Qed.

  Lemma is_2t1_loopless (G : mgraph) (t : nat) : is_2t1_graph G t -> loopless G.
  Proof.
  case=> reg cutb e; apply/negP => /eqP se.
  have h0 : (0 < #|loops_at (target e)|)%N.
    by apply/card_gt0P; exists e; rewrite inE se !eqxx.
  have hc : (2 * t + 1 <= #|cut [set (target e)]|)%N.
    by apply: cutb; rewrite cards1.
  have hm : (2 * t + 1)%N
          = (#|cut [set (target e)]|
             + (#|loops_at (target e)| + #|loops_at (target e)|))%N.
    by rewrite -(reg (target e)) mdeg_cut.
  rewrite hm -{2}[#|cut [set (target e)]|]addn0 leq_add2l leqn0 addn_eq0
          andbb in hc.
  by rewrite (eqP hc) in h0.
  Qed.
  ```

  (`cutI_loops : cut [set v] :&: loops_at v = set0` and
  `cutU_loops : cut [set v] :|: loops_at v = edges_at v` are two-line `setP`
  case splits.) Reading: *degree = (edges leaving v) + 2·(loops at v)*; the
  singleton `[set v]` is an odd vertex set, so `2t+1 <= #|cut [set v]|`, and
  with `mdeg v = 2t+1` that forces `#|loops_at v| = 0`. **Recommendation:** ship
  `mdeg_cut` and `is_2t1_loopless` as grounding lemmas of `grounding_D1.v` —
  they are exactly the "the guard excludes loops" fact the row's faithfulness
  now rests on, and they hold under either degree convention.
* **`circular_flow_number_of_regular_class_1_graphs_statement` — DEFECT
  (report, do not repair here).** Its hypotheses are `(1 <= t)%N`,
  `0 < #|G|`, `mreg G (2 * t + 1)` and `is_class1 G` — **no** odd-cut condition
  and **no** `loopless`. Nothing excludes loops, and since a loop now
  contributes 2, loopful carriers that the *old* convention rejected are now in
  the class. They break the row, because they can carry a **bridge** while
  `is_class1` still holds (base's `line_graph` makes a loop non-adjacent to
  itself, so `chromatic_index` is finite on loopful carriers, where the source's
  edge chromatic number is undefined). Explicit carrier, `t = 1`:

  | | |
  |---|---|
  | vertices | `x, y, u, v` |
  | edges | `a, b, c` parallel `x—y`; `l_u` a loop at `u`; `h = u—v`; `l_v` a loop at `v` |
  | degrees (arc ends) | `x: 3`, `y: 3`, `u: 2+1 = 3`, `v: 1+2 = 3` — so `mreg G 3`, and `mDelta G = 3` |
  | `line_graph G` | `K_3` on `{a,b,c}` ⊎ the path `l_u — h — l_v` (`l_u` and `l_v` share no vertex) |
  | `chromatic_index G` | `3`: `>= 3` by `sub_chi` + `chi_clique` on `{a,b,c}`, `<= 3` by the colouring `{a,l_u,l_v} / {b,h} / {c}` — hence `is_class1 G` |
  | conclusion | fails: at `u` the loop cancels, so `rconservative` gives `phi l_u + phi h = phi l_u`, i.e. `phi h = 0`, contradicting `1 <= |phi h|`. `G` has no nowhere-zero `r`-flow for any `r`, so `circular_flow_number_le G (2 + 2/1)` is false. |

  Under the OLD convention this carrier was **not** in the class
  (`#|edges_at u| = 2 != 3`), so the repair created this hole. Two remarks that
  size it:
  1. the row was **already false** as a mathematical statement — the corpus
     review records Mattiolo–Steffen (*J. Graph Theory* 99 (2022) 399–413)
     disproving it for `t = 4k+2`, `k >= 1` — so this is not "a true statement
     made false"; it is an already-false statement that can now be refuted for a
     **spurious** reason, by a 4-vertex graph the source excludes rather than by
     the real construction. Anyone closing the row with such a refutation would
     record a false claim about the literature.
  2. the header note of `D1.v` (lines ~70–75) states that *"the `mreg` /
     `mDelta` rows below, whose carriers are `(2t+1)`-regular or class-1 graphs,
     read exactly as before"*. That is **correct for the `is_2t1_graph` row**
     (by `is_2t1_loopless` above, under either convention) and **incorrect for
     the class-1 row**, whose carrier class strictly grew. The same over-claim is
     repeated in the per-row table of `meta/STATEMENT_IMPROVEMENTS.md`
     ("unaffected in substance").

  **Recommended repair (main session's call):** add `loopless G` to
  `circular_flow_number_of_regular_class_1_graphs_statement` — it is what the
  source means by a class-1 graph and it changes nothing about the conjecture's
  content — and correct the two notes above. (Only the `.v` body change is a
  repair; this reader did not touch it.)

### Verification

`python3 meta/check_milestone.py X212 cycle-theory` → ACCEPTED;
`python3 meta/check_statement_docs.py cycle-theory` → 0 errors;
`meta/v2_statement_waves.json` parses. `meta/probe_hints/` gained nothing: the
one new machine-checked lemma of this pass (`is_2t1_loopless`) is a POSITIVE
fact, not a refutation, and the class-1 counterexample above is left on paper
because MathComp 2's `Finite.enum` is locked, so the `coloring` / `omega`
booleans of a concrete 6-edge line graph cannot be discharged by `vm_compute`
(`#|'I_4| = 4` is already out of reach for it) — a machine-checked version needs
the explicit `partition` / `stable` / `clique` case splits, which belongs with
the repair, not with the audit. Recorded in `tactics-playbook.md` (entries 222–224).

### Addendum — the other two `mdeg` rows with no `loopless` guard (U6)

Sweeping cycle-theory for statement bodies that reach a degree without a
`loopless`, `cubic` or `simple_mgraph` guard turns up two more U6 rows that the
per-row table of `meta/STATEMENT_IMPROVEMENTS.md` groups under "unaffected:
`simple_mgraph` guards the first":

* `decomposing_an_eulerian_graph_into_cycles_with_no_tw_statement` — guarded by
  `eulerian G` and `forall v, 4 <= mdeg v`, **not** by `simple_mgraph` (that
  guard is on the sibling `decomposing_an_eulerian_graph_into_cycles_statement`
  only; the ledger line conflates the two). The carrier class DID grow: the
  one-vertex two-loop multigraph has `mdeg = 4` now and had `mdeg = 2` before.
  No refutation found — on that carrier `D = [:: [set e1]; [set e2]]` is a
  cycle decomposition (each loop is now a circuit) and neither member is two
  consecutive edges of the tour `[:: e1; e2]` (`cyc_pairs` is
  `[:: (e1,e2); (e2,e1)]`). **PASS, with the ledger line to be corrected.**
* `decomposing_eulerian_graphs_statement` — guarded by `edge_connected G 6` and
  `eulerian G`, again with no looplessness. This row looks like a **FOURTH
  victim of the old loop convention**, which nobody recorded: the one-vertex
  two-loop multigraph is `eulerian` and `edge_connected _ 6` (deleting both
  edges leaves one vertex, still `mconnected`), `P v = [set [set e1; e2]]` is a
  `transition2_system`, and under the OLD degree the only cycle decomposition
  was `[:: [set e1; e2]]` (a single loop was not a circuit), whose intersection
  with `edges_at v` is exactly the transition — so no compatible decomposition
  existed. Under the repaired degree `[:: [set e1]; [set e2]]` is a compatible
  decomposition. **PASS now**; worth adding to the repair's table for the
  record, and a `grounding_U6` lemma would pin it.
* Residual notion-level remark on the same row: `transition2_system` partitions
  `edges_at v`, an **incidence set**, whereas a classical 2-transition system
  partitions the **edge ENDS** at `v` (a loop occupies two of them). On a
  loopless carrier the two agree, and the `connectivity.v` carrier-convention
  header explicitly lists `U6.transition2_system` as a place where an incidence
  set "is meant" — but for a transition system it is a degree that is meant, so
  on loopful carriers the encoded transition systems are not the source's. The
  row currently survives, so this is an observation, not a blocker; if it is
  ever tightened, the cheap fix is the same `loopless` guard recommended for the
  D1 class-1 row.

## Follow-up after the loop-degree re-read (2026-09-23)

Main session, applying the prescriptions of the second reader of the previous
section (*Re-read after the loop-degree repair* and its *Addendum*).

### The one body change: the class-1 row

`D1.circular_flow_number_of_regular_class_1_graphs_statement`
(OPG `opg:circular_flow_number_of_regular_class_1_graphs`) — hypotheses before
and after, everything else textually identical:

```coq
(* before *)
forall (t : nat) (G : mgraph),
  (1 <= t)%N -> (0 < #|G|)%N -> mreg G (2 * t + 1)%N -> is_class1 G ->
  circular_flow_number_le G (2%:R + 2%:R / t%:R).

(* after *)
forall (t : nat) (G : mgraph),
  (1 <= t)%N -> (0 < #|G|)%N -> loopless G ->
  mreg G (2 * t + 1)%N -> is_class1 G ->
  circular_flow_number_le G (2%:R + 2%:R / t%:R).
```

The reader's diagnosis is adopted verbatim: the source's class-1 graphs are
loopless (a graph with a loop has no proper edge colouring, so its edge
chromatic number is undefined), while the encoding admitted loopful carriers
because base's `line_graph` makes a loop non-adjacent to itself, keeping
`chromatic_index` finite — and, since the loop-degree repair, such carriers are
`mreg _ (2t+1)` as well. The row was therefore spuriously refutable. The doc
block gained a `LOOPLESS GUARD (2026-09-23, second-reader prescription)`
paragraph, `loopless` in the `English statement:` and `[loopless]` in the
`Definitions:`; the `D1.v` header note and the per-row table of
`meta/STATEMENT_IMPROVEMENTS.md`, which both claimed that the two `mreg` /
`mDelta` rows "read exactly as before" / were "unaffected in substance", are
corrected to separate the two rows.

### Doc gaps closed (no body change)

* `U6.m_n_cycle_covers_statement` — `LOOP-DEGREE REPAIR (2026-09-23)` paragraph
  recording that it was the THIRD victim, realised on `Lp` by
  `grounding_X212.x212_m_n_cover_Lp`.
* `U6.decomposing_eulerian_graphs_statement` — `LOOP-DEGREE REPAIR (2026-09-23)`
  paragraph recording the FOURTH victim (one vertex, two loops, the transition
  system pairing them) and the residual remark that `transition2_system`
  partitions an incidence set rather than the edge ends.
* The ledger line that lumped
  `decomposing_an_eulerian_graph_into_cycles_with_no_tw_statement` (guarded by
  `eulerian` + `4 <= mdeg v`) together with its `simple_mgraph`-guarded sibling
  is split into three lines with the reader's verdicts.

### Lemmas added (all `Qed`, all *Closed under the global context*; 42 audited)

`grounding_D1.v`: `loops_at`, `cutI_loops`, `cutU_loops`, `mdeg_cut`,
`is_2t1_loopless` (the reader's proof, ported unchanged); `card_ends_at_add`,
`mdeg_add_edge`, `mDelta_mreg`; the non-vacuity chain `G2p`/`G3p`,
`loopless_G3p`, `mreg_G3p`, `mDelta_G3p`, `clique_line_G3p`,
`chromatic_index_G3p`, `is_class1_G3p`, `loopless_class1_3reg_G3p`; and the
teeth chain on the reader's counterexample carrier `Gcl` — `mreg_Gcl`,
`not_loopless_Gcl`, `edgeT_line_Gcl`, `card_abc_Gcl`, `clique_abc_Gcl`,
`nadj_Gcl`, `stable_S1_Gcl`, `stable_S2_Gcl`, `coloring_Gcl`,
`chromatic_index_Gcl` (= 3), `mDelta_Gcl`, `is_class1_Gcl` and
`class1_3reg_loopful_Gcl`. The reader left the counterexample on paper because
`Finite.enum` is locked; it is machine-checked here through explicit
`partition` / `stable` / `clique` case splits and `coloring.color_bound` /
`chi_clique` / `sub_chi`, with no `vm_compute` anywhere.

`grounding_U6.v`: the two-loop carrier `G2loop` with `card_edge_G2loop`,
`edgeT_G2loop`, `ends_at_G2loop`, `mdeg_G2loop` (= 4), `mconnected_G2loop`,
`eulerian_G2loop`, `edge_connected_G2loop`, `edges_at_G2loop`, `card_G2loop`,
`Ptwo`, `lp12_neq`, `transition2_G2loop`, `is_circuit_loop_G2loop`,
`cycle_decomposition_G2loop`, `compatible_decomposition_G2loop` and
`u6_decomposing_eulerian_G2loop` (hypotheses + conclusion of the fourth-victim
row on that carrier).

### Verification

`make cycle-theory -j4` exit 0; `check_milestone.py` ACCEPTED for D1, U6, U10,
X212, X228; `check_statement_docs.py cycle-theory` 0 errors (56/56 documented,
reverse coverage 52/52); `vacuity_probe.py` on the four rows above: 4 probed,
0 flagged; `faithfulness_mutation.py --mutant cycle_subdeg_counts_loop_once`
still 1/1 killed; `formal_resolutions.py --metadata-only` OK (the class-1 row is
not a registered resolution). Recorded in `tactics-playbook.md` (entries
225–228).


## Follow-up: surface vertex-count repair (2026-09-23)

**Attribution.** This follow-up implements the finding of the re-read recorded
above (*Re-read of the five repaired chromatic rows (2026-09-23)*, part "What
`surface_embeddable` actually means"): the reader derived
`base/theories/surface.v` line by line and found the **isolated-vertex wrinkle**
— `surface_embedding_vertices = #|porbits erot|` counts only the vertices that
carry a dart, so an edgeless graph got `V = E = F = 0` and computed genus 1, and
`~ surface_embeddable 0 'K_1` was machine-checkable although `K_1` is planar.
The reader classified the wrinkle as harmless AT INDEX 1 (so the three toroidal
rows keep their verdicts) but flagged that `surface_embeddable 0` is not
planarity and that every row of the shape "for every `g`, every graph with
`surface_embeddable g G` …" is thereby TOO WEAK.

**What changed in the foundation.** `surface_embedding_vertices (E) := #|G|` —
the textbook `V`, isolated vertices included; the parameter `E` is kept, so no
call site moved. Four new axiom-free lemmas pin the convention down:
`surface_embedding_vertices_orbits` (the old count = the number of NON-ISOLATED
vertices, proved from `surface_erot_vertex` by a `card_in_imset` bijection
between rotation orbits and dart-carrying vertices),
`surface_edgeless_genus0` / `surface_embeddable_edgeless` (a dartless graph with
at least one vertex is PLANAR) and the canary `surface_embeddable_K1 :
surface_embeddable 0 'K_1`, which directly reverses the reader's
`~ surface_embeddable 0 'K_1`. The twin foundation
`topological-graph-theory/theories/foundations/embedding.v` had the same defect
(`emV`) and received the same fix with the same lemmas (`emV_orbits`,
`edgeless_planar_embedding`, `planar_embedding_K1`,
`embeds_in_genus_K1_0`); its consumers all carry a connectivity guard, under
which the only affected graph was `K_1`, so the change is meaning-preserving
there.

**Effect on the three toroidal rows of this audit.** None of the verdicts moves,
and one grounding gap improves. `bm_053`, `axv_2407_18800_00` and
`axv_2407_18800_01` keep hypothesis `surface_embeddable 1 G /\ connected
[set: G]`, which is still exactly "toroidal" for connected graphs with at least
two vertices (for those, every vertex carries a dart, so the two counts agree —
this is now a lemma, `surface_embedding_vertices_orbits`, not an observation).
The reader's note (c) — "the only machine-checked inhabitant of the repaired
toroidal guard, `x213_toroidal_guard_K1`, is accepted through this wrinkle
rather than through a real embedding" — is RESOLVED: `K_1` is now admitted at
computed genus 0, i.e. as the planar graph it is, and the sharp statement lives
in base as `surface_embeddable_K1`. The reader's note (b) — "`surface_embeddable
0` is not planarity and must never be used as such" — is retired for graphs with
at least one vertex; it survives only for the EMPTY graph, which still evaluates
to genus 1 by `nat` truncation and is documented as such in `surface.v`. The
`x213_connected_guard_has_teeth` witness (two isolated vertices) is unchanged
and still disconnected, but it is now accepted at computed genus 0 through the
whole-graph Euler formula rather than through the blind spot; its comment was
rewritten accordingly. The `c-1` understatement on disconnected graphs, which is
what the connectivity guard is for, is untouched.

**Verification.** `make all -j4` exit 0; `make digraph-theory -j4` exit 0;
`check_milestone.py` ACCEPTED (11/11) for X213, X219, X210, X150, X152, X164
(chromatic-theory), X167, X80 (graph-theory-misc), X138, X202, X228, U13, D6emb
(topological-graph-theory), U13 (packing-theory), U2 (hamiltonicity-theory);
`check_statement_docs.py` 741/741 documented, 0 errors; `vacuity_probe.py
--files base/theories/surface.v chromatic-theory/theories/conjectures/X213.v
chromatic-theory/theories/conjectures/X219.v` → 13 probed, **0 FLAGGED** (no row
became settleable in either direction under the repaired hypothesis); `Print
Assumptions` *Closed under the global context* for all ten new lemmas; new
mutation canary `base_surface_vertices_orbit_count` (reverts the definition to
the orbit count) KILLED. Ledger entry: `meta/STATEMENT_IMPROVEMENTS.md`, *base — surface vertex
count repair (2026-09-23)*.

**Status of the three "items for the improvement ledger" of the re-read.**
Item 1 (*`surface_embeddable 0` is not planarity*) is DONE, and in exactly the
form the reader proposed: the reader's `#|porbits erot| + #|{v | no dart at v}|`
IS `#|G|` — that identity is what `surface_embedding_vertices_orbits` makes
machine-checked — so the definition was simply set to `#|G|`, and the canary now
ships as a lemma in `base/theories/surface.v` (`surface_embeddable_K1`) as
requested. Item 2 (*no machine-checked inhabitant of the toroidal guard with an
EDGE*) stays OPEN: `x213_toroidal_guard_K1` is now honest (`K_1` is planar, not
a wrinkle) but still dartless; the suggested `surface_embeddable 0 'K_2`
witness, and a genus-one rotation system for `K_5`/`K_7`, remain to be built.
Item 3 (*a teeth lemma should refute the unguarded body*) stays OPEN for the
same reason — `x213_connected_guard_has_teeth` still exhibits a graph that is
excluded by the guard rather than one on which the unguarded body is false, and
the honest witness (two disjoint `K_7`) still needs item 2.

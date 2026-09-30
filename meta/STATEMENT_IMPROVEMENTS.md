# Statement improvement ledger (plan WP4)

Findings collected while writing the corpus doc blocks of `meta/check_statement_docs.py` on the
existing Rocq statements. One section per package, appended independently by the per-package
documentation passes; inside a section, `### Duplicated vocabulary` lists the WP4b warnings of
`python3 meta/check_statement_docs.py --warnings <pkg>` (local definitions whose name duplicates a
coq-graph-theory / GTBase / MathComp notion), `### Suspected unfaithful or proxy encodings` lists
statements whose Rocq body does not faithfully render its corpus row (with a severity: too strong /
too weak / wrong object / vacuous-looking), and `### Other` collects everything else worth a later
pass. Nothing here changes a statement body: WP4 only writes comments, the fixes belong to a later
wave. Empty subsections say "none found".

## reconstruction-theory

Pass over the 7 documented targets of `reconstruction-theory/theories/conjectures/` (U11.v: 4 OPG
rows; X21.v: 3 `studies:` rows). Gate: `python3 meta/check_statement_docs.py --ignore-baseline
reconstruction-theory` -> 7 target(s), 7 documented, 0 error(s).

### Duplicated vocabulary

none found (`--warnings reconstruction-theory` reports 0 warnings). See `### Other` for two
deliberate near-duplicates that the suffix heuristic does not catch.

### Suspected unfaithful or proxy encodings

- `studies:std_n_dl_s_conjecture_deck_reconstruction_of_trees`
  (`reconstruction-theory/theories/conjectures/X21.v:78`,
  `nydl_tree_l_deck_reconstruction_statement`) — severity: **too strong (refutable as written)**.
  The hypotheses are `4 <= n`, `n./2 + 1 <= ell`, `#|T1| = #|T2| = n`, both trees, and
  `x21_same_l_deck T1 T2 ell`; nothing bounds `ell` by `n`. For `ell > n` the index type
  `{S : {set T} | #|S| == ell}` is empty, so `x21_same_l_deck` holds with the empty bijection and
  the statement asserts that any two `n`-vertex trees are isomorphic. Counterexample: `n = 4`,
  `ell = 5`, `T1 = P4`, `T2 = K_{1,3}`. Fix in a later wave: add `ell <= n` (the corpus row means
  `floor(n/2) + 1 <= ell <= n`).
- `studies:std_spinoza_west_connectedness_threshold_conjecture`
  (`reconstruction-theory/theories/conjectures/X21.v:105`,
  `spinoza_west_l_deck_connectedness_statement`) — severity: **too strong (refutable as written)**.
  Exactly the same missing `ell <= n` guard: for `n = 6`, `ell = 7`, take `G = K6` and `H` edgeless
  on 6 vertices; the `7`-decks are both empty, so the hypothesis holds and the conclusion
  `connected [set: G] <-> connected [set: H]` fails.
- `studies:std_kelly_manvel_conjecture_reconstruction_from_the`
  (`reconstruction-theory/theories/conjectures/X21.v:52`,
  `kelly_manvel_n_minus_r_deck_reconstruction_statement`) — severity: **too weak (mild)**.
  `x21_l_reconstructible` (X21.v:20) only quantifies over graphs `H` with `#|H| = #|G|`, whereas
  "reconstructible from its `(n-r)`-deck" quantifies over all graphs. The restriction is harmless
  for `r < n` (the deck determines `n`) but it is an added hypothesis that is not in the corpus
  row, and it is not derived anywhere. The other added guard, `r <= N`, is harmless: the conclusion
  is monotone in `N` and it makes `#|G| - r` a genuine subtraction rather than a nat truncation.

### Other

- Deliberate near-duplicates of library vocabulary in `U11.v`, documented in the file and in the
  doc blocks, not flagged by the gate's suffix heuristic: `sline_graph` (U11.v:143) vs
  coq-graph-theory's `line_graph : mgraph -> sgraph` (the local one is the iterable
  `sgraph -> sgraph` counterpart), and `sdel_edge` (U11.v:124) vs `digraph.del_edge` (directed arc,
  returns a `diGraph`). Both are tagged `@MOVE-to-base` in the file; WP4b should decide whether
  they move to `base/theories/common.v` under those names.
- Deck vocabulary is defined twice across the package: `same_deck` / `reconstructible`
  (U11.v:283-288) over `vdel_card` (U11.v:147) are the `ell = n-1` special case of
  `x21_same_l_deck` / `x21_l_reconstructible` over `induced` (X21.v:11-24), with the same
  bijection-of-index-sets model.
  A single `deck`/`same_deck`/`l_deck` family (package `foundations/`, or `base` if a second
  package needs it) would remove the duplication; an equivalence lemma
  `same_deck G H <-> x21_same_l_deck G H (#|G|).-1` is the WP6 obligation before any body rewrite.
- `opg:grahams_conjecture_on_tree_reconstruction` is a corpus *Problem* ("can we determine it
  from the integer sequence ... ?"); U11.v:264 states the affirmative proposition. This is
  recorded in the `Notes:` block; it is a project-wide convention rather than a defect, but a
  reader of the corpus row alone cannot tell which polarity was chosen.
- `opg:reconstruction_conjecture` (U11.v:308) imposes `3 <= #|G|` *and* `3 <= #|H|` although the
  deck bijection already forces `#|G| = #|H|`; redundant, harmless.

## spectral-graph-theory

Pass over the 7 documented targets of `spectral-graph-theory/theories/conjectures/` (D5.v: 5 OPG
rows; X6.v and X134.v: 2 `studies:` rows). All of them are stated over the area-local foundations
`spectral-graph-theory/theories/foundations/spectral.v` (`adjmx`, `degmx`, `Lapmx`, `is_spectrum`,
`is_signing`, `spectral_radius_le`, `is_deg_sorted`, `degseq`, `cospectral`,
`determined_by_spectrum`, and the labelled-graph layer `ladj`/`lgraphs`/`ladjmx`/`lcospectral`/
`liso`/`lspec_determined`/`total_count`/`determined_count`); each doc block names the ones its body
uses. Gate: `python3 meta/check_statement_docs.py --ignore-baseline spectral-graph-theory` ->
7 target(s), 7 documented, 0 error(s).

### Duplicated vocabulary

- `spectral-graph-theory/theories/conjectures/D5.v:63 strongly_regular` — library counterpart
  `regular` (GTBase, `base/theories/base.v:52`). False positive of the suffix heuristic:
  `strongly_regular` is a strictly stronger, different notion and its body *uses* `regular G k`
  rather than redefining it. No action; it is however a candidate for
  `base/theories/common.v` if a second package ever needs strongly regular graphs (it carries the
  primitivity guards, which are easy to get wrong).

### Suspected unfaithful or proxy encodings

- `opg:triangle_free_strongly_regular_graphs` (D5.v:91) — severity: **too strong (proxy)**. The
  corpus Problem asks for an *eighth* triangle-free strongly regular graph; the Rocq body asks for
  eight pairwise non-isomorphic ones. The two are equivalent only modulo the (unformalized) fact
  that exactly seven are known, so a prover must exhibit all eight rather than one new graph.
  A faithful alternative would enumerate the seven known graphs in `foundations/` and state the
  existence of one more, non-isomorphic to each.
- `studies:std_elphick_farber_goldberg_wocjan_conjecture_s_s` (X6.v:51),
  `studies:std_elphick_farber_goldberg_wocjan_conjecture_square` (X134.v:27, a synonym of the
  former) and `opg:laplacian_degrees_of_a_graph` (D5.v:233) — severity: **vacuous-looking**. Each
  is an implication whose hypothesis is `is_spectrum A s` for a spectrum `s` over an *abstract*
  `R : rcfType`. If the characteristic polynomial of `A` does not split over that particular `R`,
  no such `s` exists and the row holds vacuously for it. Splitting does hold for a symmetric matrix
  over any real-closed field, but that fact is nowhere proved in the development, so the statements
  currently carry no evidence of non-vacuity. Suggested follow-up: a `foundations/spectral.v` lemma
  `exists s, is_spectrum (adjmx R G) s` (resp. for `Lapmx`), or an added existence conjunct.
- `opg:signing_a_graph_to_have_small_magnitude_eigenvalues` (D5.v:121) — severity: **too weak
  (mild)**. `spectral_radius_le S b` (foundations/spectral.v:68) constrains only the eigenvalues
  of `S` that lie in `R` (`forall x : R, eigenvalue S x -> |x| <= b`). Over a real-closed field all
  eigenvalues of a symmetric matrix are in `R`, so the encoding is adequate, but as stated the bound
  says nothing about eigenvalues in an extension; the same unproved splitting fact is load-bearing.
- `opg:are_almost_all_graphs_determined_by_their_spectrum` (D5.v:153) — severity: **proxy (no
  soundness issue found)**. "Almost all" is rendered as `forall m > 0, exists N, forall n >= N,
  m * (total_count n - determined_count n) <= total_count n`, i.e. a nat-only density-one limit,
  and spectral determination is taken in the *labelled* model of `foundations/spectral.v`
  (cospectrality = equality of `char_poly` over `int`; isomorphism = permutation relabelling,
  `liso`, not `diso`). Both moves are deliberate and documented, but they mean the row is about
  labelled counts, not about the `sgraph`-level `determined_by_spectrum` that the same foundations
  file defines (spectral.v:57) and that no statement in the package uses. Worth an equivalence
  lemma (`liso r r' <-> inhabited (sgraph_of r ≃ sgraph_of r')`) before any proof work.

### Other

- **Duplicate corpus rows.** `studies:std_elphick_farber_goldberg_wocjan_conjecture_square`
  (X134.v) and `studies:std_elphick_farber_goldberg_wocjan_conjecture_s_s` (X6.v) are the same
  conjecture: `E2+`/`E2-` and `s+`/`s-` denote the same quantities, and X134's body is literally
  `elphick_farber_goldberg_wocjan_splus_sminus_statement`. Candidate for a corpus
  `same_conjecture` edge / `alias_of` in `meta/build_v2_manifest.py`, which would then make one of
  the two rows non-citable and remove the duplicated definition.
- `opg:does_the_symmetric_chromatic_function_distinguish_trees` (D5.v:199) faithfully encodes the
  corpus Problem ("Do there exist non-isomorphic trees which have the same chromatic symmetric
  function?") as an existence statement, so the `Prop` is the *expected-false* side: proving it
  would refute Stanley's conjecture. Recorded in the doc block; flagged here because a reader
  scanning names could take the row title ("does ... distinguish between trees?") for the opposite
  polarity.
- The chromatic symmetric function is encoded by its monomial-basis data (`csf_coeff`, D5.v:169:
  counts of proper `k`-colourings by colour-class-size vector) rather than as a symmetric-function
  object. Adequate for comparing two graphs, but not reusable as "the" chromatic symmetric
  function; if a second row ever needs it, it should move to `foundations/`.
- `cospectral` and `determined_by_spectrum` (foundations/spectral.v:54, 57) are defined but used by
  no statement in the package (the "almost all" row uses the labelled layer instead); dead
  vocabulary to either wire in or drop.
- The D5.v file header (lines 1-28) still repeats the five corpus source texts, which now also live
  in the per-definition doc blocks. Harmless duplication, but it is a second place to keep in sync
  when a corpus `statement_text` changes (WP3).

## cycle-theory

Pass over the 46 documented targets of `cycle-theory/theories/conjectures/` (D1.v: 15 OPG flow rows
+ 1 orphan; U6.v: 11 OPG cycle-cover/decomposition rows; U10.v: 3 OPG perfect-matching rows;
X5.v: 3 `erdos:` rows; XE1.v/XE2.v: 5 `erdos:` rows; X9.v: 2 arXiv rows; X184.v: 1 arXiv row;
X10.v/X24.v: 3 `studies:` rows; `implications_D1.v`/`implications_U10.v`: 2 orphan "external cited
fact" hypotheses). Most rows live on the multigraph carrier `mgraph` with edge sets `{set edge G}`
and share the vocabulary of `cycle-theory/theories/foundations/connectivity.v`; the `erdos:`,
`studies:` and arXiv rows live on `sgraph` with per-file local vocabulary. Gate: `python3
meta/check_statement_docs.py --ignore-baseline cycle-theory` -> 46 target(s), 46 documented,
0 error(s); reverse coverage 43/43 rows covered.

### Duplicated vocabulary

27 WP4b warnings. Grouped:

- **Four identical copies of the simple-graph edge set** — `cycle-theory/theories/conjectures/
  X10.v:16 x10_edge_set`, `X24.v:11 x24_edge_set`, `X9.v:11 x9_edge_set`, `XE1.v:9 xe1_edge_set`.
  All four have literally the same body, library counterpart `E(G)` (`sg_edge_set`,
  coq-graph-theory `sgraph`), with the bridge lemma `sg_edge_setE` already in
  `base/theories/common.v:41`. One `E(G)` per body would remove all four.
- **Cycle predicates** — `X10.v:11 x10_rainbow_cycle`, `X10.v:27 x10_longest_cycle`,
  `X24.v:27 x24_rainbow_cycle`, `X9.v:18 x9_genuine_cycle`, `XE1.v:21 xe1_cycle` — library
  counterpart `ucycle` (MathComp `path.v`); each is `ucycle (--) c /\ 2 < size c` possibly plus a
  colour condition. The `2 < size c` guard (a "genuine" cycle) recurs in six files and in
  `base/theories/base.v:111 girth_geq`; it is a candidate for a single `genuine_cycle` in
  `base/theories/common.v`.
- **Consecutive-edge extraction** — `X9.v:15 x9_cycle_edges`, `XE1.v:13 xe1_cycle_edges`,
  `X24.v:24 x24_cycle_edge_seq` (and `X10.v` inline) all compute `zip c (rot 1 c)` mapped to
  two-element sets; `X9.v:34 x9_consecutive_in_cycle` and `U6.v:173 cyc_pairs` are the same idea on
  another carrier. One shared helper would serve six rows.
- **Perfect matchings** — `U10.v:61 is_perfect_matching` (on `{set edge G}`) and
  `X24.v:15 x24_perfect_matching` (on `{set {set G}}`) — library counterpart
  `perfect_matching` (`base/theories/common.v:61`) and `matching` (coq-graph-theory
  `connectivity.v`). NOTE: the library notion is on `sgraph`, the `U10`/`U6` ones on `mgraph` edge
  sets, so the duplication is nominal on the multigraph side; the real WP4b fix there is an
  `mgraph` matching layer in `base/`, not a rewrite of the bodies.
- **Matching / path / tree / connectivity on `mgraph`** — `U6.v:73 is_path`, `U6.v:77 is_matching`,
  `U6.v:83 spanning_connected`, `U6.v:86 spanning_tree`, `D1.v:282 mg_branch_connected`,
  `D1.v:287 mg_minor`, `X184.v:16 x184_directed_k_edge_connected`, and in the package foundation
  `connectivity.v:57 connected_del_edges`, `:66 two_connected`, `:70 edge_connected`,
  `:79 subgraph_connected`, `:104 two_edge_connected` — library counterparts `Path`/`upath`,
  `matching`, `is_tree`/`is_forest`, `connected`, `minor`, `k_edge_connected`
  (coq-graph-theory `sgraph.v`/`connectivity.v`/`minor.v`, `base/theories/common.v:105`). Same
  caveat: all of these are the multigraph versions of `sgraph` notions, defined through `uwalk`
  rather than `Path`. `connectivity.v` is already the package's shared layer, so the WP4b action is
  to promote *that file* (or an `mgraph` section of `base/theories/common.v`), not to rewrite
  statements.
- Not caught by the suffix heuristic but worth listing: `D1.v:210 sedge (G : sgraph) : {set {set
  G}}` shadows the name of coq-graph-theory's `sedge` (the adjacency relation of an `sgraph`) while
  meaning the edge *set*; it is yet another copy of `E(G)`. Renaming it is a pure-readability fix.
  Likewise `D1.v:114 mreg`, `D1.v:124 mDelta`, `connectivity.v:35 mdeg` and `U6.v:95 cubic` are
  already tagged `@MOVE-to-base` in their own comments, and `U6.v:69 acyclic` (on `mgraph` edge
  sets) collides by name with `base/theories/common.v:139 acyclic` (on `diGraph`).

### Suspected unfaithful or proxy encodings

- `arxiv:1701.03366#00` (`X184.v:53 z5_antisymmetric_flow_edge_connectivity_statement`) — severity:
  **wrong object**. Already recorded in the corpus `verification_note` (faithfulness audit
  2026-07-17, `meta/BLOCKED_RETARGETING_AUDIT.md`): `x184_z5_antisymmetric_flow` (X184.v:20-25) is
  exactly "nowhere-zero + conservation mod 5", i.e. a plain nowhere-zero Z_5-flow; the defining
  ANTISYMMETRY condition of a Nesetril-Raspaud antisymmetric flow (the set B of used values
  satisfies B ∩ (−B) = ∅) is absent. The row is a proxy and the Rocq statement is strictly weaker
  than the conjecture. Recorded in the doc block.
- `opg:approximation_ratio_for_k_outerplanar_graphs` (`D1.v:802`) — severity: **wrong object
  (proxy)**. The corpus row is a *question* about the approximation ratio of MaxEDP / MaxIMF on
  k-outerplanar graphs; the Rocq body is a bounded-integrality-gap statement on the
  bounded-treewidth class, with no planarity, no k-outerplanarity and no computation model
  (the approximation *algorithm* is replaced by "there exists an integral routing within a factor
  c of the fractional value"). Deliberate and documented in the file header, but the row should
  arguably be `blocked` (needs-computation-model) rather than `done`.
- `opg:a_homomorphism_problem_for_flows` (`D1.v:655`) — severity: **too weak**. The source says
  "abelian groups"; the Rocq body quantifies over `finGroupType`, so infinite abelian groups (e.g.
  Z itself, the natural source of integer flows) are out of scope. A faithful version needs an
  abelian-group carrier that is not required to be finite, which conflicts with the Cayley graph
  being an `sgraph` (finite vertex type) — probably a `blocked`/`partial` candidate.
- `opg:faithful_cycle_covers` (`U6.v:422`) — severity: **too weak (mild)**. The source has
  `p : E -> Z`; the Rocq body has `p : edge G -> nat`, so only nonnegative weightings are covered.
  Nonnegativity is implicit in "faithful cover" (a cover count), so the restriction is harmless in
  practice, but it is formally a narrowing of the hypothesis class.
- `opg:decomposing_an_eulerian_graph_into_cycles_with_no_two_consecutives_edges_on_a_prescirbed_eulerian_tour`
  (`U6.v:317`) — severity: **too weak (mild)**. `is_eulerian_tour` (U6.v:109) uses coq-graph-theory's
  `walk`, which follows the intrinsic `source`→`target` orientation of `mgraph` edges, instead of
  the undirected `uwalk` used everywhere else in the package. The hypothesis therefore only bites on
  presentations whose reference orientation is itself an eulerian orientation. Since every eulerian
  multigraph admits such a presentation and the conclusion is orientation-free, the statement is
  equivalent up to reorientation, but as written it is the weaker universally quantified form.
  Switching `walk` to `uwalk` would remove the subtlety.
- `opg:unit_vector_flows` (`D1.v:388`) and `opg:real_roots_of_the_flow_polynomial` (`D1.v:600`) —
  severity: **too strong (mild, deliberate)**. Both quantify over an arbitrary `rcfType` where the
  source speaks of the real numbers; by model completeness of real-closed fields the first-order
  content coincides, but that transfer is nowhere formalized here, so a prover must handle every
  real-closed field. Documented in the doc blocks.

### Other

- **Two different meanings of "cycle" inside U6.v.** `opg:m_n_cycle_covers` (U6.v:369) and
  `opg:strong_5_cycle_double_cover_conjecture` (U6.v:443) take cover members to be `even_subgraph`s
  (elements of the cycle space), whereas `opg:cycle_double_cover_conjecture` (U6.v:468) uses `cdc`,
  whose members are single `is_circuit`s. Both readings are standard and, for the unrestricted CDC,
  equivalent, but the package should either state the equivalence lemma (an even subgraph decomposes
  into circuits) or use one convention throughout.
- **`xe2_all_cycle_lengths_in` is misnamed** (`XE2.v:36`): it asserts that SOME genuine cycle has its
  length in `P`, which is what `erdos:71` needs; the name reads as a universal statement. Rename
  suggestion: `xe2_some_cycle_length_in`.
- **Questions stated affirmatively.** `erdos:64/577/641/71/752/815`,
  `studies:std_akbari_...`, `arxiv:2502.04726#03` and `opg:antichains_in_the_cycle_continuous_order`
  are phrased in the corpus as questions ("Does every ...?"); every Rocq body is the affirmative
  form. That is the package-wide convention and is now stated in each doc block, but for the six
  rows whose corpus status is `solved` a reader could mistake the `Prop` for a theorem.
- **Extra guard in `opg:antichains_in_the_cycle_continuous_order`** (`D1.v:248`): the members of the
  witness family are required to have at least one edge, which strengthens the existential claim.
  It is harmless (an edgeless family admits cycle-continuous maps in both directions, hence is never
  a witness) but it is an addition to the source text, and "infinite set of graphs" is rendered as a
  `nat`-indexed family whose pairwise non-isomorphy is a consequence, not a hypothesis.
- **`opg:unit_vector_flows` carries a second conjecture** (the antipodally-odd labelling of the
  sphere by values in {-4..4}\{0}); it is formalized as `unit_vector_flows_q_statement` (D1.v:401)
  and owns no corpus row, since a row holds a single `formal_name`. If the corpus ever splits the
  row, this orphan becomes citable.
- **Two orphan "external cited fact" hypotheses.** `external_modular_orientation_to_flow_statement`
  (`implications_D1.v:115`, Tutte's modular-orientation/flow duality) and
  `external_petersen_BF_cover_statement` (`implications_U10.v:85`, the six perfect matchings of the
  Petersen graph) are not conjectures but explicit hypotheses that keep the implication edges
  axiom-free. Both are finite or classical facts that could be *proved* in `foundations/` later,
  which would upgrade the corresponding edges from conditional to unconditional.
- **`x5_edge_count`** (`X5.v:11`) counts edges as ordered adjacent pairs filtered by `enum_rank`;
  `#|E(G)|` (with `card_edge_Kn` and friends in base) would do the same job and is the form used by
  `XE2.v:169`. Minor, but the two counts appear in sibling rows (`erdos:916` and `erdos:815`) that
  both use "2n-2 edges".

## homomorphism-theory

*(WP4 doc-block pass, 12 targets in `U3.v` (10), `X135.v` (1), `X22.v` (1); 0 orphans.
Gate: `statement docs: 12 target(s), 12 documented, 0 error(s); reverse coverage: 12/12`.)*

### Duplicated vocabulary

From `check_statement_docs.py --warnings` (4):

- `homomorphism-theory/theories/conjectures/U3.v:126` `longest_cycle` — MathComp
  `ucycle`/`cycle` (`path.v`). Only the *suffix* collides: the body is a maximality
  predicate over `ucycle (--) c`, and no library notion expresses "longest". Keep.
- `homomorphism-theory/theories/conjectures/U3.v:270` `strongly_regular` — base's
  `regular` (`base/theories/base.v:52`), which `srg` already reuses verbatim.
  `strongly_regular` itself is a genuinely new notion. Keep.
- `homomorphism-theory/theories/conjectures/U3.v:329` `is_path` — coq-graph-theory
  `upath` / MathComp `path` (`sgraph.v`, `path.v`). `is_path s = uniq s && path (--) …`
  is exactly a simple walk presented as a `seq`; restating it with the library `upath`
  (or promoting a `seq`-level `simple_path` to `GTBase.common`) would remove the copy.
- `homomorphism-theory/theories/conjectures/U3.v:332` `longest_path` — same family as
  `is_path`; the maximality wrapper has no library counterpart. Keep once `is_path` is.

Not flagged by the suffix rule but duplicating library/base vocabulary:

- `U3.v:373` `hom_ffun` / `U3.v:376` `endo_count` — boolean reflection of base's
  `is_hom` (`base.v:69`), with `hom_ffunP` proving the two agree.
  `homomorphism-theory/theories/conjectures/X135.v:13` `x135_hom_count` is an
  **independent second copy** of the same boolean encoding (identical
  `[forall x, [forall y, (x -- y) ==> (f x -- f y)]]` under a different name). A single
  `hom_count` / `hom_ffun` in `GTBase.common` would serve both, plus
  `infinite-graph-theory/D4doa.v:95` `is_proper3`, which is the same pattern with
  `c x != c y`.
- `U3.v:70` `star_graph n` — a bare alias of the library `'K_1, n.-1` (`KB`).
- `U3.v:64` `path_graph` — no base counterpart (base owns `cycle_graph` only);
  a `GTBase.common` candidate, since `hamiltonicity`/`extremal` rows want `P_n` too.
- `U3.v:418` `bipartite_rel` — the relation-level form of base's `bipartite`
  (`base.v:312`): `bipartite G = bipartite_rel G (--)`. An equivalence lemma would let
  the row use base's name on the complement relation.
- `U3.v:202` `hom_equiv` — already tagged `@MOVE-to-base` in the file; used by two rows
  here (Cayley cores, strongly-regular cores) and a natural companion of
  `homs_to`/`is_core`.

### Suspected unfaithful or proxy encodings

- `opg:cores_of_cayley_graphs` (`U3.v`) — **too weak**. The source says "let M be an
  abelian group"; the encoding quantifies over `finGroupType`, i.e. FINITE abelian
  groups only, and over the concrete power `{ffun 'I_k -> M}` with M's pointwise
  operations rather than a packed group instance. Sound for the finite-graph reading
  the row needs, but the infinite instances of the source are not covered.
  (Rendering "the core of G" without a core operator, as "some Cayley graph on a power
  of M that is a core and hom-equivalent to G", is *not* a defect: cores of finite
  graphs are unique up to isomorphism.)
- `opg:cores_of_strongly_regular_graphs` (`U3.v`) — same core-operator rendering;
  "has a complete graph as core" becomes "is hom-equivalent to some `'K_n`", which is
  equivalent because `'K_n` is its own core. No defect found.
- `opg:pentagon_problem`, `opg:mapping_planar_graphs_to_odd_cycles`,
  `opg:do_any_three_longest_paths…`, `opg:extremal_problem_on_the_number_of_tree_endomorphism`
  — each adds a degeneracy guard absent from the source text (`0 < k`, `0 < #|G|`,
  `0 < n`). All four are **too weak** in the strictly formal sense but exclude only
  readings the source clearly does not intend (target `C_1`, empty graph, empty tree).
- `studies:std_engbers_homomorphism_count_maximisation_conjectu` (`X135.v`) — the corpus
  records PARTIAL (proxy) because the fractional exponents are cleared by raising both
  sides to `D = 2*delta*(delta+1)`. Over `nat` that is an equivalence, so **no strength
  is gained or lost**; the earlier independent audit (wf_bdaea8ab) reached the same
  conclusion. Candidate for upgrading the leg from `partial` to `done` in WP6.
- Vacuity sweep: none of the 12 rows is trivially provable or trivially refutable as
  stated; every hypothesis is satisfiable by a small concrete graph (cubic girth-`g`
  graphs, 3-connected graphs, trees, strongly regular graphs).

### Other

- **Duplicate formalisation across corpora.** `opg:mapping_planar_graphs_to_odd_cycles`
  (`U3.v:314`) and `studies:std_jaeger_s_conjecture_high_girth_planar_graphs_and`
  (`X22.v:29`) state the *same* mathematics with essentially the same body (only the
  order of the `k`/`G` binders and the `0 < k` vs `1 <= k` spelling differ). Consider
  one definition plus an alias, or a `implications_*` lemma tying them, so the two rows
  cannot drift apart.
- `X22.v` does not formalise the corpus text's equivalent phrasing "the circular
  chromatic number of G is at most (2k+1)/k"; circular chromatic number is not in the
  vocabulary. Not a defect, but a WP5 vocabulary candidate.
- `U3.v` file header (lines 24–31) still advertises `cycle_graph`, `triangle_free` and
  `k_connected` as "area-specific new primitives"; all three were since promoted to
  `GTBase.base`. Comment-only staleness.

## infinite-graph-theory

*(WP4 doc-block pass, 12 targets across `D4_unblocked.v` (2), `D4doa.v` (2),
`D4inf1.v` (2), `D4inf2.v` (1), `D4inf3.v` (2), `D4inf4.v` (2), `D4inf5.v` (1);
0 orphans. Gate: `12 target(s), 12 documented, 0 error(s); reverse coverage: 12/14`.)*

### Duplicated vocabulary

From `check_statement_docs.py --warnings` (6):

- `infinite-graph-theory/theories/conjectures/D4inf2.v:47` `proper_self_minor` —
  `minor`/`strict_minor` (coq-graph-theory `minor.v`, re-exported by base). The library
  notion is `sgraph`-only; the `iGraph` branch-set model (`minor_model`,
  `proper_witness`) is genuinely new. Keep, but it belongs in
  `infinite-graph-theory/theories/foundations/igraph.v` rather than in a conjecture file
  (a second infinite row will want it).
- `infinite-graph-theory/theories/conjectures/D4inf3.v:107` `uniquely_hamiltonian` —
  GTBase.common's `hamiltonian` (`base/theories/common.v:67`). Different carrier and
  different notion (spanning double ray, not Hamilton cycle). **Name clash**: the same
  identifier is defined with a different meaning at
  `hamiltonicity-theory/theories/conjectures/U2.v:221`. Rename one of the two.
- `infinite-graph-theory/theories/conjectures/D4inf4.v:43` `strongly_maximal_matching` —
  `matching` (coq-graph-theory `connectivity.v`). The library notion is `sgraph`-only;
  hypergraph matchings are new. Keep.
- `infinite-graph-theory/theories/foundations/igraph.v:68,72,76`
  `Kedge_coloring` / `sym_coloring` / `exact_coloring` — `coloring` (`coloring.v`).
  Different object: the library's `coloring` is a partition of an `sgraph`'s vertices,
  these are edge colourings of K_omega. False positives of the suffix rule; keep.

Not flagged by the suffix rule:

- `D4inf3.v:92` `regular (r : nat) (G : iGraph)` **shadows** base's
  `regular (G : sgraph) (d : nat)` (`base.v:52`) — same name, different type *and*
  argument order. Rename to `iregular` (WP6).
- `D4inf3.v:90` `locally_finite` vs `D4inf4.v:138` `d_locally_finite` — the same notion
  on the two carriers, spelled twice.
- `infinite-graph-theory/theories/foundations/igraph.v:152` `K4_free` **shadows**
  coq-graph-theory's `K4_free` (`minor.v`). This is not merely cosmetic: see *Other*
  below, it currently breaks the package build.
- `D4inf2.v:19` `iIso` duplicates the role of the library `diso` on the `iGraph`
  carrier; `D4inf4.v:94` `dautomorphism` and `hamiltonicity-theory/U2.v:75`
  `graph_automorphism` are the same notion on two carriers.

### Suspected unfaithful or proxy encodings

1. `opg:highly_arc_transitive_two_ended_digraphs` (`D4_unblocked.v:103`) — **wrong object
   / too strong (refutable)**. Three defects. (a) `d_tile A B` is *vacuous beyond
   nonemptiness*: its third conjunct `darc x y \/ darc y x \/ (~ darc x y /\ ~ darc y x)`
   is a classical tautology, so the hypothesis says only "A and B are nonempty" — the
   notion of *tile* is not captured at all. (b) The conclusion renders "is a disjoint
   union of complete bipartite graphs" as the single complete-bipartite condition,
   strictly stronger. (c) `d_two_ended` asserts only the existence of one forward and
   one backward ray, not that the digraph has exactly two ends. Together the statement
   claims that in any such digraph *any* two nonempty vertex classes are completely
   joined, which is refutable. Corpus leg already `blocked`; needs a real re-encoding.
2. `opg:characterizing_aleph_0_aleph_1_graphs` (`D4_unblocked.v:59`) —
   **vacuous-looking**. `exists Characterized : iGraph -> Prop, forall G,
   Characterized G <-> aleph0_aleph1_graph G` is provable in one line by instantiating
   `Characterized := aleph0_aleph1_graph`; the statement has no content. Secondary
   proxy: "degree aleph_1" is rendered as "neighbourhood does not inject into nat"
   (uncountable), which matches aleph_1 only under CH. Corpus leg already `blocked`.
3. `opg:strong_matchings_and_covers` (`D4inf4.v:79`) — **too strong (refutable)**.
   Nothing forbids an edge with no incident vertex. With `k = 0`, `hedge_le 0 e` forces
   every edge to be empty, and then `hcover X` (`forall e, exists v, X v /\ hinc e v`)
   is unsatisfiable as soon as one edge exists: the one-edge hypergraph with empty
   incidence refutes the row. Suggested WP6 fix: add `forall e, exists v, hinc e v`
   (or `1 <= k`) as a guard. Corpus leg is `done` — should be revisited.
4. `opg:universal_highly_arc_transitive_digraphs` (`D4inf4.v:176`) — **too strong,
   deliberate**. The existential carries three extra non-vacuity guards (`d_has_arc`,
   `d_infinite`, `d_no_sink_source`) absent from the source question, so a positive
   answer to the formal row is harder than a positive answer to the source. Documented
   in the block; keep, but it is a formal strengthening.
5. `opg:coloring_the_odd_distance_graph` (`D4inf5.v`) — **too strong, two labelled
   proxies** (carrier + reading). (i) "χ = ∞" is rendered as "finite subgraphs have
   unbounded chromatic number", the choice-free direction (the converse is
   De Bruijn–Erdős). (ii) The plane is rendered by an arbitrary `rcfType`, since
   colourings are second-order and Tarski transfer does not apply. Corpus leg `partial`,
   correctly.
6. `opg:infinite_uniquely_hamiltonian_graphs` (`D4inf3.v`) — **proxy**. The topological
   Hamilton *circle* of the source is replaced by a spanning *double ray*; faithful
   inside the co-assumed locally-finite one-ended class, not in general. Corpus leg
   `partial`, correctly.
7. `opg:counting_3_colorings_of_the_hex_lattice` (`D4doa.v`) — **too weak /
   different question**. "Find the limit" becomes "the limit exists" (Cauchy form); the
   value is never pinned, so a proof of the row would not answer the source. The root is
   quantified by `s ^+ |V| = count` rather than constructed, which is harmless (in an
   `rcfType` the nonnegative root is unique). Corpus leg `done`; consider `partial`.
8. `opg:unfriendly_partitions` (`D4inf1.v`) — **too strong (mildly)**. `countable_graph`
   means "the vertex type injects into nat", so finite graphs satisfy the hypothesis
   too, while the source says "countably infinite". Harmless (finite graphs do have
   unfriendly partitions) but formally a strengthening.
9. `opg:end_devouring_rays` (`D4inf3.v`) — the source's "countable END" is guarded as
   "countable GRAPH", again a strengthening of the hypothesis (hence a weakening of the
   statement). The end is handled through a representative ray rather than as an
   equivalence class — faithful, but worth recording.
10. `opg:unions_of_triangle_free_graphs` (`D4inf1.v`) and `opg:seymours_self_minor_conjecture`
    (`D4inf2.v`) — checked, **no defect found**. In particular `proper_witness` has
    teeth (the identity model satisfies none of its three disjuncts) and the
    `infinite_graph` guard is load-bearing (without it the row is refutable on finite
    graphs).

### Other

- **Reverse coverage gap.** Two OPG rows whose `repo` is `infinite-graph-theory` have no
  definition anywhere in the tree: `opg:hamiltonian_cycles_in_line_graphs_of_infinite_graphs`
  and `opg:hamiltonian_cycles_in_powers_of_infinite_graphs` (both `legs.statement =
  partial` in the manifest, both with `formal_name` set). This is the `12/14 rows
  covered` line of the gate for this package. Either the statements are missing or the
  manifest legs are wrong.
- **Build breakage, unrelated to the doc blocks.** `infinite-graph-theory` currently
  fails to compile at `infinite-graph-theory/theories/conjectures/grounding_D4inf1.v:59`
  with `The term "Komega" has type "iGraph" while it is expected to have type "sgraph"`.
  Cause: the in-progress WP4b edit to `base/theories/base.v` adds
  `From GraphTheory Require Export … minor …`, so coq-graph-theory's
  `K4_free : sgraph -> Prop` now shadows `igraph.v`'s `K4_free : iGraph -> Prop` in
  files that import base after igraph. All seven *conjecture* files of the package
  (the ones carrying the new doc blocks) compile; the failure is in a grounding file.
  Fix belongs to WP4b: qualify or rename one of the two `K4_free`s.
- `D4doa.v` header (lines 15–24) mentions an area-local primitive `converges` that no
  longer exists (the row uses `persite_cauchy`). Comment-only staleness.

## hamiltonicity-theory

*(WP4 doc-block pass, 10 targets in `U2.v` (9) and `X5.v` (1); 0 orphans.
Gate: `10 target(s), 10 documented, 0 error(s); reverse coverage: 10/10`.)*

### Duplicated vocabulary

From `check_statement_docs.py --warnings` (5):

- `hamiltonicity-theory/theories/conjectures/U2.v:43` `hamiltonian_path` —
  **byte-identical** to GTBase.common's `hamiltonian_path` (`base/theories/common.v:71`).
  Straight deletion + base import (WP6).
- `hamiltonicity-theory/theories/conjectures/U2.v:48` `hamiltonian_cycle` —
  **byte-identical** to GTBase.common's `hamiltonian_cycle` (`common.v:62`).
- `hamiltonicity-theory/theories/conjectures/U2.v:53` `is_hamiltonian` — same body as
  GTBase.common's `hamiltonian` (`common.v:67`), only the name differs.
- `hamiltonicity-theory/theories/conjectures/U2.v:61` `cycle_edges` — no exact library
  counterpart (the edge set *of a cycle seq*), but it sits in the `E(G)` /
  `GTBase.common.edge_set` family and would be the natural place for an
  `edge_set`-valued lemma. Keep for now.
- `hamiltonicity-theory/theories/conjectures/U2.v:221` `uniquely_hamiltonian` — new
  notion; **name clash** with `infinite-graph-theory/theories/conjectures/D4inf3.v:107`
  (different carrier, different meaning).

Not flagged by the suffix rule (the rule does not fire on a bare `edge_set`):

- `hamiltonicity-theory/theories/conjectures/U2.v:258` `edge_set` — **byte-identical**
  to GTBase.common's `edge_set` (`base/theories/common.v:34`), which additionally ships
  `edge_setE : edge_set G = E(G)`. Highest-value deletion in this package.
- `hamiltonicity-theory/theories/conjectures/U2.v:112` `line_graph` — base owns a
  `line_graph` on multigraphs (`base.v:190`); this is the `sgraph` analogue under the
  *same name*. Either rename, or promote the `sgraph` version to base beside it.
- `hamiltonicity-theory/theories/conjectures/U2.v:75,78` `graph_automorphism` /
  `vertex_transitive` — no library counterpart, but the same notions are re-spelled as
  `dautomorphism` in `infinite-graph-theory/D4inf4.v:94`; a `GTBase.common` candidate.
- `hamiltonicity-theory/theories/conjectures/U2.v:134` `cayley_graph` /
  `U2.v:138` `symmetric_set` — the `sgraph` Cayley construction; `homomorphism-theory/U3.v:191`
  builds the *same* thing on group powers (`pcayley`, `pconn_set`). Two areas now need
  Cayley graphs, so this meets the WP4b "promote to `common.v`" bar.

### Suspected unfaithful or proxy encodings

1. `opg:hamiltonicity_of_cayley_graphs` (`U2.v`) — **too weak**. The literal source is
   "Is every Cayley graph Hamiltonian?"; the row adds three hypotheses (`2 < #|gT|`,
   `symmetric_set S`, `<<S>> = [set: gT]`). They pin the meaningful Lovász/Babai form
   and are documented in the block, but a proof of the row would not settle the literal
   question. Also: the identity may lie in `S` (harmless, it contributes no edge).
2. `opg:hamiltonian_paths_and_cycles_in_vertex_transitive_graphs` (`U2.v`) — only the
   *path* half of the row title is formalised. That matches the row's single source
   proposition ("Does every connected vertex-transitive graph have a Hamiltonian
   path?"), so it is faithful to the corpus text, but the row's *title* also promises
   cycles. Guard `0 < #|G|` added (excludes the empty graph). Severity: minor / too weak.
3. `opg:hamiltonian_cycles_in_line_graphs` (`U2.v`) — **too weak**. The body quantifies
   over `line_graph G` for a *simple* `G`, not over abstract 4-connected line graphs;
   line graphs of multigraphs (the usual setting of this conjecture) are out of scope.
4. Rows 5/7/8 (`decomposing_the_prism_of_a_3_connected_cubic_planar…`,
   `every_prism_over_a_3_connected_planar_graph_is_hamil…`, `barnettes_statement`) state
   planarity as `wagner_planar` (no K5 and no K3,3 minor). By Wagner's theorem this is
   exactly planarity, so it is **faithful**; what it does not give is an embedding, so
   Barnette's usual polytopal phrasing ("simple 3-polytope with even faces") is not
   expressible. No defect, recorded for WP6 when the embedding layer is generally
   available (row 6 already uses it via `toroidal`).
5. `arxiv:1608.07568#00` (`X5.v`) — checked, **no defect found**. The cleared bound
   `4*L <= 5*n + n_2 - 4` uses truncated `nat` subtraction, but `k_connected G 2` forces
   `#|G| > 2`, hence `5*n >= 15 > 4` and the subtraction never truncates. `#|G| = n` is
   a redundant binder (n is determined by G) but harmless. NB the conjecture has since
   been PROVED (Wigal–Yoo–Yu, arXiv:2112.06278); the manifest `status` is `solved`, and
   the file states it only.
6. Degenerate-size sweep: `hamiltonian_cycle G c` is unsatisfiable for `#|G| ∈ {1,2}`
   (`not_hamiltonian_K1` in `base/theories/common.v`). Every row concluding
   `is_hamiltonian G` here guards `G` with `k_connected G 3` or `k_connected G 4`, which
   force `#|G| > 3` resp. `> 4`, so no row is accidentally false on tiny graphs.
   Checked, no defect.

### Other

- `U2.v` rows 5 and 7 differ only in the cubicity hypothesis and the conclusion
  (decomposition vs single Hamilton cycle); row 5 implies row 7 on cubic graphs. A
  candidate `implications_U2.v` edge if the corpus records the relation.
- `U2.v` is the only conjecture file in the three packages that imports the topological
  embedding layer (`Topological.foundations.embedding`, for `toroidal`); worth keeping
  in mind when the planarity rows are migrated off `wagner_planar`.

## graph-theory-misc

Doc-block pass (plan WP4) over the 67 previously undocumented statement targets of
`graph-theory-misc/theories/conjectures/` (D7, U13, implications_U13, X14, X20, X29, X37-X41,
X55, X62, X74, X77, X80, X82, X87, X89, X91, X94, X99, X101, X102, X110, X113, X114, X116,
X128, X139, X141, X144-X146, X156, X163, X165, X167-X169, X171, X172, X182, X197, X205, X208,
XE1, XE2).  Every `English statement:` below was written by back-translating the Rocq body and
then compared with the corpus `statement_text`/`context_text`; the items recorded here are the
places where the two disagree, plus the local vocabulary that duplicates a library/GTBase
notion.  No Rocq code was changed.

### Duplicated vocabulary

- `edge_set` (coq-graph-theory / GTBase `common.v` edge-as-2-set vocabulary) — six identical
  local copies, all `[set e | exists x y, x -- y && e == [set x;y]]`:
  `X102.v:32 x102_edge_set`, `X14.v:11 x14_edge_set`, `X20.v:23 x20_edge_set`,
  `X37.v:11 x37_edge_set`, `X38.v:11 x38_edge_set`, `X77.v:11 x77_edge_set`.
  GTBase already has `fg_edges`/`graph_edge_set` (`finite_graph.v`, `graph_metric.v`), used by
  X167/X168/X172 — the six copies should migrate there.
- `edges` — `U13.v:46 n_edges` (edge count; GTBase `fg_edge_count`),
  `X14.v:26 x14_path_edges` and `X172.v:11 x172_path_edges` (edges of a vertex sequence; one
  shared helper would do), `X77.v:15 x77_separates_edges` (name-only collision, a genuine local
  notion).
- `cycle` (MathComp `ucycle`, GTBase girth vocabulary) — `U13.v:65 induced_cycle`,
  `U13.v:70 has_induced_cycle`, `X113.v:31 x113_is_cycle`, `X29.v:40 x29_has_induced_cycle`,
  `X91.v:25 x91_consecutive_in_cycle`, `X91.v:28 x91_induced_cycle`, `XE1.v:12 xe1_rel_cycle`.
  `x113_is_cycle` and `xe1_rel_cycle` are literally `ucycle r c /\ 2 < size c`; the induced
  variants (U13, X29, X91) differ in how chord-freeness is expressed and should be unified.
- `path` (coq-graph-theory `pathp`/`upath`, MathComp `path`) —
  `X114.v:19 x114_consecutive_in_path`, `X116.v:27 x116_ST_path`, `X14.v:29 x14_genuine_path`,
  `X14.v:44 x14_rainbow_path`, `X146.v:21 x146_A_path`, `X39.v:21 x39_xy_path`,
  `X91.v:11 x91_consecutive_in_path`, `X91.v:14 x91_induced_path`, `X91.v:38 x91_avoidable_path`.
  `x116_ST_path`, `x39_xy_path` and `x146_A_path` share the same `uniq p && path (--) x q`
  skeleton; `x114_induced_path_between` and `x91_induced_path` are the same induced-path notion.
- `tree` (coq-graph-theory `is_tree`) — `X167.v:14 x167_spanning_tree`,
  `X168.v:16 x168_spanning_tree` (byte-identical to each other), `X169.v:18 x169_clique_tree`
  (a tree decomposition with clique bags; cf. `x27_tree_decomposition` in minor-theory and
  `x102_tree_alpha_at_most`).
- `connected` (coq-graph-theory `connected`) — `U13.v:297 externally_connected` and
  `implications_U13.v:59 externally_connected` (identical copies; a multistage-network notion,
  name-only collision), `X169.v:38 x169_token_sliding_connected` (name-only collision).
- `regular` (GTBase `regular`) — `U13.v:290 stage_regular` and
  `implications_U13.v:54 stage_regular` (identical copies of a bipartite-stage notion).
- `tournament` — `D7.v:382 is_tournament` (a genuine duplicate of the `tournament` notion that
  WP4b plans for `base/theories/common.v`), `D7.v:395 enc_tournament` (name-only collision, an
  instance encoding).
- `clique` — `U13.v:73 is_max_clique` (clique of size `omega`; no library counterpart yet).
- `matching` — `X14.v:15 x14_matching` (pairwise disjoint edges; duplicates
  `GraphTheory.connectivity.matching`, which `base.v` does not yet re-export).
- `forest` — `X74.v:14 x74_induced_linear_forest` (`is_forest` plus degree at most 2; the
  "linear forest" notion is a candidate for `common.v`).
- `colouring` — `X14.v:35 x14_proper_edge_colouring` (proper edge colouring; GTBase has
  `chromatic_index` but no edge-colouring predicate).
- `complete` — `X114.v:82 x114_np_complete` (name-only collision with `complete n`).
- `conn` — `X89.v:15 x89_conn` (`connect (restrict A (--))`; a restricted-connectivity helper).

Cross-file duplication not caught by the suffix warning: `X113.v`, `X116.v`, `X146.v`, `X39.v`
and `X20.v` each carry their own copy of the closed-ball fixpoint
(`x113_ball`, `x116_ball`, `x146_ball`, `x39_ball`, `x20_ball`) while GTBase already provides
`ball` and `graph_dist`; `X128.v` and `X139.v` each carry their own copies of
`poly_eval`/`radius_at_most`/`shallow_minor_model`/`grad_at_most`; `X144.v` and `X41.v` each
carry their own `complete_between`/`anticomplete_between`/`pure_pair`.

### Suspected unfaithful or proxy encodings

- `studies:std_esperet_raymond_conjecture_polynomial_expansion` (`X139.v:51`) —
  `x139_strong_reach_set` drops the requirement that the witnessing length-`<= r` path have all
  internal vertices ordered after `v`, so what is bounded is the backward `r`-ball
  (`col(G^r)`), not `scol_r`.  Severity: too strong.  (Row leg already `blocked`.)
- `studies:std_fitzpatrick_howell_messinger_pike_subadditivity` (`X141.v:36`) — the source
  parameter `z` is the deterministic ZOMBIE number; the file encodes the ZERO FORCING number.
  Severity: wrong object.  (Row leg already `blocked`.)
- `arxiv:1408.4257#00` (`X156.v:43`) — the hypothesis `forall N, exists n, N <= n /\ N <= f n`
  says `f` is unbounded, whereas the conjecture assumes `f` tends to infinity; the weaker
  hypothesis makes the statement false (an `f` dipping to 0 infinitely often forces certificate
  diameter 0 there).  Severity: too strong.  (Row leg already `blocked`.)
- `arxiv:1604.07976#00` (`X167.v:34`) — extension complexity is not modelled: the record fields
  `x167_accepts_tree` / `x167_rejects_non_tree` have conclusion `True` and the only real field
  is `#|ineq_index| <= facets`, satisfied by an empty index.  Severity: vacuous-looking.
  (Row leg already `blocked`.)
- `arxiv:1604.07976#01` (`X168.v:35`) — same defect as X167, on the minor-closed variant.
  Severity: vacuous-looking.  (Row leg already `blocked`.)
- `arxiv:1605.00442#00` (`X169.v:54`) — `x169_ts_step` never requires the intermediate sets of a
  slide sequence to be stable, so the decided predicate is not TS_k connectivity of independent
  sets.  Severity: wrong object.  (Row leg already `blocked`.)
- `arxiv:1709.09050#02` (`X197.v:43`) — the minimality clause of `x197_capture_time` is relative
  to the starting position `C0` that the existential just chose, while `capt_3(G)` minimises
  over starting positions; a deliberately bad `C0` witnesses a large `t`.  Severity: too weak.
  (Row leg already `blocked`.)
- `arxiv:1802.05582#01` (`X205.v:44`) — the `rounds` argument of
  `x205_randomized_local_algorithm` is a phantom parameter: it occurs in the type signature and
  in the logarithmic bound but in none of the record's fields, and `x205_output` carries no
  locality constraint, so no round complexity of a distributed algorithm is expressed.
  Severity: wrong object / vacuous-looking.  (Row leg already `blocked`.)
- `studies:std_conlon_fox_sudakov_sparse_linear_conjecture` (`X41.v:29`) — NEW FINDING, row leg
  is `done`.  The two sides of the pure pair get different bounds: the `B` clause is the correct
  linear `eps_den * #|B| >= eps_num * #|G|`, but the `A` clause is
  `eps_den^eps_den * #|A|^eps_den >= eps_num^eps_den * #|G|^eps_num`, i.e.
  `eps_den * |A| >= eps_num * |G|^(eps_num/eps_den)`, a SUBLINEAR bound whenever
  `eps_num < eps_den`.  The source asks for a pure `(eps|G|, eps|G|)`-pair, both sides linear.
  Severity: too weak.  Likely a copy of the near-linear template used in `X144.v` (where the
  `n^(1-o(1))` exponent form is correct).

### Other

- `studies:std_chen_chv_tal_conjecture` (`X55.v:35`) and `studies:std_chen_chv_tal_conjecture_146`
  (`X110.v:14`) have byte-identical bodies (the `2 <= #|V|` guard the second row is named for is
  already present in the first).  Two corpus rows, one mathematical statement; a candidate for an
  alias decision, or at least for an `implications` equivalence edge.
- `studies:std_bounded_tree_independence_number_conjecture_dall` (`X102.v:58`) — the corpus text
  says "if (and only if)"; the Rocq body is the full biconditional.  Also,
  `x102_subdivided_multiclaw` approximates "subdivided multiclaw" by three properties (forest,
  subcubic, at most one branch vertex per connected part) rather than by a construction from a
  star, and the "finite class" is a `finType`-indexed family, so the three witnesses need not be
  distinct.
- `arxiv:1606.06011#00` (`X171.v:24`) and `arxiv:1606.06011#01` (`X172.v:54`) encode "a finite
  set of exceptional graphs" by an order bound (only graphs with more than `B` vertices are
  constrained).  For X171 this is formally weaker than the source, which excludes a fixed finite
  set `F0` but constrains every other graph, small ones included.
- `arxiv:1612.07540#00` (`X182.v:15`) states the POLYNOMIAL version of the open problem, which
  has since been settled affirmatively (Kozik-Micek-Trotter 2019 `O(h^6)`, Gorsky-Seweryn 2021
  `O(h^3)`); only the LINEAR version remains open.  The statement as written is now a theorem —
  worth re-scoping in a later wave.
- `opg:approximation_ratio_for_maximum_edge_disjoint_paths_problem` (`D7.v:241`) — the source
  poses a two-branch question; encoding it as a disjunction is a classical tautology (the
  hardness branch's constant ratios are a subfamily of the algorithm branch's `o(sqrt n)`
  ratios), so the body deliberately selects the improvement branch only.  Its specification is
  also the value-estimation form (no routing witness demanded).  Both documented in `Notes:`.
- `opg:complexity_of_the_h_factor_problem` (`D7.v:348`) carries two guards absent from the source
  text but needed to keep the statement open rather than refutable: `H` connected on at least
  four vertices (K1 and K2 are in P), and `a < b`, i.e. `0 < c < 1` (at `c = 1` the instance
  class is empty).
- `opg:finding_k_edge_outerplanar_graph_embeddings` (`D7.v:530`) uses a documented proxy for
  k-edge-outerplanarity (a planar graph with an edge-layering into outerplanar levels); the
  faces / outer-boundary definition needs the embedding API (gate G2).
- `opg:a_gold_grabbing_game` (`U13.v:599`) — the corpus proposition is a Problem ("find optimal
  strategies"), rendered as the existence of a value function plus an attaining move function
  satisfying the Bellman recursion.  A modelling decision, not a claim of the source.
- `studies:std_chudnovsky_seymour_trotignon_question_on_subcubi` (`X114.v:96`) uses the D7
  relational complexity layer (`problem`/`in_NP`/`NP_hard` with abstract cost bounds, no machine
  model) — the corpus-standard proxy, weaker than a machine-model NP-completeness claim; the
  induced-subdivision model is replicated byte for byte from
  `extremal-graph-theory/theories/conjectures/X98.v` because `graph-theory-misc` does not import
  that package (a second copy to reconcile in WP6).
- Several rows state their extremal parameters RELATIONALLY (`is_book_thickness`,
  `is_pebbling_number`, `weighted_chromatic_number`, `weighted_clique_number`, `fas_opt`,
  `edp_opt`, `x89_max_quartet_distance`, `x141_zero_forcing_number`) and are therefore
  conditional on the minimum/maximum being realized.  Harmless on finite graphs but worth a
  shared `is_least`/`is_greatest` helper in `base/theories/common.v`.

## topological-graph-theory

WP4 doc-block pass over the 32 undocumented targets of `topological-graph-theory/theories/`
(all in `theories/conjectures/`; `theories/foundations/` holds no statement target).  Gate after
the pass: `32 target(s), 32 documented, 0 error(s); reverse coverage 28/28`.  The package is
dominated by crossing numbers, surface embeddings and genus, so most rows rest on one of four
proxy layers: `theories/foundations/crossing.v` (split-planarization crossing number),
`theories/foundations/crossing_genus.v` (its genus refinement),
`theories/foundations/embedding.v` / `signed_embedding.v` (orientable and signed rotation
systems), `theories/foundations/geometry.v` (straight-line drawings over an `rcfType`), and
`base/theories/surface.v` (Euler genus from a rotation system).  Each doc block names the proxy it
uses; the entries below are what a reader should not have to rediscover.

### Duplicated vocabulary

- `topological-graph-theory/theories/conjectures/D3D6_unblocked.v:181` `proper_minor` — duplicates
  coq-graph-theory's `minor` (GraphTheory/minor.v); it is `minor G H /\ #|H| < #|G|`, i.e. a
  *vertex-count*-proper minor, which is weaker than the usual proper-minor relation (edge deletions
  do not change the vertex count).  If promoted, it belongs in `base/theories/common.v` next to
  `minor`, with the intended strictness fixed.
- `topological-graph-theory/theories/conjectures/X158.v:11` `x158_edge_set` — duplicates the
  `edge_set` notion listed for `base/theories/common.v` (WP4b item 2); identical shape to the
  `x15_edge_set` / `x5_edge_set` copies in packing-theory.
- `topological-graph-theory/theories/conjectures/X158.v:19` `x158_nested_edges` — flagged by the
  gate against `edges`; it is genuinely new (queue-layout nesting), but it is built on the local
  `x158_edge_set` and on `index` into a vertex enumeration, both of which should come from the
  shared layer.
- `topological-graph-theory/theories/conjectures/X23.v:11` `x23_genuine_path` — duplicates
  MathComp's `path` plus `uniq` (and coq-graph-theory's `Path`/`upath` in `sgraph.v`); it is
  literally `uniq p /\ path (--) x q` on a non-empty list.
- `topological-graph-theory/theories/conjectures/X23.v:17` `x23_nonrepetitive_colouring` — flagged
  against `colouring`; the colouring part is standard, only the square-free condition is new.  The
  nonrepetitive (Thue) chromatic number is wanted by chromatic-theory too, so this is a
  `base/theories/common.v` candidate rather than a local notion.

Not caught by the gate's suffix heuristic, but the same kind of item:

- `X138.v:11,14,17` `x138_embeddable_on_surface`, `x138_clustered_two_colourable`,
  `x138_clustered_two_colourable_with_clustering` are pure one-line aliases of
  `surface_embeddable`, `clustered_chromatic_at_most` and `clustered_colouring`
  (`base/theories/surface.v`).  They add nothing and should simply be dropped.
- `implications_U13.v:70,75` re-declare `k_degenerate_on` / `k_degenerate`, which were promoted to
  `base/theories/base.v` (and which `U13.v` now takes from there).
- `X103.v:13-41` re-implements the orientation-determinant / segment-intersection vocabulary of
  `theories/foundations/geometry.v` over `Z` instead of reusing it over an `rcfType`.
- `D3cr.v:63` `hypercube` is already tagged `@MOVE-to-base` in the source; it is a generic graph
  family (cartesian power of `'K_2`, not base's distance `graph_power`).
- `D6emb.v:73,79,83` `antiprism` / `is_prism` / `is_antiprism` are deliberately local (tied to the
  positive-curvature classification); recorded here only so the decision is not re-litigated.

### Suspected unfaithful or proxy encodings

`D3D6_unblocked.v` (five "legacy blocked OPG rows") is the worst offender: every one of its five
statements is built on a record whose semantic fields are free or tautological, so each is either
classically false or empty of content.  These are placeholders, not encodings.

- `opg:3_colourability_of_arrangements_of_great_circles` — **wrong object** (and refutable).
  `great_circle_arrangement` is a graph plus an uninterpreted `Prop`; instantiating it with
  `gca_graph := 'K_4`, `gca_general_position := True` falsifies the statement.  No sphere, no
  circles, no 4-regular planar arrangement graph.
- `opg:are_different_notions_of_the_crossing_number_the_same` — **wrong object / vacuous-looking**.
  `pair_crossing_drawing G n` is inhabited for every `G` and every `n` (its only content is a
  natural equal to `n`), so `pair_crossing_number G m` holds for all `m`; with a planar `G`
  (`is_crossing_number G 0`) the body forces `m = 0` for every `m`, i.e. the statement is
  classically false.
- `opg:drawing_disconnected_graphs_on_surfaces` — **wrong object** (refutable).  Both fields of
  `surface_drawing` are free: `sd_crossings := 0` (hence optimal) with
  `sd_component_image := fun _ _ => True` satisfies the hypothesis and kills the conclusion.
  Separately, "disjoint union of `G_1` and `G_2`" is weakened to an arbitrary vertex bipartition.
- `opg:obstacle_number_of_planar_graphs` — **wrong object / vacuous-looking**.  The
  `obstacle_visibility` field is the tautology `x != y -> (x -- y) \/ ~ (x -- y)`, so
  `obstacle_representation G k` is inhabited for every `G` and every `k` (including `k = 1`); the
  first conjunct is therefore false and the whole statement is classically false.  The integer
  point placement is never constrained.
- `opg:consecutive_non_orientable_embedding_obstructions` — **vacuous-looking / wrong object**.
  `nonorientable_embedding G g` is inhabited for every `G`, `g` (free `noe_scheme := 0`), so
  `embeds_nonorientable` is universally true and no minor-minimal obstruction can exist: the
  statement is false for reasons unrelated to the mathematics.  Non-orientable embeddability is not
  modelled; `signed_embedding.semb_in_genus` is itself documented there as *not* being "embeds in
  `N_k`".
- `studies:std_expected_number_of_faces_of_random_embeddings_co` (`X140.v`) — **vacuous**
  (already recorded BLOCKED by the 2026-07-17 audit, `meta/BLOCKED_RETARGETING_AUDIT.md`).
  `x140_orientable_embedding` carries a *free* `x140_faces : nat` and a meaningless
  `x140_rotation_system : edge G -> bool`; taking a one-point index type and `0` faces makes the
  inequality trivially true.  "Uniformly random" and "expected" are replaced by an arbitrary finite
  index type with an averaged sum.
- `arxiv:1608.07680#02` (`X176.v`) — **wrong object** (BLOCKED, same audit).  The paper's `f_s(k)`
  is the **maximum** of `cr(cone G)` over graphs with `cr(G) = k`; `x176_simple_cone_crossing_value`
  pins the value by `forall H m, is_cr H k -> is_cr (cone H) m -> n <= m`, i.e. the **minimum** —
  the wrong extremum, so the quantity constrained is not `f_s`.  Compounded by the
  split-planarization crossing proxy and by an integer approximation of `sqrt(2) k^(3/4)`.
- `arxiv:1710.11281#00` (`X202.v`) — **too weak, and too strong where it is not weak** (BLOCKED,
  same audit).  The two-sided `c(g) = g^{1/2+o(1)}` becomes the one-sided
  `x202_cop_number_genus_window`, dropping the `g^{1/2-eps}` lower bound entirely; what survives is
  not the conjectured upper bound but the stronger `limsup c(g)^2/(g+1) <= 1`.  The non-orientable
  half `ec(g)` is absent: `surface_embeddable` is the orientable rotation-system Euler genus of
  `base/theories/surface.v`.
- `opg:the_crossing_number_of_the_complete_bipartite_graph`, `opg:the_crossing_number_of_the_complete_graph`,
  `opg:crossing_numbers_and_coloring`, `opg:the_crossing_number_of_the_hypercube`,
  `opg:crossing_sequences` — **proxy** (acknowledged PARTIAL).  All five use the
  split-planarization crossing number of `theories/foundations/crossing.v` (resp. its genus variant
  `crossing_genus.v`), which the #5/#6 readback review found to lack the local rotation/alternation
  data at each new degree-4 crossing vertex; equality with the drawing crossing number is not
  validated, so the encoded quantity is only known to be *a* planarization invariant.  Two extra,
  smaller items: the Guy row relies on the unenforced arithmetic fact that the Guy product is
  divisible by 4 (`%/ 4` would silently truncate otherwise), and `opg:crossing_sequences` formalizes
  only the orientable half of the source's "orientable (non-orientable, resp.)" pair.
- `opg:grunbaums_conjecture` (`D6emb.v`) — **stale corpus status, faithful encoding**.  The general
  orientable form encoded here was refuted by Kochol (2009); the corpus row is still recorded open.
  Orientability is load-bearing: quantifying over `emap` instead of `embedding` would make the row
  classically false via `K_6` in the projective plane (Petersen dual).
- `opg:the_circular_embedding_conjecture` (`D6emb.v`) — **guard-dependent proxy**.
  `circular_emap` is strictly weaker than "every face boundary is a cycle" on graphs with degree-1
  vertices (`K_2` satisfies it yet has no cycle); the `k_connected G 2` hypothesis is what makes it
  exact.  Any reuse of `circular_emap` without a min-degree-2 guard would be unfaithful.
- `opg:what_is_the_largest_graph_of_positive_curvature` (`D6emb.v`) — **too weak (by design)**.
  The source asks *which* graph is largest; the encoding asserts only that a uniform vertex bound
  exists over the class.  That is the natural `Prop`-valued reading, but it does not answer the
  problem.  Note also that "planar" here is a genus-0 rotation system, not `wagner_planar`.
- `studies:std_brass_et_al_simultaneous_embeddability_problem` (`X103.v`) — **too weak**.  The
  statement is an existential ("there exist two planar graphs that are *not* simultaneously
  embeddable"), and the point set is restricted to `Z * Z`; a pair with no integer common point set
  could still have a real one, so the encoded claim is a priori weaker than the source question.
  Additionally `x103_crossing_free_drawing` only forbids intersections between edges with four
  distinct endpoints, so a vertex lying inside a non-incident edge is permitted — unlike
  `geometry.straightline_planar`, which forbids it.
- `studies:std_esperet_joret_question_on_clustered_colouring_of` (`X138.v`) — **proxy**.  "Surface"
  is a natural number bounding the *orientable* Euler genus computed from a rotation system, so
  non-orientable surfaces are unreachable although the source quantifies over all surfaces.
  Triangle-freeness is written `girth_geq G 4` rather than base's `triangle_free` (equivalent for
  simple graphs, but a different notion read literally).  The quantifier order (`exists c` before
  `forall G`) is correct and was fixed by the 2026-07-17 re-encoding; it must not regress.
- `opg:large_induced_forest_in_a_planar_graph`, `opg:earth_moon_problem`,
  `opg:colouring_the_square_of_a_planar_graph`, `opg:degenerate_colorings_of_planar_graphs`
  **as re-stated in `implications_U13.v`** — **too strong**.  The file header claims the four
  definitions are verbatim copies of `U13.v`, but they have diverged: `U13.v` now uses the concrete
  `wagner_planar`, while the copies still carry the pre-G2 oracle
  `forall (is_planar : sgraph -> Prop)`, which demands the conclusion for *every* predicate,
  including degenerate ones.  Each copy is therefore strictly stronger than the statement it is
  supposed to mirror, and the edge annotation at the end of the file is stated between the strong
  copies rather than between the real rows.  Fix in WP6: re-sync the copies (or import `U13`).
- `opg:large_induced_forest_in_a_planar_graph` (`U13.v`) — **marginally too strong**.
  `#|G| <= 2 * #|S|` is `|S| >= ceil(n/2)`, whereas the source says `n/2`; the two differ for odd
  `n`.  Harmless for the conjecture's intent, worth a line in the WP6 review.

### Other

- `U13.v`'s file header still describes the pre-G2 encoding ("the planarity predicate is discharged
  into each statement as a universally-quantified oracle `is_planar`", rows "honestly marked
  `compile_blocked`").  The four statements now use `wagner_planar`, so the header is stale; only
  `implications_U13.v` still matches it.  Header-only fix (no body change) for WP6.
- `implications_U13.v` deliberately schedules **zero** verified edges: the four U13 rows are
  mutually independent open problems.  The single literature-motivated direction (degenerate
  colouring gives an induced forest on at least `2n/5` vertices, short of the `n/2` demanded) is a
  candidate annotation with a real constant gap, and must not be forced into a `Qed` theorem.
- `D3cr.v`, `D3xseq.v`, `X176.v` all consume `is_crossing_number` / `is_crossing_genus`
  relationally rather than as a total `nat`-valued `cr`.  This is deliberate (totality would need
  "every finite graph admits a finite-crossing drawing", i.e. geometry, which the layer excludes and
  which must not enter as an `Axiom`), and any WP6 rewrite must preserve it.
- `D3geo.v` quantifies the point-set row over `forall R : rcfType`.  The Tarski–Seidenberg argument
  that makes this equivalent to the real plane is spelled out in the doc block; it is load-bearing
  and would break if the quantifier were relaxed to `realFieldType`.
- The five `D3D6_unblocked.v` rows and the three BLOCKED rows (`X140`, `X176`, `X202`) are the
  natural first targets of a re-encoding wave: four of the five `D3D6_unblocked.v` statements are
  outright false as written, which is worse than being absent, since `check_milestone.py`'s
  exact-type probes could in principle close them by refutation.

## digraph-theory

116 targets documented (92 with a corpus row, 24 `No corpus row` orphans);
`python3 meta/check_statement_docs.py --ignore-baseline digraph-theory` ends with 0 errors and
reverse coverage 91/91. 42 duplicate-vocabulary warnings.

### Duplicated vocabulary

From `python3 meta/check_statement_docs.py --ignore-baseline --warnings digraph-theory`
(42 warnings), grouped by the library counterpart:

- `tree` (coq-graph-theory `sgraph.v` `is_tree` / `is_forest`, GTBase):
  `conjectures/P9.v:179 oriented_tree`, `conjectures/P9.v:181 antidirected_tree`,
  `conjectures/X2.v:101 oriented_tree`, `conjectures/generalised_wheel.v:385 wheel_tree`,
  `conjectures/grounding_two_extremal.v:107 canon_tree`,
  `conjectures/grounding_two_extremal.v:152 odd_par_tree`,
  `conjectures/two_extremal_glue.v:299 canon_tree`. `P9.oriented_tree`/`X2.oriented_tree` are two
  different encodings of the same notion (arc count `#V - 1` vs `is_forest` + `connected`).
- `forest` (`is_forest`): `conjectures/chi_bounded.v:56 oriented_forest`,
  `conjectures/heroes_dichotomy.v:40 oriented_forest` (two copies of the same definition, over
  two different local `underlying` graphs), `conjectures/path_fas.v:65 linear_forest`,
  `conjectures/two_extremal.v:217 two_extremal_digonG_forest`,
  `conjectures/two_extremal_hajos.v:349 realises_digonG_forest`.
- `connected` (`connectivity.v` `connected`/`connectedb`):
  `conjectures/P9.v:68 weakly_connected`, `conjectures/X2.v:460 weakly_connected` (two different
  encodings: `[forall ...] connect` on booleans vs a `Prop` `connect`),
  `conjectures/X179.v:18 x179_k_vertex_strongly_connected`,
  `conjectures/X179.v:24 x179_k_arc_strongly_connected`,
  `conjectures/X44.v:13 x44_p_strongly_connected`,
  `conjectures/two_extremal.v:244 three_connected_digonG_connected`.
- `conn`: `conjectures/two_extremal.v:121 local_arc_conn`, `conjectures/two_extremal.v:125
  arc_conn` (the same arc-connectivity invariant as `conjectures/sad.v`'s `arc_strong`/`lambda`
  and as `conjectures/P9.v`'s `arccut`/`karcstrong`, stated three times).
- `tournament` (this package's own `core/tournament.v` structure):
  `conjectures/X123.v:17 x123_transitive_tournament`, `conjectures/X93.v:13
  x93_t_local_tournament`, `conjectures/XE2.v:33 xe2_tournament`, `conjectures/heroes.v:104
  is_tournament`, `conjectures/heroes_dichotomy.v:52 transitive_tournament`. `X123
  x123_transitive_tournament` and `heroes_dichotomy.transitive_tournament` are the same
  definition written twice; `XE2.xe2_tournament` is a third, relation-level copy.
- `path` (`sgraph.v` `Path`/`upath`, MathComp `path`): `conjectures/X166.v:30
  x166_directed_path`, `conjectures/X179.v:27 x179_directed_path` (identical definitions, and both
  are `core/dipath.v`'s `dipath` plus an endpoint condition), `conjectures/X2.v:426 oriented_path`,
  `conjectures/X2.v:429 antidirected_path`.
- `cycle` (MathComp `cycle`/`ucycle`, `core/dipath.v` `dicycle`): `conjectures/X2.v:286
  sg_has_cycle`, `conjectures/XE2.v:15 xe2_directed_cycle`, `conjectures/two_extremal.v:356
  sym_cycle`, `conjectures/two_extremal.v:360 symmetric_odd_cycle`,
  `conjectures/two_extremal_glue.v:164 di_cycle`.
- `stable` (`dom.v` `stable`): `conjectures/X2.v:340 x2_arc_stable` — same body as
  `conjectures/classic_core.v`'s `stable`, and `conjectures/X166.v:14 x166_stable_set` is a third
  copy (in `Prop` form).
- `colouring`: `conjectures/X51.v:17 x51_majority_colouring`, `conjectures/colouring_variants.v:216
  arc_colouring`, `conjectures/sad.v:167 SAD_colouring`.
- `acyclic`: `conjectures/X92.v:27 x92_inverts_to_acyclic` (its `x92_acyclic_rel` duplicates
  `conjectures/dichromatic.v`'s `acyclicb` at relation level, as does
  `conjectures/XE2.v:18 xe2_acyclic_rel`).
- `edges`: `conjectures/XE2.v:12 xe2_uses_only_edges`.
- `minor`: `conjectures/two_extremal.v:169 sg_minor` (re-states coq-graph-theory `minor.v`'s
  `minor_rmap`, which the interop does not re-export).
- `complete`: `conjectures/X90.v:44 x90_np_complete` (a false positive of the suffix heuristic —
  complexity, not graph completeness).

Beyond the mechanical warnings, the same notion is defined more than once in this package:

- looplessness / orientedness: `two_extremal.v:loopless`, `chi_bounded.v:oriented_dg`,
  `heroes_dichotomy.v:oriented_dg`, `X2.v:x2_oriented`, `X122.v:x122_oriented`,
  `X16.v:x16_loopless`, `X19.v:x19_loopless` — seven variants of two notions.
- underlying simple graph: `chi_bounded.v:underlying` (with the `u != v` guard),
  `two_extremal.v:underlyingG` (needs an explicit `loopless` proof),
  `heroes_dichotomy.v:underlying` (on `orientedDigraph`) — three incompatible carriers for the
  same object; the three doc blocks have to name which one they use.
- in-degree: `classic_core.v:indeg`, `colouring_variants.v:indeg`, `reals_growth.v:indeg`
  (`conjectures/P9.v` already has to write `classic_core.indeg` to disambiguate).
- arc selectors / branchings: `packing.v:{real_sel,selindeg,out_branching,in_branching,
  arc_disjoint_sel}` vs `X86.v:{x86_real_sel,x86_sel_indeg,x86_out_branching_on,
  x86_in_branching_on,x86_arc_disjoint}` — a full second copy parameterised by a vertex subset.
- subdivision containment: `P9.v:subdivides`, `X2.v:contains_subdivision`,
  `X179.v:x179_directed_subdivision` — three inequivalent notions (see below).
- subdigraph containment: `P9.v:contains_subdig`, `X2.v:subdigraph_embed`,
  `unvd.v:contains_subdigraph` — three identical definitions (injective arc-preserving map).
- Eulerian: `two_extremal.v:Eulerian`, `colouring_variants.v:eulerian`, `reals_growth.v:eulerian`.
- 2-kernel machinery: `X2.v:{x2_covers1,x2_covers2,two_kernel}` is reused by `X16.v`, but
  `X16.v:x16_no_sources` duplicates `X2.v:no_sources` verbatim.

### Suspected unfaithful or proxy encodings

- `opg:monochromatoc_reachability_in_arc_colored_digraphs` →
  `conjectures/colouring_variants.v:mono_reach_or_rainbow_statement` — **wrong object**. The row's
  `statement_text` is the general Sands–Sauer–Woodrow statement (for every `k` there is `f(k)` such
  that every `k`-arc-coloured digraph has a set `S`, a union of `f(k)` stable sets, reachable
  monochromatically from every vertex). The Rocq body is the three-colour TOURNAMENT variant
  (rainbow triangle or monochromatic-reachability root). The statement that does match the row,
  `sands_sauer_woodrow_statement`, sits in the same file with no row at all. Fix: move the row to
  `sands_sauer_woodrow_statement` and give the tournament variant its own row (or fold it into
  `opg:monochromatic_reachability_vs_rainbow_triangles`, which `conjectures/P9.v` already carries
  as an alias of exactly this body).
- `arxiv:1608.03040#02` (Open Problem 1) →
  `conjectures/X45.v:majority_three_colouring_beta_statement` — **too strong**. The row asks
  whether SOME constant `beta < 1` works; the body fixes `beta = 1/2`, i.e. it restates
  `arxiv:1608.03040#00` (`majority_3col_statement`, `conjectures/colouring_variants.v`) verbatim.
  Two rows of different strength are then pinned to the same proposition, and the weaker,
  genuinely-`solved` Open Problem 1 is not formalised at all.
- `arxiv:2310.04265#03` (Conjecture 3.13) → `conjectures/twinwidth.v:conj_3_13_statement` —
  **too strong / wrong invariant**. The corpus text now reads `tww(T, p) <= f(tww(T))`; the body
  bounds the ordered twin-width by `f(omegabar T)`. During this documentation pass the row's
  `formal_name` was detached upstream (it is now `null`, statement leg back to `todo`), so the
  definition is documented as an orphan whose marker records the divergence. The body is
  untouched; re-attaching the row needs the paper adjudication.
- `arxiv:1604.02317#00` → `conjectures/X166.v:vertex_disjoint_paths_stability_two_np_complete_
  statement` — **vacuous-looking / provably false**. `x166_np_hard P` demands, for EVERY `Q` in
  `x166_in_np`, a reduction program whose output equals its input (`prun red (enc I) = enc I`) with
  `Q I -> P I`. Since the constantly-true predicate is in `x166_in_np` (take `cert_enc := fun _ _
  => True`), the clause collapses to "`P` holds on every instance", so the conjunction is refutable
  rather than open. The fourth conjunct, `... \/ ~ ...`, is also trivially true in this classical
  development (`foundations/prelude.v` imports `boolp`). Needs a genuine many-one reduction (image
  digraph, not the identity) before it means anything.
- `arxiv:1610.00876#05` (Problem 16) → `conjectures/X179.v:digraph_kappa_maderian_statement` —
  **too weak**. `x179_directed_subdivision` requires only that the internal vertices of each
  replacement path avoid branch vertices; unlike `X2.contains_subdivision` it does NOT require the
  interiors of distinct replacement paths to be pairwise disjoint, so a "subdivision" here may
  reuse internal vertices. The intended statement is strictly stronger.
- `opg:hamilton_cycle_in_small_d_diregular_graphs` →
  `conjectures/P9.v:hamilton_cycle_in_small_d_diregular_graphs_statement` (alias of
  `classic_core.jackson_hamilton_small_diregular_statement`) — **too weak (mild)**. The row says
  "indegree and outdegree at least `d`"; `diregular D d` asks for equality, a strictly stronger
  hypothesis, hence a weaker conjecture. Same reading question in
  `conjectures/X19.v:behzad_chartrand_wall_girth_regular_digraph_statement` (`r`-regular read as
  exactly `r`), where equality is the standard reading.
- `opg:splitting_a_digraph_with_minimum_outdegree_constraints` →
  `conjectures/classic_core.v:splitting_min_outdegree_statement` — **too strong (guard)**. The body
  adds `V1 != set0` and `V1 != setT`. The guard is needed (without it `V1 := setT` trivialises the
  complement clause), but it is not in the corpus text; the corpus text itself is garbled (it
  writes the hypothesis degree as `d`, leaving `f(d)` unused).
- `arxiv:1608.03040#04` (Open Problem 3) →
  `conjectures/colouring_variants.v:majority_3col_eulerian_statement` — **too strong (mild)**.
  `eulerian` keeps only the balanced-degree condition and drops connectivity, so the hypothesis is
  weaker than the classical "Eulerian digraph". Majority colouring is a local condition and a
  balanced digraph is a disjoint union of connected balanced ones, so the two readings coincide;
  worth a bridging lemma rather than a body change.
- `studies:std_bang_jensen_et_al_conjecture_f_subdivision_compl` (`conjectures/X90.v`) and
  `arxiv:1604.02317#00` (`conjectures/X166.v`) — **model-relative**. Both are only as faithful as
  the GTBase `complexity.v` cost-coupled interpreter (`prog`, `prun`, `poly_cost_on`,
  `polytime_decides_on_class`); `X90` uses a genuine many-one reduction and looks sound, `X166`
  does not (above). Any later re-encoding should share one NP-completeness vocabulary.

### Other

- **Open questions encoded affirmatively.** Several bodies encode the YES answer to a corpus
  question, so refuting the definition is answering NO:
  `P9.v:switching_reconstruction_of_digraphs_statement` (existence of a
  switching-nonreconstructible digraph on >= 12 vertices),
  `P9.v:oriented_chromatic_number_of_planar_graphs_statement` (the maximum exists and is attained),
  `X2.v:directed_kneser_existence_statement`, `X54.v:odd_dicycle_free_dichromatic_chi_bound_
  statement`, `X179.v:digraph_kappa_maderian_statement` (conjunction of the two questions).
  This is the repo convention, but it is invisible in the manifests and is recorded here.
- **Near-duplicate statements owning two different rows.**
  `X136.v:erdos_hajnal_tournament_transitive_subtournament_statement`
  (`studies:std_erd_s_hajnal_conjecture_for_tournaments`) and
  `X79.v:alon_pach_solymosi_tournament_erdos_hajnal_statement`
  (`studies:std_alon_pach_solymosi_conjecture`) are the same conjecture with the same rational-
  exponent encoding, differing only in where the witness size is quantified.
  `X45.v:majority_three_colouring_beta_statement` vs
  `colouring_variants.v:majority_3col_statement` (see above).
  `X17.v:stein_oriented_paths_strict_semidegree_statement` and
  `X2.v:semidegree_oriented_paths_statement` are the strict and non-strict semidegree thresholds of
  the same family (this pair is deliberate).
- **Misnamed constants.** `opg:hoand_reed_conjecture` carries the corpus typo, so the Rocq node is
  `P9.v:hoand_reed_statement` while the real statement lives in `packing.v:hoang_reed_statement`
  (row-less, documented as an orphan pointing at the alias). Likewise the corpus slug
  `opg:monochromatoc_reachability_in_arc_colored_digraphs` is misspelled.
  `P9.v` truncates four formal names mid-word (`..._of_order_statement`,
  `..._cyclomatic_num_statement`, `..._in_digraphs_w_statement`, `..._a_planar_oriente_statement`)
  because they are generated from a length-capped slug.
- **Header attributions disagreeing with the corpus.** `conjectures/unvd.v`'s header credits
  arXiv:2410.23566 to "Aboulker, Bang-Jensen, Bousquet, Charbit, Havet, Hörsch, Maffray, Zamora,
  *Unavoidability of digraphs*", while the corpus rows record *Blow-ups and extensions of trees in
  tournaments* by Aboulker, Havet, Lochet, Lopes, Picasarri-Arrieta, Rambaud;
  `conjectures/chi_bounded.v`'s header credits arXiv:1605.07411 to "Aboulker–Charbit–Naserasr"
  where the corpus lists seven authors. The doc blocks use the corpus attribution.
- **Aliases.** Three `P9.v` nodes are plain aliases (`hoand_reed_statement`,
  `hamilton_cycle_in_small_d_diregular_graphs_statement`,
  `monochromatic_reachability_vs_rainbow_triangles_statement`), and
  `reals_growth.v:prob6_unvd_statement` is a verbatim re-export of `unvd.prob_6`. The aliased
  definitions own no row, so they are documented as orphans that point at the alias; a later pass
  could make the manifest name the primitive instead.
- **Row-less statements worth a corpus row** (currently `No corpus row`): the whole Path-FAS family
  (`path_fas.v`, 4 targets, arXiv:2402.10782 Problem 4.4 and its reduction), `sad.v:CL1_statement`,
  `chi_bounded.v:{conj5_1605_statement,chordal_not_dichromatic_bounded_statement,avec_core_
  statement,tvec_core_statement,m3_landmark_statement}`, the four `reals_growth.v` Theta-envelope
  variants, `clique_cluster.v:conjecture_5_8_statement` (Conjecture 5.8 of arXiv:2310.04265, the
  node the corpus status semantics of `arxiv:2310.04265#07` actually cites as proved), and
  `applications/color_avoiding_tournament.v:problem_5_1_q6_n9_statement` (a PROVED resolution of
  arXiv:2512.10438 Problem 5.1 with no corpus row for the paper).
- **Build note.** `make digraph-theory` cannot run in this environment: there is no `digraph` opam
  switch (only `default`, which lacks `mathcomp-classical`), so `theories/foundations/prelude.v`
  fails on `Require Import boolp classical_sets` before any documented file is reached. The 116
  inserted blocks were instead checked by extracting them into a standalone file and compiling it
  with `rocq c` (exit 0), and `conjectures/XE2.v` — the one documented file with no `prelude`
  dependency — compiles.

## packing-theory

Pass over the 38 documented targets of `packing-theory/theories/conjectures/` (U9.v: 13 OPG rows;
U13.v: 2 OPG rows; X5.v/XE1.v: 6 `erdos:` rows; X15.v, X18.v: the `arxiv:1611.03196` family plus 2
`studies:` rows; X25.v, X26.v, X47.v, X48.v, X111.v, X155.v, X178.v: 1 row each; X15alone.v: a
second, untracked-by-`_CoqProject` copy of the two X15 rows; plus the 3 `_llm*` orphans of X15.v).
Gate: `python3 meta/check_statement_docs.py --ignore-baseline packing-theory` -> 38 target(s), 38
documented, 0 error(s), reverse coverage 33/33. Package rebuild green (`make packing-theory`), and
`fair_matching.v` / `fair_matching_edge_partition_disproved.v` still print "Closed under the global
context".

### Duplicated vocabulary

29 gate warnings (`--warnings`), plus a handful the suffix heuristic misses. Grouped by the notion
that is being re-invented:

- **Edge set of a simple graph** — the same boolean comprehension
  `[set e | exists x y, (x -- y) && (e == [set x; y])]` is copied 7 times verbatim:
  `U9.v:83 edge_setG` (not flagged: suffix `setG`), `X15.v:11 x15_edge_set`,
  `X15alone.v:20 x15_edge_set`, `X25.v:11 x25_edge_set`, `X47.v:11 x47_edge_set`,
  `X5.v:17 x5_edge_set`, `XE1.v:9 xe1_edge_set`. Library counterpart: `sgraph.sg_edge_set` (`E(G)`),
  with `GTBase.common.sg_edge_setE` / `in_sg_edge_set` as the bridging rewrites (`base/theories/
  common.v:33-53` explains why `common.v` deliberately has no `edge_set`). Note that X15.v's
  `_llm2`/`_llm3` orphan variants already use `sg_edge_set` directly, so within one file two
  spellings of E(G) coexist.
- **Derived edge sets** — `X178.v:15 x178_path_edge_set`, `X25.v:22 x25_hamiltonian_edge_set`,
  `X47.v:27 x47_copy_edge_set`, `XE1.v:62 xe1_clique_edge_set`, `XE1.v:39 xe1_image_edges`,
  `X47.v:18 x47_crossing_edges`: all would be one-liners over `sg_edge_set` (and
  `GTBase.common.del_edge_set` for the crossing/deletion ones).
- **Matching** — `X15.v:15 x15_matching`, `X15alone.v:24 x15_matching`,
  `U9.v:187 is_matching_edges` (same notion, edge-set form). Library counterpart:
  `connectivity.v matching`.
- **Perfect matching** — `X18.v:34 x18_perfect_matching`, `X25.v:15 x25_perfect_matching`
  (identical up to the name). Counterpart: `GTBase.common.perfect_matching`.
- **Triangle / triangle edge set** — `U9.v:74 is_triangle` and `X5.v:11 x5_is_triangle` are
  byte-identical, as are `U9.v:79 tri_edges` and `X5.v:14 x5_tri_edges` (neither `is_triangle` pair
  is flagged). Counterpart: `clique` (sgraph.v) with `#|T| = 3`.
- **Clique variants** — `XE1.v:16 xe1_maximal_clique`, `X178.v:32 x178_odd_semi_clique`; both build
  on `clique`/`cliqueb` and only the "maximal" wrapper is genuinely missing from the library.
- **Independent / stable set** — `X18.v:31 x18_independent_set`, `XE1.v:13 xe1_stable_set` (same
  definition, two names; neither flagged). Counterpart: `dom.v stable`.
- **Paths** — `U9.v:105 consec` + `U9.v:110 spath` + `U9.v:115 is_induced_path`,
  `X26.v:21 x26_xy_path`, `X178.v:12 x178_path_seq`: three seq-based path encodings for one notion.
  Counterpart: `sgraph.v Path`/`upath` (and `irred`/induced for the chordless variant).
- **Cycles** — `XE1.v:54 xe1_induced_cycle`, `U9.v:177 hamiltonian_cycleG` +
  `U9.v:181 cycle_edgesG`. Counterparts: MathComp `ucycle` and
  `GTBase.common.hamiltonian_cycle`/`hamiltonian` (`hamiltonian_cycleG` is literally
  `common.hamiltonian_cycle`).
- **Balls / graph metric** — `X111.v:16 x111_ball` and `X26.v:11 x26_ball` are the same `Fixpoint`,
  copied "to avoid a cross-repo import" (X111.v's own comment); `X26.v:15 x26_set_ball` extends it.
  Counterpart: the `graph_metric.v` distances listed in the WP4b base inventory.
- **Edge-connectivity** — `X47.v:21 x47_edge_connected` (cut-size form, reused by X48.v),
  `U9.v:256 edge_conn_via` + `U9.v:262 edge_conn_subset` (multigraph, walk form). Counterpart:
  `GTBase.common.k_edge_connected`.
- **Tree / forest** — `XE1.v:36 xe1_tree` is exactly `is_forest [set: T] /\ connected [set: T]`,
  i.e. `sgraph.is_tree` (which X47.v and X48.v already use). Counterpart: `is_tree`.
- **Bipartite** — `U9.v:89 del_bipartite` is "bipartite after deleting an edge set", expressible as
  `bipartite (del_edge_set S)` with base's `bipartite` and `GTBase.common.del_edge_set`.
- **Whole GTBase layer re-declared** — `X15alone.v:39 N`, `X15alone.v:41 Delta`,
  `X15alone.v:43 bipartite`, `X15alone.v:46 ceil_div` are verbatim copies of base notions, because
  that file deliberately does not import `GTBase base`. See the `### Other` entry on X15alone.v.
- **Hypercube** — `U9.v:211 hypercube` (with `hc_rel`/`hc_sym`/`hc_irrefl`) is a general-purpose
  graph family used by two U9 rows; a `common.v` candidate under the WP4b "needed by >= 2 waves"
  rule.
- **False positives of the suffix heuristic** (no action): `U9.v:130 all_but_finitely_many_regular`
  (a cofiniteness combinator, not a `regular` copy) and `X47.v:21 x47_edge_connected` /
  `X26.v:21 x26_xy_path` are flagged for `connected`/`path` although the duplication they really
  carry is the one recorded above.

### Suspected unfaithful or proxy encodings

- `arxiv:1407.5833#00` — `X155.v identifying_code_vc_dimension_approximation_dichotomy_statement`.
  **Severity: high (already `legs.statement = blocked`).** The body is
  `forall C hereditary, (A1 /\ A2) \/ (B1 /\ B2)` with `A1` and `B1` both of the form
  `exists G, C G /\ ...`; the empty class `fun _ : sgraph => False` is vacuously hereditary and
  falsifies both, so the statement is refutable as written (machine-refuted, recorded in
  `meta/BLOCKED_RETARGETING_AUDIT.md`, audit of 2026-07-17). Two further gaps: the corpus text is an
  informal survey observation about classes that *contain* graphs (the missing non-emptiness guard),
  and `x155_vc_dimension_at_most` — the notion the dichotomy is *named after* — is defined in the
  file but does not occur in the statement at all, so the body states a log-vs-polynomial dichotomy,
  not a VC-dimension one. A faithful retarget needs a non-emptiness/infinite-class guard and an
  explicit VC-dimension side condition.
- `opg:weak_saturation_of_the_cube_in_the_clique` —
  `U9.v weak_saturation_of_the_cube_in_the_clique_statement`. **Severity: medium (proxy / too
  weak).** The source is a "Determine wsat(K_n, Q_3)" problem with no proposition to prove; the
  body asserts only that the minimum exists (`forall n, 8 <= n -> exists m, is_wsat n m`), which is
  a provable well-definedness fact on a finite carrier rather than a determination of the quantity.
  Flagged as a deliberate proxy in the doc block; a value-level restatement (e.g. a closed form or
  matching bounds) would be the faithful target.
- `arxiv:1611.03196#03` — `X15alone.v bipartite_matching_underrepresentation_statement`.
  **Severity: medium (too strong / wrong row).** Unlike the X15.v definition carrying the same
  corpus name, this body additionally asserts `c <= 32 * (m + 1) ^ 3`. The corpus row only asks
  that some `c(m)` exist, so this is X15.v's orphan variant
  `bipartite_matching_underrepresentation_llm_statement` published under the Conjecture 1.15 name.
  Harmless today (both forms are proved in `theories/foundations/fair_matching.v`, and the file is
  not in `_CoqProject`), but the name/row pairing is wrong and a hash-pinned resolution must not be
  taken from this file.
- `arxiv:1507.08208#00` / `arxiv:1907.11600#00` — `X47.v`/`X48.v`
  `x47_tree_decomposition_by_copies`. **Severity: low (encoding slack).** "Partition into copies of
  T" is a `seq` of edge sets with disjointness stated as "two parts sharing an edge are equal", so a
  list may repeat one part; the number of parts is not tied to `|E(G)| / |E(T)|`. Equivalent to a
  genuine partition in the end (every part is a full copy and every edge is covered), but it is a
  set-indexed-by-a-list idiom that a `partition`-based version would state more directly.
- `arxiv:2309.07905#00` — `X26.v bounded_degree_distant_induced_menger_statement`.
  **Severity: low.** "Pairwise at distance at least d" is encoded as "the (d-1)-ball around the
  vertices of p misses the vertices of q", using truncated `d.-1`, so `d = 0` and `d = 1` collapse to
  the same (vertex-disjoint) condition instead of `d = 0` being no condition at all. The `k` paths
  are also only required to be distinct *as sequences* (`uniq paths`), not pairwise distinct as
  vertex sets — harmless for `d >= 1`, where distinct sequences with the same vertices cannot be
  distant.

### Other

- **Duplicate rows with divergent encodings.** `erdos:167` (`X5.v
  triangle_packing_transversal_statement`) and `opg:triangle_packing_vs_triangle_edge_transversal`
  (`U9.v`) are the same mathematical problem in two files: the packing is a repetition-free `seq`
  in X5.v and a `{set {set G}}` in U9.v, and only X5.v requires the transversal to consist of
  genuine edges (U9.v lets it be an arbitrary set of 2-element vertex sets, which only strengthens
  its conclusion). A WP6 pass should keep one encoding and prove the other from it.
- **X15alone.v is a scratch duplicate.** It re-declares `fair_matching_edge_partition_statement` and
  `bipartite_matching_underrepresentation_statement` (the two pinned X15 names) with its own copies
  of `N`, `Delta`, `bipartite`, `ceil_div`, is untracked by `packing-theory/_CoqProject` (so nothing
  ever compiles it), and ends with three `Print`/`About` debug commands. It nevertheless satisfies
  the doc gate, i.e. the gate scans files the build ignores. Recommendation: either wire it into
  `_CoqProject` or move it out of `theories/conjectures/`.
- **Corpus metadata oddity, `opg:jones_conjecture`.** The row is `partial` with
  `status_semantics` "proven for planar graphs (Jones); the general bound is open", but the
  conjecture itself is stated *for planar graphs* — which is exactly what `U9.v jones_statement`
  encodes. Either the status summary is about a different (general-graph) statement, or the row
  should be `done`/solved. Worth a corpus-side re-read before the row is used as a WP5 target.
- **Relational extrema everywhere.** `is_domination_number` (U13.v), `is_min_fvs` /
  `is_max_cycle_packing` / `is_wsat` (U9.v), `x111_tau` / `x111_nu` (X111.v),
  `xe1_clique_transversal_number` / `xe1_triangle_free_independence_guarantee` (XE1.v),
  `x155_identifying_code_number_at_least/at_most` (X155.v) are five different idioms for "the
  minimum/maximum is m": a `Prop`-level witness-plus-bound pair, an `[arg min_...]`, a `\max_(...)`,
  and two one-sided predicates. A shared `is_least`/`is_greatest` helper in
  `base/theories/common.v` would unify them and make the "the hypothesis pins the extremum"
  reasoning reusable.
- **`XE1.v erdos_151_statement` is conditionally vacuous.** It takes
  `xe1_triangle_free_independence_guarantee n h` as a hypothesis; for any `n` where no greatest such
  `h` exists the row says nothing. Finiteness makes `H(n)` well defined, but the fact is not proved
  anywhere, so a grounding lemma (`forall n, exists h, xe1_triangle_free_independence_guarantee n h`)
  is the natural non-vacuity witness. The same remark applies to `xe1_clique_transversal_number`.
- **`XE1.v erdos_743_statement` index shift.** The source indexes `T_2, ..., T_n` with `|T_k| = k`;
  the body indexes `'I_n` with `|T_k| = k + 1`, i.e. trees on `1, ..., n` vertices. The edge count
  still matches `|E(K_n)|` (the extra one-vertex tree has no edge), so this is faithful, but the
  shift is invisible from the body and is recorded in the doc block only.
- **Guards that carry the statement.** Several rows would be false or trivial without a
  non-obvious guard, now documented in the blocks: `connected [set: G]` in
  `domination_in_plane_triangulations_statement` (without it, disjoint triangles are genus-0
  pseudo-planar and refute the bound), `0 < #|T|` in `packing_t_joins_statement`, `0 < k` in
  `partition_of_a_cubic_3_connected_graphs_into_paths_o_statement` and `kriesells_statement`,
  `2 <= d` in the hypercube row, `8 <= n` in the weak-saturation row, and `0 < Delta G` in
  `bipartite_matching_underrepresentation_statement`. These are the first candidates for WP5
  guard-has-teeth grounding lemmas.

## minor-theory

Pass over the 31 documented targets of `minor-theory/theories/conjectures/` (U7.v: 6 OPG rows;
X5.v, X8.v, X11.v, X27.v, X42.v, X67.v, X121.v, X127.v, X133.v, X147.v, X174.v, X175.v, X190.v,
X198.v, X199.v, X200.v, X201.v, X95.v: 25 `arxiv:` / `studies:` rows). Gate:
`python3 meta/check_statement_docs.py --ignore-baseline minor-theory` -> 31 target(s), 31
documented, 0 error(s); reverse coverage 31/31. No orphans: every target owns a corpus row.

### Duplicated vocabulary

From `--warnings minor-theory` (8 warnings):

- `minor-theory/theories/conjectures/U7.v:47` `path_edges` — library counterpart: the edge set of
  a walk; no coq-graph-theory / GTBase notion exists, the file already tags it `@MOVE-to-base`.
- `minor-theory/theories/conjectures/X11.v:15` `x11_xy_path` — MathComp `path` / sgraph.v
  `upath`, `Path`: an `x11_xy_path` is a `upath` from a vertex of `X` to a vertex of `Y`.
- `minor-theory/theories/conjectures/X147.v:12` `x147_c_fat_minor` — minor.v `minor` (the four
  first clauses are literally a `minor_rmap`; only the distance clause is new).
- `minor-theory/theories/conjectures/X198.v:32` `x198_join_path` and `:35`
  `x198_forbids_Ktm_and_join_path` — MathComp `path` (the name clash is incidental: `join_path`
  is the graph `I_{t-1} + P_m`, not a path predicate).
- `minor-theory/theories/conjectures/X27.v:23` `x27_consecutive_in_cycle` — MathComp
  `cycle` / `ucycle` (`rot 1 c` bookkeeping that `ucycle` already provides).
- `minor-theory/theories/conjectures/X67.v:12` `x67_consecutive_in_path` — MathComp `path`.
- `minor-theory/theories/conjectures/X67.v:35` `x67_no_cross_edges` — "anticomplete", the same
  notion as `x11_anticomplete_sets` in X11.v; no library counterpart yet.

Found by reading, not caught by the suffix heuristic (the more valuable WP4b input):

- `X27.v:11` `x27_tree_decomposition` — coq-graph-theory treewidth.v `sdecomp`. It is the single
  most reused local notion of the package: `x27_treewidth_at_most` (X27.v), `x121_tree_alpha_le`
  (X121.v), `x127_two_tree_width_le` (X127.v), `x95_pathwidth_at_most` and
  `x95_subgraph_indexed_tree_decomposition_width_at_most` (X95.v), `x201_treewidth_at_least`
  (X201.v) all build on it. Migrating it to base and proving
  `x27_tree_decomposition bag <-> sdecomp ...` would unlock six statements at once.
- `X11.v:12` `x11_path_vertices`, `X67.v:15` `x67_path_vertices`, `X175.v:14`
  `x175_path_internal` — three copies of "the vertex set of a sequence".
- `X190.v:11` `x190_weight` and `X199.v:11` `x199_weight` — byte-identical definitions in two
  files (`\sum_(v in S) rho v`).
- `X200.v:11` `x200_minor_model` — minor.v `minor_rmap`; `X147.v:12` `x147_c_fat_minor` repeats
  the same four clauses again.
- `X133.v:12` `x133_Ks_free` and `X121.v:15` `x121_omega` — two wrappers around the library
  clique number `ω` in two files.
- `X175.v:17` `x175_simple_path_between` — sgraph.v `upath` / `Path`.
- `X190.v:14` `x190_strongly_sublinear_separator_class` and `X199.v:14`
  `x199_weighted_balanced_separator` — both re-derive "balanced separator" without using
  connectivity.v `separator` / `separates`.
- `U7.v:57` `immersion` is *not* a duplicate (no library immersion exists) but it is already a
  cross-file primitive: X174.v imports U7 for it. It belongs in `base/theories/common.v`.

### Suspected unfaithful or proxy encodings

- `opg:high_connectivity_no_k_n` (`minor-theory/theories/conjectures/U7.v:124`,
  `high_connectivity_no_k_n_statement`) — severity: **too strong** (for n <= 5). `n - 5` is
  truncated natural subtraction, so for every n <= 5 the conclusion becomes
  `planar_after_deleting wagner_planar G 0`, i.e. "G itself is planar". The source's `n-5` is
  negative there and the problem is only meaningful for n >= 5; a guard `5 <= n` (or the
  alternative bound `n - 5` replaced by an explicit `exists m, n = m + 5`) would restore the
  source's domain.
- `studies:std_georgakopoulos_papasoglu_conjecture_fat_minors` (`X147.v:39`) — severity: **too
  weak (proxy)**. `x147_quasi_isometric_to_H_minor_free` is not a quasi-isometry: it gives two
  DECOUPLED maps `f : G -> Q` and `g : Q -> G`, each with only the upper Lipschitz bound
  `dist(f x, f y) <= L * dist(x,y) + C` plus coarse surjectivity. The lower bound
  `dist(x,y)/L - C <= dist(f x, f y)` and the quasi-inverse condition `dist(g (f x), x) <= C`
  are both missing. Already flagged `PARTIAL (proxy)` in the row's `verification_note`
  (faithfulness audit 2026-07-17).
- `arxiv:1606.06810#00` (`X174.v:26`, `kt_immersion_clique_count_extremal_statement`) —
  severity: **too weak / wrong object** on the two boundary values. `x174_extremal_bound t n`
  computes `(n - t) + 3` over the naturals, so at the two admitted values `n = t-2` and
  `n = t-1` it evaluates to `2^(t-2) * 3` instead of `2^(t-2) * 1` and `2^(t-2) * 2`. The
  universal half is then too weak and the existence half asks for the wrong exact count. Fix:
  write the bound as `2^(t-2) * (n + 3 - t)` with the guard already present, or guard `t <= n`.
- `arxiv:1704.00125#00` (`X190.v:44`, `thin_overlay_without_bounded_degree_statement`) —
  severity: **vacuous-looking**. `x190_thin_system_of_overlays C` unfolds to
  `exists thin, forall G, C G -> exists _ : x190_overlay G thin, True`, and the `x190_overlay`
  record is inhabited for EVERY `G` by the identity cover (cover graph `G`, cover map `id`,
  every fibre a singleton, every edge lifted), so the conclusion holds with `thin = 1` and the
  whole statement is provable. The source's overlays must additionally be structured
  (bounded-treewidth pieces covering `G`); that content is absent. Row recorded as blocked.
- `arxiv:1710.03117#00` (`X199.v:35`, `strongly_sublinear_separator_constant_M_statement`) —
  severity: **too strong** (believed false). Three departures from Dvorak's conjecture: the
  polynomial omega-expansion hypothesis on the class is dropped (it quantifies over ALL
  `C : sgraph -> Prop`); the constant `bound` is chosen BEFORE `ell` although the source lets it
  depend on the class and on `ell`; and the source's weighted separator bound `q(C) <= q(V)/ell`
  is replaced by a cardinality bound `#|S| <= ell * sqrt_ceil #|G|.+1 + ell`. Row recorded as
  blocked.
- `studies:std_dallard_milani_torgel_conjecture` (`X121.v:46`) — severity: **too strong** (mild,
  forward direction only). The class is an arbitrary predicate on `sgraph` with no hereditary /
  induced-minor-closure assumption, whereas Dallard, Milanic and Storgel state the conjecture for
  hereditary classes. The backward direction is unaffected; the forward direction is strictly
  stronger than the source. Worth a second reader against the paper.
- `studies:std_dujmovi_joret_morin_norin_wood_question_2_tree_w` (`X127.v:44`) — severity: none
  (faithful), recorded for visibility. The statement is FAITHFUL-TO-REFUTED: the Burling graphs
  give 2-tree-width <= 2 with unbounded chromatic number (Felsner, Joret, Micek, Trotter,
  Wiechert, arXiv:1703.07871, Thms 1 and 2), so the statement is false while the row is recorded
  as open. Distinct from the same authors' still-open spaghetti Conjecture 3.

### Other

- Empty-graph soundness guards `0 < #|G|` are added, with no counterpart in any source text, in
  `forcing_a_k_6_minor_statement`, `seagull_statement`,
  `forcing_a_2_regular_minor_statement` (U7.v) and in the four arXiv:2204.10119 rows of X5.v.
  They are necessary (the empty graph vacuously satisfies every degree / regularity hypothesis
  yet has no nonempty minor), but they do weaken each statement by one degenerate case and are
  the natural targets of WP5 guard-has-teeth grounding lemmas. In `forcing_a_k_6_minor_statement`
  the guard is redundant in the second conjunct, where `7.-connected G` already forces
  `7 < #|G|`.
- `arxiv:1606.06810#00` (X174.v) counts ALL cliques, the empty set included, while its sibling
  `arxiv:1606.06810#01` (X175.v) counts only NONEMPTY cliques — two conventions for the same
  quantity from the same paper. Only one of them can match Fox and Wei's construction; the X174
  convention is the one the audit checked.
- `arxiv:2001.01607#00` (X42.v) formalises only the treewidth half of the source's "bounded
  treewidth (or cliquewidth)" question. That is the stronger half, but the row text covers both.
- The U7.v file header still described the two planarity rows as taking an ABSTRACT
  `is_planar` parameter and being `compile_blocked`, while the bodies had already been retargeted
  to the combinatorial `wagner_planar`. The header paragraph was updated in this pass (comment
  only, no code touched).
- `arxiv:1710.06282#00` and `#01` (X200.v, X201.v) are recorded `solved` in the corpus yet carry
  open-form statements; that is by design (the statement leg tracks faithfulness, not truth), but
  a `check_milestone` exact-type probe should confirm no committed proof targets them.

## hypergraph-theory

Pass over the 25 documented targets of `hypergraph-theory/theories/conjectures/` (U12.v: 4 OPG
rows; X6.v, X72.v, X73.v, X104.v, X108.v, X117.v, X119.v, X137.v, X148.v, X209.v, XE1.v, XE2.v:
21 `arxiv:` / `studies:` / `erdos:` rows). Gate:
`python3 meta/check_statement_docs.py --ignore-baseline hypergraph-theory` -> 25 target(s), 25
documented, 0 error(s); reverse coverage 25/25. No orphans.

### Duplicated vocabulary

From `--warnings hypergraph-theory` (16 warnings). All of these are hypergraph notions that have
no coq-graph-theory / GTBase counterpart at all; the warning fires only on the name suffix, so the
library counterpart column says "name clash only" unless stated otherwise:

- `hypergraph-theory/theories/conjectures/U12.v:116` `contains_complete` — `complete` / `'K_n`
  (name clash only: this is the hypergraph `K_m^(k)`).
- `U12.v:169` `berge_cycle` — MathComp `cycle` (name clash only: Berge cycle of a hypergraph).
- `U12.v:180` `berge_acyclic` — `acyclic` (name clash only).
- `U12.v:185` `hg_connected` — connectivity.v `connected` (name clash only: Berge connectivity).
- `U12.v:194` `k_forest`, `U12.v:203` `critical_k_forest` — sgraph.v `is_forest` (name clash
  only).
- `U12.v:198` `k_tree` — sgraph.v `is_tree` (name clash only).
- `U12.v:263` `hg_matching` — connectivity.v `matching` (name clash, but see the cross-file
  duplication below: it IS a duplicate of `x6_matching`).
- `X117.v:27` `x117_edges`, `XE1.v:9` `xe1_complete_uniform_edges` — `edges` (name clash only).
- `XE1.v:12` `xe1_mono_3_clique` — sgraph.v `clique` (name clash only).
- `X6.v:19` `x6_matching`, `X6.v:27` `x6_no_k_matching`, `X6.v:30`
  `x6_extremal_no_k_matching` — `matching` (name clash; `x6_matching` duplicates `hg_matching`).
- `X6.v:48` `x6_proper_coloring` — coloring.v `coloring` (name clash only: hypergraph
  colouring forbids monochromatic hyperedges, not monochromatic edges).
- `X73.v:19` `x73_regular` — GTBase `regular` (name clash; duplicates the hyperdegree notion of
  X6.v, see below).

The real WP4b finding is intra-package duplication: this package has no `foundations/` directory,
so every file re-declares the same hypergraph vocabulary.

- **"k-uniform" is defined SEVEN times with the same body**: `U12.v:52` `k_uniform`,
  `X6.v:11` `x6_uniform`, `X104.v:11` `x104_uniform`, `X108.v:11` `x108_uniform`,
  `X119.v:11` `x119_uniform`, `X137.v:11` `x137_uniform`, `X209.v:11` `x209_uniform`.
- **"r-partite r-uniform" twice**: `U12.v:203` `r_partite_uniform` and `X6.v:14`
  `x6_r_partite_uniform` (identical; X72.v and X73.v import the X6 one).
- **matching and matching number twice**: `U12.v:209` `hg_matching` + `U12.v:214`
  `is_matching_number` vs `X6.v:19` `x6_matching` + `X6.v:23` `x6_matching_number` (identical).
- **vertex cover and cover number twice**: `U12.v:219` `hg_cover` + `U12.v:223`
  `is_cover_number` vs `X72.v:15` `x72_vertex_cover` + `X72.v:19` `x72_transversal_number`
  (equivalent; one spells the meeting condition `X :&: e != set0`, the other
  `~~ [disjoint X & e]`).
- **hyperedge degree twice**: `X6.v:45` `x6_hg_degree` and `X73.v:16` `x73_hyperdegree`
  (identical).
- **the Ramsey host machinery three times**: image of a hyperedge (`X108.v:23`, `X117.v:32`,
  `X119.v:20`), monochromatic copy (`X108.v:27`, `X117.v:36`, `X119.v:24`) and "N vertices force
  a monochromatic copy" (`X108.v:35`, `X117.v:46`, `X119.v:34`). The X119 versions are the
  q-colour generalisation of the two-colour X108 / X117 ones, so one parameterised copy suffices.
- **"contains a complete r-uniform hypergraph on q vertices" three times**: `U12.v:96`
  `complete_sub` + `U12.v:102` `contains_complete`, `XE1.v:25` `xe1_contains_complete_uniform`,
  `XE2.v:11` `xe2_hyperclique`.
- **integer ceiling square root**: `X119.v:48-51` `x119_sqrt_ex` / `x119_sqrt` is a verbatim copy
  of `sqrt_ceil_ex` / `sqrt_ceil` in `base/theories/asymptotics.v:68-72` — a true
  library-counterpart duplicate, and the cheapest one to remove.

Recommended WP4b/WP6 action: one `hypergraph-theory/theories/foundations/hypergraph.v` holding
`uniform`, `r_partite_uniform`, `matching` / `matching_number`, `cover` / `cover_number`,
`hyperdegree`, `hg_chromatic_number` and the Ramsey-host trio, with the per-file copies replaced
by equivalence lemmas.

### Suspected unfaithful or proxy encodings

- `studies:std_gerbner_keszegh_methuku_abhishek_nagy_patk_s_tom`
  (`hypergraph-theory/theories/conjectures/X148.v:32`,
  `gerbner_two_families_ahlswede_khachatrian_bound_statement`) — severity: **wrong object**
  (believed false as written). The source (Scott and Wilmer, verifying Gerbner et al. Conj. 2.5)
  fixes a UNIFORM profile `|A_i| = a`, `|B_i| = b` with `t <= a <= b` and bounds `#|I|` by
  `AK(a+b, a, t)`, the maximum size of an `a`-UNIFORM `t`-intersecting family of subsets of an
  `(a+b)`-set. The Rocq statement has no `a`, no size constraint on `A i` or `B i`, and
  `x148_AK_bound #|T| t` is the NON-UNIFORM maximum of Frankl families over the whole ground set.
  Row recorded as blocked (faithfulness audit 2026-07-17).
- `arxiv:1803.08462#00` (`X209.v:54`, `hypergraph_cut_excess_theta_sqrt_statement`) — severity:
  **wrong object** (minimality mis-quantification). `x209_is_min_scaled_excess` (X209.v:38-45)
  reads `forall (T' : finType) (E' : {set {set T}}) (y : nat), ...`: `T'` is bound but never
  used, and `E'` is typed over the OUTER witness type `T`. The "smallest maximum r-cut over all
  m-edge k-graphs" is therefore a minimum over m-edge k-graphs on ONE chooseable vertex set. Fix:
  type `E'` over `T'`.
- `opg:turans_problem_for_hypergraphs` (`U12.v:105`) — severity: **too weak** (partial coverage).
  The corpus row carries TWO conjectures; only the first (3-uniform on 3n vertices, no
  `K_4^(3)`, bound `n^2(5n-3)/2`) is formalised. The second (3-uniform on 2n vertices, no
  `K_5^(3)`, bound `n^2(n-1)`) has no Rocq counterpart, so the statement does not cover its row.
  Same pattern as `opg:forcing_a_k_6_minor` in minor-theory, which DOES conjoin both of its
  source propositions — the conventions differ between the two rows.
- `studies:std_erd_s_rado_sunflower_conjecture` (`X137.v:28`) — severity: **deliberate deviation
  from `statement_text`** (stronger than the recorded text). The corpus text is "there is a
  constant `C = C(r)` depending only on `r` such that `f_r(k) <= C^k`"; the body puts the
  constant on the PETAL COUNT and the SET SIZE in the exponent (`C(k)^r`). The audit fix of
  2026-07-18 made that swap on the ground that the `C(r)^k` reading follows from the 1960
  Erdos-Rado sunflower LEMMA and carries no open content. The reasoning is sound, but the row's
  `statement_text` and the Rocq body no longer agree literally; a second reader should either
  confirm the corpus text uses `r` for the petal count or flag the corpus text for correction.
- `studies:std_lov_sz_conjecture_on_r_partite_hypergraph_matchi` (`X6.v:73`) — severity: none
  (faithful), recorded for visibility. The row's status is `open`, but the sibling row
  `arxiv:2505.05339#02` comes from a paper titled "A Counterexample to a Conjecture of Lovasz"
  that refutes exactly this statement. FAITHFUL-TO-REFUTED; the row status should probably move
  to `disproved`.
- `erdos:834` (`X6.v:116`, `critical_three_uniform_min_degree_seven_statement`) — severity:
  **too strong** (marginal). `x6_chromatic_edge_critical E k` (X6.v:65-68) demands
  `x6_chromatic_number (x6_edge_delete E e) k.-1` for every hyperedge, i.e. the chromatic number
  must become EXACTLY `k-1`; the usual definition of criticality only asks it to drop below `k`.
  At `k = 3` the two agree unless the remaining family is 1-colourable, so the risk is small, but
  the statement is an EXISTENCE claim, where a stronger requirement on the witness makes it
  harder, not easier, to satisfy.
- `opg:are_critical_k_forests_tight` (`U12.v:175`) — severity: **interpretation risk (wrong
  object?)**. Both undefined terms of the row are given readings the OPG text does not pin down:
  "critical k-forest" as maximal-Berge-acyclic (`critical_k_forest`, U12.v:171) and the
  acyclicity itself as Berge-acyclicity rather than one of the other standard hypergraph
  acyclicities (alpha-, beta-, gamma-acyclic, or tightness in the sense of tight k-trees, which
  the row TITLE evokes). A second reader against the OPG page and its references is warranted
  before the row is treated as settled.

### Other

- `X119.v:48-51` (`x119_sqrt_ex`, `x119_sqrt`) is a verbatim copy of `base/theories/asymptotics.v`
  `sqrt_ceil_ex` / `sqrt_ceil`, lemma included; X199.v in minor-theory already uses the base one.
- `XE1.v:9` `xe1_complete_uniform_edges` is defined but used by no statement in the package.
- `erdos:` rows carry no site or review URL (`corpus_registry.row_urls` returns `(None, None)` for
  that tag), so their doc blocks say `Site: none` / `Review: none`. Eight of the 25 targets are
  such rows (X6.v x4, XE1.v x3, XE2.v x3 — ten in total counting XE2).
- Non-vacuity guards with no counterpart in the source text: `1 < r` and `E != set0` in both X6.v
  matching-deletion rows, `E != set0` in `ryser_intersecting_partite_cover_gap_statement`
  (X72.v), `0 < n` in `turans_problem_for_hypergraphs_statement`, `0 < k` and `E != set0` in
  `are_critical_k_forests_tight_statement`, `1 < r` in `rysers_statement`, `1 <= d` in X73.v,
  `2 <= k` in X137.v, `2 <= r` throughout XE1/XE2 and `3 <= e` in X104.v. Each is justified in
  its doc block's `Notes:`; together they are the WP5 guard-has-teeth grounding list for this
  package.
- Several rows recorded `solved` / `disproved` in the corpus carry open-form statements
  (`erdos:775`, `erdos:794`, `erdos:832`, `erdos:833`, `erdos:834`, `arxiv:1803.08462#00`); that
  is by design, but the `check_milestone` exact-type probes should confirm that no committed
  proof or refutation targets them.

## chromatic-theory

Documentation pass (WP4) over the 123 statement targets of the package: 122 corpus-row blocks and
1 orphan marker. `python3 meta/check_statement_docs.py --ignore-baseline chromatic-theory` ends
with 0 errors and 122/122 reverse coverage; `make chromatic-theory` rebuilds clean. Every
`English statement:` below was written by back-translating the Rocq body and then compared with the
row's `statement_text`/`context_text`; the disagreements found are listed in
`Suspected unfaithful or proxy encodings`.

### Duplicated vocabulary

From `check_statement_docs.py --ignore-baseline --warnings chromatic-theory` (44 warnings, all in
this package), grouped by the library/GTBase notion they duplicate.

- `edge_set` (coq-graph-theory `mgraph.edge_set`, GTBase `finite_graph.fg_edges`): eight verbatim
  copies of "the 2-element vertex sets that are edges" — `X100.v:11 x100_edge_set`,
  `X142.v:11 x142_edge_set`, `X33.v:11 x33_edge_set`, `X34.v:11 x34_edge_set`,
  `X35.v:11 x35_edge_set`, `X43.v:11 x43_edge_set`, `X64.v:12 x64_edge_set`,
  `XE1.v:11 xe1_edge_set`. Prime candidate for one `base/theories/common.v` `edge_set` on `sgraph`.
- `colouring` (coq-graph-theory `coloring.v` `coloring`/`chi_mem`, GTBase `list_colourable`):
  `X109.v:11 x109_proper_colouring`, `X162.v:21 x162_proper_colouring`,
  `X187.v:13 x187_proper_3_colouring`, `X3.v:40 x3_proper_colouring`,
  `X63.v:11 x63_proper_colouring`, `X68.v:11 x68_proper_three_colouring` are six copies of the same
  "adjacent vertices get different colours" predicate; the remaining ones name genuinely new
  notions built on it (`U4.v:145 acyclic_colouring`, `U5.v:402 acyclic_edge_colouring`,
  `U5.v:437 star_edge_colouring`, `X100.v:18 x100_modular_edge_colouring`,
  `X126.v:31 x126_nonrepetitive_list_colouring`, `X130.v:16 x130_bfold_colouring`,
  `X142.v:22 x142_proper_edge_colouring`, `X159.v:23 x159_correspondence_colouring`,
  `X164.v:54 x164_linear_time_outputs_three_colouring`, `X210.v:21 x210_conflict_colouring`,
  `X63.v:19 x63_k_homogeneous_colouring`, `XE1.v:80 xe1_strong_edge_colouring`,
  `XE2.v:42 xe2_cochromatic_colouring`).
- `path` (coq-graph-theory `sgraph.upath`/`Path`, mathcomp `path`):
  `X126.v:12 x126_genuine_path`, `X157.v:14 x157_simple_xy_path`, `X3.v:54 x3_induced_path`
  (the last adds chordlessness, the first two are plain simple paths), plus the helpers
  `X3.v:22 x3_consecutive_in_path` and `X83.v:12 x83_rainbow_induced_path`.
- `cycle` (mathcomp `ucycle`, GTBase `girth_geq` companions): `XE1.v:29 xe1_cycle` is exactly
  "`ucycle` with more than two vertices" and is re-derived as `X153.v:14 x153_short_cycle`; the
  consecutive-vertex helpers `X3.v:19 x3_consecutive_in_cycle` and
  `XE1.v:26 xe1_consecutive_in_cycle` are byte-for-byte the same definition in two files;
  `XE2.v:62 xe2_triangles_plus_hamilton_cycle` names a compound object.
- `edges` / deletion: `X7.v:31 x7_delete_edges`, `XE1.v:62 xe1_delete_edges` (identical) and
  `XE1.v:74 xe1_strongly_independent_edges`; an `sgraph` edge-deletion belongs in base.
- `clique`: `X181.v:15 x181_maximal_clique` (coq-graph-theory has `clique`/`cliqueb`, not
  maximality).
- `complete`: `X188.v:44 x188_component_not_complete` (uses `clique` on a component).
- `matching`: `X34.v:42 x34_linear_forests_and_matching` (the matching clause duplicates
  `connectivity.matching` in edge-set form).
- `minor`: `U8.v:149 vertex_minor` is a genuinely different notion (local complementation plus
  vertex deletion) and only collides by suffix; no action needed beyond the name.

### Suspected unfaithful or proxy encodings

Rows whose Rocq body does not match the corpus text. The first five are NEW findings of this pass
(their corpus legs are `done` and they carry no prior audit note); the rest restate, in the doc
blocks, defects already recorded by the 2026-07-17 faithfulness audit
(`meta/BLOCKED_RETARGETING_AUDIT.md`) — repeated here because the doc blocks now have to state
them.

- `opg:seymours_r_graph_conjecture` (`U5.v seymours_r_graph_statement`) — the source concludes
  `chi'(G) <= r+1` for every r-graph, the body concludes `edge_colourable G r`, i.e.
  `chi'(G) <= r`. Severity: **too strong**, and in fact refutable — the Petersen graph is a
  3-graph with chromatic index 4, so the statement as written is false. Fix: `edge_colourable G r.+1`.
- `opg:list_colorings_of_edge_critical_graphs` (`U4.v`) — `Delta_edge_critical` only requires that
  deleting any edge lowers the chromatic index; the classical Delta-edge-critical hypothesis also
  requires `chi'(G) = Delta + 1`. The hypothesis holds for strictly more graphs than the source's.
  Severity: **too strong**.
- `opg:list_colourings_of_complete_multipartite_graphs_with_2_big_parts` (`U4.v`) — the corpus row
  asks for the VALUE of the least `t` with `ch(K_{a,b}+K_t) = chi(K_{a,b}+K_t)`; the body only
  asserts that this least `t` exists. Severity: **too weak** (a "what is" question encoded as
  well-definedness).
- `opg:universal_steiner_triple_systems` (`U5.v`) — the corpus row is the classification problem
  "which Steiner triple systems are universal?"; the body asserts only that SOME valid STS is
  universal. Severity: **too weak**.
- `arxiv:2302.13312#00` (`X34.v planar_odd_degree_linear_forests_plus_matching_statement`) — the
  source conjecture assumes odd `Delta >= 7`, the Rocq guard is `9 <= Delta G`. The formal row
  therefore excludes exactly `Delta = 7`, which the corpus `status_semantics` records as the only
  case still open (`Delta >= 9` is proved). Severity: **too weak** (the encoded range is already a
  theorem).
- `studies:std_dreier_toru_czyk_conjecture_merge_width_polynomi` (`X124.v`, leg `blocked`) — the
  merge expression is consumed only through `x124_expr_leaves`, so the "bounded merge-width"
  antecedent restricts nothing and the implication collapses to "every class is polynomially
  chi-bounded". Severity: **vacuous-looking antecedent / too strong**.
- `arxiv:1510.06964#00` (`X162.v`, leg `blocked`) — `x162_kempe_step` requires only a connected
  two-coloured set, not a whole Kempe component, and does not require the result to be proper, so
  the statement is trivially true for every finite graph and every `q`. Severity: **vacuous**.
- `arxiv:1601.01197#00` (`X164.v`, leg `blocked`) — the class drops the source's "in the
  affirmative case" precondition, so a valid 3-colouring output is demanded even for instances
  whose precolouring does not extend. Severity: **too strong** (provably false).
- `arxiv:1605.07411#02` (`X170.v`, leg `blocked`) — `x170_nonexceptional` excludes
  `[set inord 7]` and `[set ord0]`, which under the bit encoding are not the two non-chi-bounded
  orientations (directed and antidirected `P4`). Severity: **wrong object** (false).
- `arxiv:1609.00314#00` (`X177.v`, leg `blocked`) — "induced" is absent from both the antecedent
  and the consequent; the fourth clause of `x177_induced_path_between` is a machine-confirmed
  tautology. Severity: **wrong object / too weak**.
- `arxiv:1701.05597#00` (`X185.v`, leg `blocked`) — widespreadness of a multigraph `H` is about
  subdivisions of `H`, but the body subdivides `line_graph H`. Severity: **wrong object**.
- `arxiv:1701.05597#01` (`X186.v`, leg `blocked`) — `x186_contains_induced_subdivision` imposes no
  chord-freeness and no internal disjointness between the branch paths, so it is weaker than
  "contains an induced subdivision". Severity: **too weak**.
- `arxiv:1703.05380#00` (`X188.v`, leg `blocked`) — `x188_add_colour` unions a colour into a list,
  so the adversary may re-supply a colour already present and the list never grows; this is not the
  Bonamy–Meeks interactive game. Severity: **wrong object**.
- `arxiv:1703.07871#00` (`X189.v`, leg `blocked`) — the spaghetti condition reduces to
  `connect (--) root t`, which is vacuous on a connected index tree, so the hypothesis is an
  ordinary tree-decomposition plus a path-decomposition. Severity: **too strong**.
- `arxiv:1612.08698#00` (`X183.v`, leg `blocked`) — `weighted_epsilon_flexible G d.+1 p q` requires
  lists of size AT LEAST `d+1` while the request weight sums over all colours of each list, and
  weighted flexibility is not monotone in list size; the source is about lists of size exactly
  `d+1`. Severity: **too strong** (provably false).
- `arxiv:1802.03727#00` (`X203.v`, leg `blocked`) — the universal quantifier over graphs includes
  the empty graph, which has minimum degree `d` vacuously and is separation `j`-choosable for every
  `j`. Severity: **too strong** (refutable).
- `arxiv:1803.10962#00` (`X210.v`, leg `blocked`) — the source's `C, C' > 0` is dropped, so
  degenerate witnesses such as `C = 0` are admitted; the positive constant `C` in "at most `Ck`
  conflicts" carries the whole content. Severity: **vacuous-looking**.
- `studies:std_gimbel_thomassen_problem_3` (`X150.v`, leg `partial`), `arxiv:1010.2472#00`
  (`X152.v`, leg `partial`) and its duplicate `arxiv:1404.6356#00` (`X154.v`), plus the surface
  hypothesis of `X164.v` and `X210.v` — `surface_embeddable` unfolds to
  `exists rotation system E, surface_euler_genus E <= g` with `surface_euler_genus` computing the
  ORIENTABLE genus, so every non-orientable surface (projective plane, Klein bottle, …) is silently
  excluded. Severity: **wrong object** (proxy, narrower class than the source).
- `arxiv:1612.06539#00` (`X181.v`, leg `partial`) — the conjecture is an equality
  `chi_c(G(n,1/2)) = (1/2+o(1)) log2 n`; the window only asserts that SOME `k` inside the window is
  a clique-colouring number of the graph, not that the clique chromatic number itself lies there.
  Severity: **too weak**.

### Other

- **Questions asserted affirmatively.** 40 of the 122 documented rows have corpus `kind`
  `Problem` (32) or `Question` (8), and several more OPG rows carry no `kind` while their text is a
  question ("Are there ...?", "Is it true that ...?", "Does there exist ...?"); wherever the corpus
  text is interrogative the Rocq body is the affirmative proposition (U1 rows 2, 4, 8, U4 row 3, U5 rows 6
  and 8, X3 rows 3, 4, 8, XE1 all four, several XE2 rows, X28, X43, X63, X69, X75, X81, X112, X126,
  X150, X152, X157, X160, X161, X192, X203, X7 rows 2–5). This is the package's standing convention
  and is now stated in each block's `Notes:`; a negative resolution of any such question refutes the
  corresponding definition rather than confirming it.
- **Cross-file duplicate definitions** (invisible to the suffix warning, all candidates for
  `foundations/` or `base/theories/common.v`): `x3_polynomially_chi_bounded` (X3.v) vs
  `x124_poly_chi_bounded` (X124.v), with `x3_poly_eval` and `x124_poly_eval` identical;
  `chi_bounded` (U8.v) vs `x112_chi_bounded` (X112.v) vs `x170_chi_bounded` (X170.v);
  `x3_complement_graph` (X3.v) vs `xe2_complement_graph` (XE2.v) — identical constructions;
  `x31_subgraph_of` (X31.v) vs `xe1_subgraph_of` (XE1.v); `x3_stable_set` (X3.v) vs
  `xe1_stable_set` (XE1.v), both duplicating `dom.stable`; `x126_tree_decomposition` (X126.v) vs
  `x189_tree_decomposition` (X189.v), both duplicating `treewidth.sdecomp`;
  `x157_data_nth_nat` (X157.v) vs `x164_data_nth_nat` (X164.v);
  `x177_contains_induced_long_subdivision` (X177.v) vs `x185_contains_induced_long_subdivision`
  (X185.v) — byte-for-byte identical — and the unlengthed variant
  `x186_contains_induced_subdivision` (X186.v); `x43_line_graph` (X43.v) and `x33_total_graph`
  (X33.v) re-do base's `line_graph`/`total_graph` on `sgraph` instead of `mgraph`.
- **Local synonyms of base notions**, defined only to rename: `x112_omega` and `x124_omega`
  (= `omega`), `x129_maxdeg` (= `Delta`), `x132_triangle_free`, `x187_triangle_free`,
  `x192_triangle_free` (= `girth_geq G 4`, while base already has `triangle_free`, used elsewhere in
  the same package), `x150_embeddable_in_fixed_surface`, `x152_embeddable_in_fixed_surface`,
  `x210_euler_genus_embeddable` (= `surface_embeddable`), `x164_embedded_in_fixed_surface_with_boundary`
  (which additionally IGNORES its `boundary` argument).
- **Dead / unused vocabulary**: `XE2.v:35 xe2_sqrt_lower` is defined but used by no statement in the
  package (the `erdos:753` row uses `xe2_above_half_plus_rational_power` instead);
  `X189.v:20 x189_rooted_spaghetti_index` is likewise unused, and its type is suspicious
  (`bag : T -> {set T}` maps index nodes to sets of INDEX nodes).
- **Guards with no counterpart in the source text**, each justified in its block's `Notes:` and
  together forming the guard-has-teeth list for this package: `0 < #|G|` in
  `double_critical_graph_statement`, `reeds_omega_delta_and_chi_statement` and
  `aravind_rainbow_induced_chromatic_path_statement`; `0 < Delta G` in
  `strong_edge_colouring_statement` and `strong_colorability_statement`; `2 < k` in
  `cycles_in_graphs_of_large_chromatic_number_statement`; `2 <= k` in
  `clustered_chromatic_minor_class_treedepth_bound_statement`; `1 <= t` in
  `list_hadwiger_two_t_statement`; `1 <= s`, `1 <= t` in
  `woodall_ks_t_minor_free_list_colouring_statement`; `1 <= d` in
  `a_generalization_of_vizings_theorem_statement`; `0 < k`, `k <= #|G|` in
  `sparse_graph_low_chromatic_cut_statement`; `msimple G` in `behzads_statement` (load-bearing: the
  bound is false over multigraphs).
- **Duplicate corpus rows sharing one encoding**: `X131.v` is a literal synonym of `X130.v` and
  `X154.v` of `X152.v`, in both cases deliberately, so that the two corpus rows cannot drift.
- `erdos:` and `studies:` rows carry no site or review URL (`corpus_registry.row_urls` returns
  `(None, None)`), so 38 of the 122 blocks in this package say `Site: none` / `Review: none`.
- One orphan: `applications/alon_tarsi_triangle.v question_6_1_statement`. The corpus DOES contain
  the matching row `arxiv:2209.09107#00` ("Question 6.1"), but that row registers no `formal_name`
  and its statement leg is `todo`, so the gate cannot link them; the file proves
  `question_6_1_disproved`. Registering the `formal_name` on that row (and on
  `arxiv:2209.09107#01`) would turn this orphan into a normal documented row.

## extremal-graph-theory

Pass over the 120 documented targets of `extremal-graph-theory/theories/` (116 corpus rows + 4
orphans): 41 Erdős-problem rows (`XE1.v`, `XE2.v`, `X4.v`), 25 OPG rows (`D2chr.v`, `D2pr.v`,
`D2ram.v`, `D2str.v`, `D2tur.v`), 19 `studies:` rows, 11 arXiv rows, and the 4 list-Ramsey
definitions of `foundations/list_ramsey.v` + `applications/` that carry no corpus row. Gate:
`python3 meta/check_statement_docs.py --ignore-baseline extremal-graph-theory` ->
`statement docs: 120 target(s), 120 documented, 646 in baseline, 0 error(s); reverse coverage:
116/116 rows covered, 0 uncovered`. Build: `make extremal-graph-theory` green (exit 0).

### Duplicated vocabulary

44 warnings from `python3 meta/check_statement_docs.py --warnings extremal-graph-theory`, grouped
by the library notion they shadow.

- **`edge_set`** (9) — `conjectures/X4.v:126 x4_edge_set`, `X36.v:11 x36_edge_set`,
  `X36.v:15 x36_degree_in_edge_set`, `X60.v:14 x60_edge_set`, `X76.v:11 x76_edge_set`,
  `X78.v:11 x78_edge_set`, `X84.v:11 x84_edge_set`, `X84.v:28 x84_cycle_edge_set`,
  `XE2.v:124 xe2_path_edge_set` — library counterpart: coq-graph-theory `E(_)` = `sg_edge_set`
  (and GTBase `fg_edges`). The six `*_edge_set` bodies are *textually identical*
  (`[set e | exists x y, (x -- y) && (e == [set x; y])]`).
- **`edges`** (9) — `D2pr.v:130 valid_edges`, `D2tur.v:130 ham_path_edges`,
  `X88.v:35 x88_within_part_edges`, `X191.v:38 x191_delete_edges`, `XE1.v:67 xe1_delete_edges`,
  `XE1.v:88 xe1_triangle_free_diameter_completion_edges`, `XE1.v:239 xe1_add_edges`,
  `XE1.v:265 xe1_min_turan_over_size_edges`, `XE2.v:10 xe2_tri_edges` — counterpart: `sg_edge_set`
  / `fg_edges`; `xe1_delete_edges`, `xe1_add_edges`, `x191_delete_edges` and
  `X60.v:29 x60_delete_edge_graph` are four independent edge-deletion/addition constructors that
  belong in `base/theories/common.v`.
- **`cycle`** (9) — `D2str.v:240 geodesic_cycle`, `D2str.v:252 induced_cycle`,
  `D2str.v:257 peripheral_cycle`, `X4.v:113 x4_consecutive_in_cycle`,
  `X49.v:25 x49_has_induced_cycle`, `X60.v:32 x60_has_induced_cycle`,
  `X115.v:28 x115_odd_induced_cycle`, `X143.v:11 x143_contains_cycle`, `XE2.v:88 xe2_cycle` —
  counterpart: MathComp `cycle`/`ucycle` (`path.v`) and GTBase `cycle_graph`;
  `x49_has_induced_cycle` and `x60_has_induced_cycle` are identical.
- **`path`** (3) — `D2tur.v:238 incr_path`, `X98.v:12 x98_consecutive_in_path`,
  `XE2.v:32 xe2_monochromatic_path` — counterpart: coq-graph-theory `Path`/`upath`, MathComp
  `path`. `x98_consecutive_in_path` and `X4.v:113 x4_consecutive_in_cycle` are the same idea on
  `zip p (behead p)` resp. `zip c (rot 1 c)`.
- **`tree`** (3) — `X105.v:16 x105_path_tree`, `X105.v:19 x105_star_tree`, `XE1.v:76 xe1_tree` —
  counterpart: coq-graph-theory `is_tree` / `is_forest`. `xe1_tree` is literally
  `is_forest [set: T] /\ connected [set: T]`, i.e. an unfolded `is_tree`.
- **`colouring`** (3) — `D2chr.v:60 bfold_colouring`, `D2chr.v:356 star_edge_colouring`,
  `foundations/circular_colouring.v:36 pq_colouring` — counterpart: coq-graph-theory `coloring`
  and GTBase `chromatic_index`/`edge_colourable`. `star_edge_colouring` genuinely needs the colour
  FUNCTION that base's count-only surface does not expose (documented in-file, tagged
  `@MOVE-to-base`).
- **`matching`** (2) — `X180.v:11 x180_matching`, `X180.v:15 x180_induced_matching` — counterpart:
  coq-graph-theory `connectivity.v` `matching`.
- **`minor`** (1) — `D2chr.v:70 frac_clique_minor` — counterpart: coq-graph-theory `minor.v`
  `minor` (this one is a deliberate LP relaxation, not a duplicate).
- **`connected`** (1) — `X115.v:17 x115_connected` — counterpart: coq-graph-theory `connected` /
  `connectedb`; `D2pr.v:134 connectedb` is a second, edge-set-indexed copy of the same idea.
- **`regular`** (1) — `X115.v:22 x115_two_regular` — counterpart: GTBase `regular`;
  `D2pr.v:132 regularb` is a second copy.
- **`forest`** (1) — `X195.v:11 x195_contains_forest` — counterpart: `is_forest`.
- **`stable`** (1) — `X61.v:15 x61_neither_clique_nor_stable` — counterpart: coq-graph-theory
  `dom.v` `stable`. Five further stable-set copies are not caught by the suffix heuristic:
  `XE1.v:13 xe1_stable_set`, `X56.v:11 x56_stable_set`, `X97.v:11 x97_stable_set`,
  `D2ram.v` (via `alpha`), `X13.v`/`X30.v` (via `bipartite`).
- **`complete`** (1) — `XE1.v:174 xe1_monochromatic_copy_in_complete` — FALSE POSITIVE of the
  suffix heuristic: the name ends in "in_complete", it does not redefine `complete`/`'K_n`.

Not caught by the heuristic but duplicated verbatim across files, worth one shared definition each:
`x56_induced_free` / `x57_induced_free` / `x58_induced_free` / `x61_induced_free` /
`x118_induced_free` / `x120_induced_free` (six identical copies of induced-subgraph-freeness);
`x57_anticomplete` / `x58_anticomplete`; `x59_poly_eval` / `x60_poly_eval`;
`x13_min_degree_at_least` / `x30_min_degree_at_least` / `xe1_min_degree_at_least`;
`x56_complement` / `xe1_complement_graph`; `x118_edges_between` / `x120_edges_between`;
`D2ram.v:85 edge_count` and `D2tur.v:74 edge_count` (same name, two different definitions, one via
`#|E(G)|` and one via `oedge`).

### Suspected unfaithful or proxy encodings

Seven of these confirm the existing `BLOCKED` verification notes; the rest are new findings from
the back-translation of the Rocq bodies.

- `studies:std_drier_linial_conjecture_haj_s_number_of_random_l`
  (`conjectures/X125.v:104`) — severity: **vacuous-looking / too weak**. `x125_almost_all`
  existentially quantifies the observation model `M : x125_lift_model ell`; a multiplicity-skewed
  model (extra sample points all observing the trivial disjoint-copies lift) satisfies every record
  field yet concentrates the `fg_whp` ratio on one lift, so the statement is provable with
  `a = b = 1`. Needs the canonical uniform labelled lift model.
- `arxiv:1611.02400#01` (`conjectures/X180.v:60`) — severity: **too weak**. The source asks for a
  family whose multitasking capacity `alpha > 0` is INDEPENDENT of `n`, but the capacity ratio
  `a/b` is chosen inside `x180_multitasker_capacity_positive G`, i.e. per graph; likewise the
  constants `c, C` of `x180_average_degree_logarithmic`. A family with capacity tending to 0
  satisfies the body.
- `studies:std_forcing_conjecture_skokan_thoma` (`conjectures/X143.v:70`) — severity:
  **too weak / wrong object**. `x143_density_converges` states only the UPPER relative bound
  `b * target_den * num <= (b + a) * target_num * den`; the source's `t(F,G_n) -> p^{e(F)}` is a
  TWO-SIDED convergence. A sequence whose densities collapse to 0 satisfies the predicate, so both
  sides of the encoded iff are wrong.
- `arxiv:1706.05642#00` (`conjectures/X191.v:78`) — severity: **vacuous-looking**. Finiteness
  collapse: in `x191_subquadratic_deletion_to_partite` the constant `C` is bound AFTER `F`, and
  `forall n, #|F| = n -> ...` pins `n` to the single value `#|F|`. The exponent `2 - delta` carries
  no content; take `C` large.
- `arxiv:1708.07369#00` (`conjectures/X195.v:48`) and `arxiv:1708.07369#01`
  (`conjectures/X196.v:23`) — severity: **wrong object**. `x195_k_nice` (X195.v:21-25) fixes
  exactly two colours (`{set 'K_N} -> 'I_2`) and its `k` argument never occurs in its body, whereas
  the paper's `k`-nice is "the `k`-colour Ramsey number `R(F;k)` meets its natural construction
  lower bound with equality". Both "for all `k >= k0`" and "for infinitely many `k`" are therefore
  contentless.
- `arxiv:1803.03588#00` (`conjectures/X207.v:56`) — severity: **vacuous-looking / wrong object**.
  Three independent breaks: (i) Rödl's theorem needs one eps-SPARSE or one eps-DENSE subgraph, but
  both disjuncts of `x207_rodl_delta_works` are LOWER density bounds; (ii) the second disjunct is
  `x207_density_at_least (induced S) (1 - d) 1` with nat subtraction, so for every `d >= 1` it
  reduces to `0 <= 2|E|` and holds for every `S`; (iii) `x207_H_free` uses MINOR-freeness where the
  source means INDUCED-subgraph-freeness.
- `arxiv:1810.00058#00` (`conjectures/X58.v:40`) — severity: **too weak** (NEW). The source asks
  for an anticomplete `(eps|G|, eps|G|)`-pair. The body bounds `B` linearly but bounds `A` by
  `eps_num^eps_den * #|G|^eps_num <= eps_den^eps_den * #|A|^eps_den`, i.e. `|A| >= eps * |G|^eps`,
  a SUBLINEAR bound whenever `eps < 1`. The two sides should carry the same linear bound.
- `studies:std_chv_tal_tuza_conjecture_on_maximum_odd_induced_c` (`conjectures/X115.v:57`) —
  severity: **too weak (disclosed proxy)**. Encodes `Theta(3^{n/3})` (two-sided constant factor,
  cubed) instead of the source's literal `= 3^{n/3}`, which is ill-posed over nat and already
  machine-refuted (`K_6`: count >= 20, `20^3 = 8000 > 729 = 3^6`). Kept as the resolved
  (Morrison–Scott) form; the deviation is documented in the block.
- `studies:std_arman_tsaturian_conjecture_on_the_number_of_cycl` (`conjectures/X85.v:40`) —
  severity: **too weak** (NEW). The source envelope is `(d/e)^n`; the body replaces `e` by an
  EXISTENTIALLY quantified natural `den > 1`, so a prover may take `den = 2` and obtain a strictly
  weaker bound than `d/e`.
- `opg:monochromatic_vertex_colorings_inherited_from_perfect_matchings`
  (`conjectures/D2chr.v:249`) — severity: **too weak**. The source asks "for which `(n,d)`"; the
  body only asserts the existence of ONE non-trivial pair (`n > 0`, `d >= 2`). The
  characterisation, which is the open content, is not expressed.
- `opg:circular_choosability_of_planar_graphs` (`conjectures/D2chr.v:319`) — severity:
  **proxy**. The Problem asks WHAT the best upper bound is; the body asserts that a least upper
  bound exists and is rational. No value is pinned.
- `opg:shannon_capacity_of_the_seven_cycle` (`conjectures/D2pr.v:252`) — severity: **proxy**.
  "What is the Shannon capacity of `C_7`?" is rendered as "the capacity exists over every
  `realFieldType`". Over an incomplete ordered field the infimum need not be attained, so the
  statement is well-definedness up to a completeness gate (mathcomp-analysis not installed).
- `opg:asymptotic_distribution_of_form_of_polyhedra` (`conjectures/D2pr.v:448`) — severity:
  **wrong object (over-approximation) + proxy**. `polyhedralb` tests only 3-connectivity, dropping
  planarity (by Steinitz, polyhedra = 3-connected PLANAR); graphs are counted LABELLED while the
  source counts topologically inequivalent polyhedra; and the source's "what is the distribution?"
  becomes "a limiting distribution exists".
- `opg:almost_all_non_hamiltonian_3_regular_graphs_are_1_connected`
  (`conjectures/D2pr.v:164`) — severity: **proxy**. `NH`/`NHB` count LABELLED graphs (edge sets on
  `'I_(2n)`) while the source counts isomorphism classes. Plausibly harmless for a ratio -> 1
  claim, but it is a modelling substitution, not the source's object.
- `opg:chromatic_number_of_common_graphs` (`conjectures/D2ram.v:256`) — severity: **proxy**.
  `common_graph H` is a finite eventual counting bound
  (`n^|V(H)| <= mono_copies * 2^|E(H)|`) standing in for the analytic notion "the random colouring
  asymptotically minimises the monochromatic count". The proxy class may be strictly wider or
  narrower than the true class of common graphs, so the quantified bound on `chi` is about a
  different family.
- `opg:negative_association_in_uniform_forests` (`conjectures/D2pr.v:293`) — severity:
  **stronger hypothesis (deliberate)**. The source says "let `e, f in E(G)`" with no distinctness;
  the body adds `e != f`. At `e = f` the source inequality degenerates to "every forest contains
  `e`", generically false, so the guard is a repair rather than an error — but the body is formally
  weaker than the literal text.
- `opg:covering_powers_of_cycles_with_equivalence_subgraphs` (`conjectures/D2str.v:446`) —
  severity: **too weak**. The growth threshold `g : nat -> nat` is existentially quantified with no
  constraint, so `g` may be chosen as large as needed. Documented as necessary (near-complete
  powers such as `C_{2k+1}^k = K_{2k+1}` violate any linear bound), but it makes the encoded
  `Omega(k)` weaker than the conjecture.
- `opg:what_is_the_smallest_number_of_disjoint_spanning_trees_made_a_graph_hamiltonian`
  (`conjectures/D2tur.v:161`) — severity: **proxy (PARTIAL)**. Only Question 1 is encoded, and as
  "the smallest such `k` exists" rather than "what is it"; Questions 2-4 (shortest Hamiltonian
  path, 1-trees, Hamiltonian cycle) are absent.
- `opg:good_edge_labelings` (`conjectures/D2tur.v:277`) — severity: **proxy**. Only the
  Conjecture is encoded (the companion Question on maximum edge density is dropped), and "finitely
  many critical graphs" becomes "a bound `N` on the vertex count", which is equivalent only up to
  isomorphism.
- `arxiv:2102.04994#00` (`conjectures/X56.v:46`) — severity: **too weak** (NEW). The
  Erdős–Hajnal exponent is encoded as `1/c` with `c : nat` (`#|G| <= #|S| ^ c`), so only
  reciprocals of integers are available; the source allows an arbitrary positive real `delta`.
- `erdos:87` (`conjectures/XE1.v:767`) — severity: **divergence from the literal text** (NEW). The
  source asks two questions (`R(G) > (1-eps)^k R(k)`, and the stronger uniform `R(G) > c R(k)`);
  the body formalises only the second, and with `>=` rather than `>`.
- `erdos:812` (`conjectures/XE1.v:691`) — severity: **stronger than the source** (NEW). The source
  asks the ratio question and the difference question separately; the body asserts their
  CONJUNCTION.
- `erdos:129` (`conjectures/XE1.v:352`) — severity: **slightly too weak** (NEW). The source bound
  is `R < C^{sqrt n}`; the body uses `xe1_sqrt_ceil`, hence `R < C^{ceil(sqrt n)}`.
- `erdos:552` (`conjectures/XE1.v:472`) — severity: **partial + slightly stronger** (NEW). Only
  the "in particular" half is encoded ("determine `R(C_4,S_n)`" has no Prop form), and
  `floor(sqrt n)` replaces `sqrt(n)`, tightening the bound for non-square `n`.
- `erdos:567` (`conjectures/XE1.v:568`) — severity: **inconsistent vocabulary** (NEW). `Q_3` and
  `K_{3,3}` are pinned by Rocq equality of `sgraph` structures (`G = xe1_hypercube 3`,
  `G = KB 3 3`) whereas `H_5` is characterised up to isomorphism (`xe1_h5_graph G`). Harmless here
  (the conclusion is isomorphism-invariant) but it should be one convention.
- `erdos:814` (`conjectures/XE2.v:532`) — severity: **wrong object at one boundary instance**
  (NEW). `(k - 1) * (n - k + 2)` parses as `(k-1) * ((n-k) + 2)` with nat subtraction; at the
  boundary `n = k-1` this is `(k-1)*2 + C(k-2,2) + 1` where the intended edge count is
  `(k-1)*1 + C(k-2,2) + 1`, so that single instance constrains a different family. The added guard
  `0 < #|S|` also makes the statement stronger than a literal reading.
- `erdos:915` (`conjectures/XE2.v:579`) — severity: **stronger than the source** (NEW). "m
  disjoint paths" is encoded as internally vertex-disjoint AND edge-disjoint, which additionally
  forbids two copies of the single edge `x-y`.
- `erdos:556` (`conjectures/X4.v:185`) — severity: **too weak (disclosed, necessary)**. The
  literal `R_3(C_n) <= 4n-3` is false for small `n` (`n = 3`: `R_3(K_3) = 17 > 9`), so the body
  adds an existential threshold `n0`.
- `opg:circular_colouring_the_orthogonality_graph` (`conjectures/D2chr.v:435`) — severity:
  **proxy**. Vertices are all 3-vectors rather than the lines through the origin, so each line
  becomes an independent set of its non-zero multiples and `0` is isolated. Invariant for the
  circular chromatic number, but a representative model rather than the source object.
- `opg:linear_hypergraphs_with_dimension_3` (`conjectures/D2str.v:190`) — severity: **proxy**.
  The incidence poset is taken on the full ground type `T + {set T}` (non-hyperedge subsets sit as
  isolated points) and the plane is an arbitrary ordered field rather than `R`.
- `arxiv:2505.24100#00` / `#01` (`conjectures/X49.v:41`, `conjectures/X60.v:50`) — severity:
  **corpus text garbled, repaired in the encoding**. Both `statement_text`s say "`G` is `H`-free"
  with `H` undefined; the bodies use the intended reading "no induced `C_{2t-2}`".
- Cross-cutting pattern (not a single row): the Erdős Ramsey/Turán rows pass the extremal quantity
  as a PARAMETER constrained by a minimality/maximality predicate
  (`xe1_graph_ramsey_number`, `xe1_size_ramsey_number`, `x4_turan_number`,
  `xe1_turan_number_for_graph`, `xe2_incident_chord_extremal`, `is_alpha`, ...). Every instance in
  which that extremal value does not exist is vacuously true. This is sound but makes non-vacuity
  a *grounding* obligation rather than a property of the statement; `erdos:545`, `erdos:766`,
  `erdos:85`, `erdos:812`, `erdos:87`, `erdos:767` are the most exposed.

### Other

- **Dead and buggy**: `conjectures/XE1.v:88 xe1_triangle_free_diameter_completion_edges` ignores
  its own parameter `F` — both clauses use `@xe1_delete_edges G set0`, so the predicate says
  nothing about the `h` edges and is equivalent to "`G` is triangle-free of diameter `<= r`". It is
  used by NO statement (`erdos_619_statement` uses
  `xe1_triangle_free_diameter_completion_number`, XE1.v:242, which is correct). Delete it or fix
  it to `xe1_add_edges G F`.
- **Dead definitions** (unused by any statement or lemma in their file):
  `conjectures/XE2.v:91 xe2_cycle_diagonal_count`, `conjectures/XE2.v:29 xe2_path_in_graph`,
  `conjectures/XE1.v:16 xe1_has_independent_set`, `conjectures/X88.v:12 x88_clique_count` (the
  last one deliberately: the in-file comment explains why `D_r` replaced the clique count as the
  dominated quantity).
- **Misnamed constant**: `conjectures/X88.v:66
  pentagonal_turan_stability_dominates_clique_count_statement` no longer dominates a CLIQUE COUNT —
  the dominated quantity is `x88_edit_to_r_partite` (`D_r`, the edit distance to `r`-partiteness).
  The name contradicts the body and its own explanatory comment.
- **Corpus row with no `formal_name`**: `arxiv:2103.15175#00` (repo `extremal-graph-theory`, status
  open, "For `s >= 2`, if `H_s` is the family of graphs with chromatic number greater than `s`,
  then `R_l(H_s, k) = s^k + 1`") is PROVED in this package four times over
  (`foundations/list_ramsey.v:207 list_ramsey_chromatic_statement`,
  `applications/list_ramsey_nat.v:101 list_ramsey_natural_statement`,
  `applications/list_ramsey_graph.v:130 list_ramsey_chromatic_graph_statement`,
  `applications/list_ramsey_graph.v:212 list_ramsey_chromatic_resolution_statement`), yet the row
  carries `formal_name: null`, so the gate forces all four to be documented as `No corpus row`.
  Registering the source-facing one (`list_ramsey_chromatic_resolution_statement`) as the row's
  `formal_name` would turn an open row into a recorded resolution. The two sibling rows
  `arxiv:2103.15175#01` and `studies:std_growth_rate_of_list_ramsey_numbers_alon_buci_kal` have
  `repo: null`.
- **Existing prose preserved**: five in-file comments carried load-bearing content and were folded
  into the new blocks before being removed (`erdos_802_statement` on `trunc_log 2` vs `logn 2` and
  the average-degree direction; `erdos_547_statement` on the `2 <= n` guard;
  `erdos_803_statement` on `trunc_log` and the `1 <= m` guard;
  `three_colour_cycle_ramsey_bound_statement` on the `n0` threshold; the `M_c` infimum comment of
  `mixing_circular_colourings_0_statement`). The `Row N` header comments of `D2chr.v`, `D2pr.v`,
  `D2ram.v`, `D2str.v`, `D2tur.v` are not adjacent to their `Definition` and were left in place.
- **Comment hazard found while writing**: a doc block containing the substring `G*)` (from
  `e(G*)`) silently closes the Rocq comment early. Detected by the gate on
  `pentagonal_turan_stability_dominates_clique_count_statement` and rewritten as `e(Gstar)`. Worth
  a lint in `check_statement_docs.py`: no `*)` inside a doc block body.

## cycle-theory — bridgeless/simple_mgraph repair (2026-09-23)

Foundation repair answering blockers A and B of the `X212`/`X228:cycle-theory`
sections of `meta/X211-X229_faithfulness_audit.md`. **No statement body changed**
— every `Definition …_statement` is textually identical to what was committed;
the meaning change comes entirely from the two foundation definitions below.

### What was wrong

1. `Cycle.foundations.connectivity.is_bridge` was
   `eseparates (source e) (target e) [set e]`, and coq-graph-theory's
   `eseparates` quantifies over the **directed** `walk`
   (`walk x y (e :: w) = (source e == x) && walk (target e) y w`). So
   `bridgeless G` demanded an alternative *directed* route `u ⇝ v` for every arc
   `u → v`. Consequences the reader proved: a cyclically oriented triangle is not
   bridgeless; a simple carrier in the class has minimum degree ≥ 4; a cubic
   loopless multigraph in it is a disjoint union of triple-edge dipoles — no
   cycle, no Petersen graph, no snark.
2. `U6.simple_mgraph` bounded `#|edges x y|`, and `mgraph.edges x y` is
   **directed**, so a pair of *antiparallel* arcs — a doubled edge of the
   underlying undirected multigraph — passed as "simple". That made
   `small_cycle_double_cover_statement` axiom-free refutable
   (`meta/probe_hints/small_cycle_double_cover_statement.v`).

### The repaired definitions (verbatim)

`cycle-theory/theories/foundations/connectivity.v`:

```coq
Definition ueseparates (G : mgraph) (x y : G) (E : {set edge G}) : Prop :=
  forall w : seq (edge G), uwalk x y w -> exists2 f, f \in E & f \in w.

Definition is_bridge (G : mgraph) (e : edge G) : Prop :=
  ueseparates (source e) (target e) [set e].

Definition bridgeless (G : mgraph) : Prop :=
  forall e : edge G, ~ is_bridge e.
```

`cycle-theory/theories/conjectures/U6.v`:

```coq
Definition simple_mgraph (G : mgraph) : Prop :=
  loopless G /\ forall x y : G, (#|edges x y| + #|edges y x| <= 1)%N.
```

`two_edge_connected` (= `mconnected G /\ bridgeless G`) is unchanged textually
and inherits the repair. The foundation header now states the **carrier
convention** explicitly: an `mgraph` here encodes an *undirected* multigraph,
one arc per edge, the `source`/`target` split being a reference orientation with
no mathematical content; every notion must be invariant under reversing an arc.
Audited for that invariance: `mdeg`/`subdeg` (through `edges_at`/`incident`,
already symmetric — so `even_subgraph`, `subgraph_kregular`, `two_factor`,
`is_matching`, `cubic` are undirected degrees), `cut S` (an exclusive-or of the
two endpoints), all connectivity predicates (already on `uwalk`). The only
directed reader left is `mgraph.edges x y`, now always used as the sum
`#|edges x y| + #|edges y x|`; the one remaining use of coq-graph-theory's
directed `walk` in the package is `U6.is_eulerian_tour`, where a tour genuinely
is a sequence.

### Statements affected (bodies unchanged, `Notes:` rewritten)

| file | statement | change |
|---|---|---|
| `D1.v` | `five_flow_statement` | `bridgeless` = no cut edge |
| `U6.v` | `cycle_double_cover_statement` | idem |
| `U10.v` | `the_berge_fulkerson_statement`, `petersen_coloring_statement`, `intersecting_two_perfect_matchings_statement` | `cubic_bridgeless` no longer forces triple-edge dipoles |
| `X212.v` | `small_cycle_double_cover_statement` (bm-013) | both defects fixed; refutation hint now stale |
| `X212.v` | `orientable_five_cycle_double_cover_statement` (bm-026) | `two_edge_connected` = connected + no cut edge |
| `X228.v` | `half_flow_pair_statement` | snarks are back in the hypothesis class |

The "directed-walk bridgeless is stronger than no cut edge" caveats written by
the documentation pass and by the reader are removed and replaced by `REPAIRED
(foundation repair, 2026-09-23)` paragraphs. No `Corpus row` / `Site` / `Review`
/ `English statement` line changed: the English already said "bridgeless" /
"no bridge", which is now what the Rocq says.

### Lemmas proving the repaired notions behave as intended

New in `cycle-theory/theories/conjectures/grounding_X212.v` (all `Qed`,
`Print Assumptions` → *Closed under the global context*), on the cyclically
oriented triangle `Tri` (three vertices `option bool`, one arc `v → x212_rot v`
per vertex — every arc oriented the same way round the cycle, the configuration
the old definition rejected):

* `x212_bridgeless_Tri : bridgeless Tri` — the triangle **is** bridgeless;
* `x212_mconnected_Tri`, `x212_two_edge_connected_Tri` — and 2-edge-connected;
* `x212_edges_Tri`, `x212_card_edges_Tri`, `x212_simple_Tri : simple_mgraph Tri`
  — and genuinely simple;
* `x212_small_cdc_hypotheses_Tri` — so the hypothesis class of bm-013/bm-026 has
  a three-vertex, three-edge witness, not merely the degenerate corner;
* `x212_is_bridge_G1 : forall e : edge G1, is_bridge e` and
  `x212_not_bridgeless_G1 : ~ bridgeless G1` — a genuine **cut edge** (two
  vertices joined by a single edge) **is** a bridge, so the notion has teeth;
* `x212_not_simple_Gd : ~ simple_mgraph Gd` — the **doubled edge** carried by two
  antiparallel arcs is rejected (this is exactly the loophole the refutation
  exploited).

Supporting general lemmas added to `foundations/connectivity.v`: `uwalk_cons`,
`uwalk_cons_rev`, `uwalk_one`, `uwalk_one_rev`, `is_bridgeP`,
`not_bridge_detour`, `loop_not_bridge`, `uwalk_crosses`.

### Proofs repaired

* `grounding_U6.simple_mgraph_unit` — two `edges` terms to kill instead of one.
* `grounding_U10.bridgeless_Gt` — directed one-edge detour → `uwalk_one`.
* `implications_U6`: the local directed `walk_crosses` was deleted and
  `bridgeless_cut2` now goes through the foundation's `uwalk_crosses`; the
  scheduled edge `faithful_cycle_covers_statement ⟹ cycle_double_cover_statement`
  is unchanged and still `Qed`.
* `implications_X228` (edge `e174`, `half_flow_pair_statement ⟹
  five_flow_statement`) needed **no** change: its proof never unfolds
  `bridgeless`, it only passes the hypothesis along — but both endpoints now
  carry the repaired hypothesis, so the edge is no longer a consistency check
  between two crippled statements.
* `grounding_X212.x212_bridgeless_G2p` and `grounding_X228.x228_bridgeless_G2p`
  compiled unchanged (their `isT` walk witnesses still compute under `uwalk`);
  only their comments, which claimed the antiparallel digon `Gd` is *not*
  bridgeless, were corrected — under the repaired definition it is.

### Verification

* `make cycle-theory`: clean, 62/62 `Print Assumptions` → *Closed under the
  global context*.
* `check_milestone.py … cycle-theory` for `D1`, `U6`, `U10`, `X212`, `X228`
  (and `X5`, `X9`, `X10`, `X24`, `XE1`, `XE2`, `X184`): all **ACCEPTED**.
* `check_statement_docs.py cycle-theory`: 56/56 documented, **0 errors**,
  52/52 rows covered.
* `vacuity_probe.py --names small_cycle_double_cover_statement,cycle_double_cover_statement,five_flow_statement,half_flow_pair_statement,orientable_five_cycle_double_cover_statement`:
  5 probed, 0 flagged; `small_cycle_double_cover_statement` reports
  **`hint-stale-FIX-OK`** — the committed refutation no longer compiles, which is
  the fix-verification signal. The hint file itself is kept unchanged apart from
  a header note recording that it is stale by design.


### Loop degree: `subdeg` now counts arc ends (2026-09-23)

**What was wrong.** `Cycle.foundations.connectivity.subdeg H v` was
`#|edges_at v :&: H|` — the number of edges INCIDENT with `v` — so a **loop at
`v` contributed 1 instead of 2**. Every textbook convention gives a loop degree
2; that is exactly what makes a single loop a cycle (an element of the binary
cycle space, a circuit of length 1) and what makes the degree sum twice the
number of edges. Under the old reading the one-vertex one-loop multigraph
`Lp = mgraph.add_edge (unit_graph tt) tt tt tt` had `mdeg = 1`, so
`U6.even_subgraph [set: edge Lp]` was false (1 is odd) and
`connectivity.is_circuit [set: edge Lp]` was false
(`subgraph_kregular _ 2` wants 0 or 2 and got 1) — while `Lp` is `mconnected`
and `bridgeless` (a loop is never a cut edge,
`connectivity.loop_not_bridge`), hence `two_edge_connected`. Its only edge had
to be covered twice and every candidate member containing it was the whole edge
set, so the conclusions were unsatisfiable and two rows were axiom-free
**refutable** on this one graph, although the conjectures plainly hold there
(cover the loop twice). This was the second, independent defect found by the
second-reader re-read of the bridgeless/`simple_mgraph` repair, recorded in
`meta/X211-X229_faithfulness_audit.md`, section "A SECOND, independent defect:
`subdeg` counts a loop once".

**The new definition** (`cycle-theory/theories/foundations/connectivity.v`):

```coq
Definition ends_at (G : mgraph) (H : {set edge G}) (b : bool) (v : G) : {set edge G} :=
  [set e in H | endpoint b e == v].
Definition subdeg (G : mgraph) (H : {set edge G}) (v : G) : nat :=
  #|ends_at H false v| + #|ends_at H true v|.
Definition mdeg (G : mgraph) (v : G) : nat := subdeg [set: edge G] v.
```

`subdeg H v` is the number of **arc ENDS** of `H` at `v`: reversing an arc swaps
its two contributions, so the count is symmetric in `source`/`target` (the
carrier convention of the package), and a loop, having both ends at `v`,
contributes 2. Two lemmas bound the change:

* `subdegE : subdeg H v = #|edges_at v :&: H| + #|[set e in H | (source e == v) && (target e == v)]|`
  — the identity *degree = incidences + loops*, i.e. exactly how far the new
  reading differs from the old one;
* `subdeg_loopless : loopless G -> subdeg H v = #|edges_at v :&: H|`
  (and `mdeg_loopless`) — **on a loopless carrier the two readings agree**, so
  no row guarded by `loopless`, `cubic` or `simple_mgraph` changes meaning.

Supporting lemmas added alongside: `incidentE`, `ends_atU`, `ends_atI`,
`ends_at1`, `subdeg_loop` (`source e = v -> target e = v -> subdeg [set e] v = 2`),
`ends_at_sub`, `subdeg_sub`, `subdeg_mdeg`, `subdeg0`, `mdeg_gt0_edge`.

#### Which rows changed meaning

| File | Row | Effect of the repair |
|---|---|---|
| `U6.v` | `cycle_double_cover_statement` (OPG, statement leg `done`) | **was refutable**: the loop graph is bridgeless with an edge, and no member could be a circuit. Now the loop is a circuit and `cdc` is realised on it (`grounding_U6.cdc_Gloop`). |
| `X212.v` | `orientable_five_cycle_double_cover_statement` (bm-026, `open`) | **was refutable**: the loop graph is 2-edge-connected and no member containing its edge was an `even_subgraph`. Now the row's conclusion is *exhibited* on it (`grounding_X212.x212_orientable_5_Lp`). |
| `U6.v` | `m_n_cycle_covers_statement` (OPG, guarded only by `bridgeless`) | **was refutable by the same graph and the same argument** (five `even_subgraph` members, two of them containing the loop): the two refutation hints never spelled this one out, but the repair fixes it too — take `C0 = C1 = [set: edge Lp]`, the other three empty, now machine-checked as `grounding_X212.x212_m_n_cover_Lp`. Worth a second reader's attention. |
| `U6.v` | `strong_5_cycle_double_cover_statement`, `odd_cycles_and_low_oddness_statement`, `cycle_double_covers_containing_predefined_2_regular_statement` | **unaffected**: all guarded by `cubic`, which forces `loopless`. |
| `U6.v` | `decomposing_an_eulerian_graph_into_cycles_statement` | **unaffected**: guarded by `simple_mgraph`, which forces `loopless`. |
| `U6.v` | `decomposing_an_eulerian_graph_into_cycles_with_no_tw_statement` | **corrected 2026-09-23** (the line above used to lump the three eulerian rows together): this row is guarded by `eulerian G` and `forall v, 4 <= mdeg v`, **not** by `simple_mgraph`, so its carrier class DID grow — the one-vertex two-loop multigraph has `mdeg = 4` now and had `mdeg = 2` before. No refutation: on that carrier `[:: [set e1]; [set e2]]` is a cycle decomposition (each loop is now a circuit) and neither member holds two cyclically consecutive edges of the tour `[:: e1; e2]`. **PASS.** |
| `U6.v` | `decomposing_eulerian_graphs_statement` (`edge_connected G 6` + `eulerian G`, no looplessness) | **FOURTH victim, was refutable** (found by the second-reader re-read, 2026-09-23): on the one-vertex two-loop multigraph — eulerian, 6-edge-connected, with the 2-transition system `P v = [set [set e1; e2]]` — the old degree made a single loop a non-circuit, so the ONLY cycle decomposition was `[:: [set e1; e2]]`, whose trace at the vertex IS the transition: no compatible decomposition existed. With a loop of degree 2 the row is realised there, `grounding_U6.u6_decomposing_eulerian_G2loop` (hypotheses + conclusion) via `compatible_decomposition_G2loop`. |
| `D1.v` | `five_flow_statement` | **unaffected**: it does not mention `mdeg`; only its `bridgeless` hypothesis was repaired earlier. |
| `D1.v` | `circular_flow_numbers_of_r_graphs_statement` (`mreg`) | **unaffected, and now machine-checked to be so**: its `is_2t1_graph G t` guard FORCES looplessness — `grounding_D1.is_2t1_loopless`, from `grounding_D1.mdeg_cut` (`mdeg v = #|cut [set v]| + 2·#|loops_at v|`): the singleton `[set v]` is an odd vertex set, so `2t+1 <= #|cut [set v]|` and `mdeg v = 2t+1` leaves no room for a loop. The carrier class is the source's under either convention. |
| `D1.v` | `circular_flow_number_of_regular_class_1_graphs_statement` (`mreg`, `mDelta`) | **DEFECT — repaired 2026-09-23 by adding `loopless G` to the body** (corrects the earlier "unaffected in substance" claim on this row, which was true only of its sibling). It had NO odd-cut and no `loopless` guard, so when a loop started counting 2 its carrier class strictly GREW: base's `line_graph` makes a loop non-adjacent to ITSELF, so `chromatic_index` stays finite and `is_class1` can hold on loopful carriers, where the source's edge chromatic number is undefined (a graph with a loop has no proper edge colouring). Witness: four vertices, three parallel edges `x—y`, a loop at `u`, an edge `u—v`, a loop at `v` — `mreg _ 3`, `mDelta = χ' = 3`, hence class 1, yet with NO nowhere-zero `r`-flow for any `r` (at `u` the loop cancels in `rconservative`, forcing `phi(u—v) = 0`). The row was thus SPURIOUSLY refutable, by a graph the source excludes rather than by the published Mattiolo–Steffen counterexamples. Teeth and non-vacuity: `grounding_D1.class1_3reg_loopful_Gcl` and `grounding_D1.loopless_class1_3reg_G3p`. |
| `X212.v` | `small_cycle_double_cover_statement` (bm-013) | **unaffected**: `simple_mgraph` forces `loopless`, so `subdeg_loopless` applies. |
| `U10.v` | `the_berge_fulkerson_statement`, `petersen_coloring_statement`, `intersecting_two_perfect_matchings_statement` | **unaffected**: `cubic` forces `loopless`. |
| `X228.v` | `half_flow_pair_statement` | **unaffected**: `cubic_bridgeless` forces `loopless`. |

No `Corpus row` / `Site` / `Review` line changed. One `Definition
…_statement` body changed later, in the second-reader follow-up below
(`circular_flow_number_of_regular_class_1_graphs_statement` gained `loopless G`);
no body changed in the repair pass itself. The `Definitions:` clauses that described `subdeg`
/ `mdeg` as "the number of edges incident with v" now say "the number of ARC
ENDS at v, so a loop contributes 2"; the `STILL BLOCKED (second-reader re-read,
2026-09-23)` paragraph of bm-026 is replaced by a `LOOP-DEGREE REPAIR
(2026-09-23, main session)` paragraph, the bridgeless-repair paragraph being
kept.

#### Lemmas pinning the repaired convention

In `cycle-theory/theories/conjectures/grounding_U6.v`, on the loop graph
`Gloop := mgraph.add_edge U tt tt tt`: `subdeg_Gloop`/`mdeg_Gloop` (degree 2),
`even_subgraph_Gloop`, `subgraph_kregular_Gloop`, `subgraph_connected_Gloop`,
`is_circuit_Gloop`, `two_factor_Gloop`, `mconnected_Gloop`, `bridgeless_Gloop`,
`two_edge_connected_Gloop`, `cdc_Gloop`, and the teeth lemma
`not_matching_Gloop` (a loop can never sit in a matching).

New in `cycle-theory/theories/conjectures/grounding_X212.v`, section
*The LOOP GRAPH `Lp` and the loop-degree repair*, with `Lp := Gloop` — the same
construction as the `Lp` of the two refutation hints, so the three agree
definitionally (all `Qed`, `Print Assumptions` → *Closed under the global
context*):

* `x212_card_Lp`, `x212_card_edge_Lp` — one vertex, one edge;
* `x212_mdeg_Lp : forall v : Lp, mdeg v = 2` and `x212_subdeg_Lp` — **the point
  of the repair**;
* `x212_even_subgraph_Lp`, `x212_subgraph_kregular_Lp`,
  `x212_subgraph_connected_Lp`, `x212_is_circuit_Lp` — the single loop is an
  even subgraph and a circuit;
* `x212_two_edge_connected_Lp`, `x212_orientable_5_hypotheses_Lp` —
  NON-VACUITY: `Lp` satisfies every hypothesis of bm-026 (and of the CDC row);
* `x212_cdc_Lp` — the CDC conclusion on `Lp` (cover the loop twice);
* `x212_m_n_cover_Lp` — the (5,2)-cycle-cover conclusion on `Lp`
  (`U6.m_n_cycle_covers_statement`, the third row the old convention refuted);
* `x212_Lp_cover`, `x212_Lp_dir`, `x212_Lp_coverE`, `x212_Lp_even`,
  `x212_Lp_vertex`, `x212_Lp_balanced`, `x212_Lp_cover_card`,
  `x212_Lp_opposite` — the explicit five-member cover: the loop in members
  `ord0` and `ord_max`, oriented oppositely there, the other three empty;
* `x212_orientable_5_Lp : x212_orientable_5_even_double_cover Lp` and
  `x212_orientable_5_loop_instance` — **the conjecture holds on the loop
  graph**, hypotheses and conclusion together.

#### Mutation canary

`meta/faithfulness_mutation.py` gains `cycle_subdeg_counts_loop_once` (phase
`X212`, package `cycle-theory`): it reverts `subdeg` to `#|edges_at v :&: H|`
and requires `check_milestone.py` to reject the mutant with
`[FAIL] package compiles`. Run: **1/1 killed**. The mutant dies inside the
foundation (`connectivity.subdeg_loop`) and, were that lemma removed, downstream
at `grounding_U6.mdeg_Gloop` / `grounding_X212.x212_mdeg_Lp`.

#### Verification

* `make cycle-theory -j4`: exit 0, **91/91** `Print Assumptions` → *Closed under
  the global context* (the 20 new `x212_*_Lp` lemmas among them, re-audited
  individually).
* `check_milestone.py <P> cycle-theory` for `D1`, `U6`, `U10`, `X212`, `X228`:
  all **ACCEPTED**, 11/11 checks each; statements 15/15, 11/11, 3/3, 8/8, 1/1
  Defined and axiom-free.
* `check_statement_docs.py cycle-theory`: 56 targets, 56 documented, **0
  errors**, reverse coverage 52/52.
* `vacuity_probe.py --names small_cycle_double_cover_statement,cycle_double_cover_statement,five_flow_statement,half_flow_pair_statement,orientable_five_cycle_double_cover_statement`:
  **5 probed, 0 flagged**; `cycle_double_cover_statement`,
  `orientable_five_cycle_double_cover_statement` and
  `small_cycle_double_cover_statement` all report **`hint-stale-FIX-OK`** — the
  three committed refutations no longer compile, which is the fix-verification
  signal. The hint files are kept unchanged apart from a `STALE BY DESIGN since
  the loop-degree repair of 2026-09-23` header note added to
  `meta/probe_hints/cycle_double_cover_statement.v` and
  `meta/probe_hints/orientable_five_cycle_double_cover_statement.v` (the
  `small_cycle_double_cover_statement` hint already carried one from the
  bridgeless repair).
* `faithfulness_mutation.py --mutant cycle_subdeg_counts_loop_once`:
  **ACCEPTED: 1/1 mutation canaries killed**.

#### Second-reader follow-ups (2026-09-23)

Prescribed by the re-read recorded in
`meta/X211-X229_faithfulness_audit.md` (*Re-read after the loop-degree repair*
and its *Addendum*), applied in this session.

**Body change (one row).**

```coq
(* before *)                                  (* after *)
(1 <= t)%N -> (0 < #|G|)%N ->                 (1 <= t)%N -> (0 < #|G|)%N -> loopless G ->
mreg G (2 * t + 1)%N -> is_class1 G ->        mreg G (2 * t + 1)%N -> is_class1 G ->
```

in `circular_flow_number_of_regular_class_1_graphs_statement` (`D1.v`,
OPG row `opg:circular_flow_number_of_regular_class_1_graphs`), with a
`LOOPLESS GUARD (2026-09-23, second-reader prescription)` paragraph in its
`Notes:`, `loopless` added to the `English statement:` and `[loopless]` to the
`Definitions:`. The `D1.v` header note, which claimed both `mreg`/`mDelta` rows
"read exactly as before", is corrected to separate the two rows, and so is the
per-row table above.

**Doc gaps closed (two rows, bodies unchanged).** `U6.m_n_cycle_covers_statement`
(third victim) and `U6.decomposing_eulerian_graphs_statement` (fourth victim)
each gained a `LOOP-DEGREE REPAIR (2026-09-23)` paragraph in their `Notes:`,
the second one also recording the residual notion-level remark that
`transition2_system` partitions an incidence set rather than the edge ends.

**Lemmas added** (all `Qed`, all `Print Assumptions` → *Closed under the global
context*; 42 audited).

`cycle-theory/theories/conjectures/grounding_D1.v`:

* `loops_at`, `cutI_loops`, `cutU_loops`, `mdeg_cut`
  (`mdeg v = #|cut [set v]| + (#|loops_at v| + #|loops_at v|)`) and
  `is_2t1_loopless : is_2t1_graph G t -> loopless G` — the reader's proof,
  ported: *why the sibling row needs no guard*;
* `card_ends_at_add`, `mdeg_add_edge`
  (`mdeg (add_edge G x y tt) v = mdeg v + ((x == v) + (y == v))`) and
  `mDelta_mreg` — degree bookkeeping for `add_edge`, reusable;
* NON-VACUITY: `G2p`/`G3p` (the triple edge) with `loopless_G3p`, `mreg_G3p`,
  `mDelta_G3p`, `clique_line_G3p`, `chromatic_index_G3p` (= 3, its line graph
  is a triangle), `is_class1_G3p` and
  `loopless_class1_3reg_G3p : [/\ 0 < #|G3p|, loopless G3p, mreg G3p (2*1+1) & is_class1 G3p]`;
* TEETH: the loopful carrier `Gcl` (three parallel `x—y`, a loop at `u`, `u—v`,
  a loop at `v`) with `mreg_Gcl`, `not_loopless_Gcl`, the explicit proper
  3-edge-colouring `coloring_Gcl` ({`ea`,`elu`,`elv`} / {`eb`,`eh`} / {`ec`}),
  `clique_abc_Gcl` + `chromatic_index_Gcl` (= 3), `mDelta_Gcl`, `is_class1_Gcl`
  and
  `class1_3reg_loopful_Gcl : [/\ 0 < #|Gcl|, mreg Gcl (2*1+1), is_class1 Gcl & ~ loopless Gcl]`
  — the guard is the ONLY hypothesis that excludes it. (The reader left this
  counterexample on paper; it is now machine-checked, by explicit
  `partition`/`stable`/`clique` case splits rather than by `vm_compute`.)

`cycle-theory/theories/conjectures/grounding_U6.v`, the two-loop carrier
`G2loop := mgraph.add_edge Gloop tt tt tt`:

* `card_edge_G2loop`, `edgeT_G2loop`, `ends_at_G2loop`,
  `mdeg_G2loop : forall v, mdeg v = 4` (2 under the old convention),
  `mconnected_G2loop`, `eulerian_G2loop`, `edge_connected_G2loop`,
  `edges_at_G2loop`, `card_G2loop`;
* `Ptwo`, `lp12_neq`, `transition2_G2loop` — the transition system pairing the
  two loops;
* `is_circuit_loop_G2loop` (each loop is a circuit of length 1),
  `cycle_decomposition_G2loop`, `compatible_decomposition_G2loop` and
  `u6_decomposing_eulerian_G2loop` — the hypotheses AND the conclusion of
  `decomposing_eulerian_graphs_statement` on that carrier.

**Verification of the follow-up.** `make cycle-theory -j4` exit 0;
`check_milestone.py` ACCEPTED for `D1`, `U6`, `U10`, `X212`, `X228` (11/11
each); `check_statement_docs.py cycle-theory` 56/56 documented, 0 errors;
`vacuity_probe.py --names circular_flow_number_of_regular_class_1_graphs_statement,circular_flow_numbers_of_r_graphs_statement,decomposing_eulerian_graphs_statement,m_n_cycle_covers_statement`
4 probed, 0 flagged; `faithfulness_mutation.py --mutant cycle_subdeg_counts_loop_once`
still 1/1 killed; `formal_resolutions.py --metadata-only` OK (7 entries — the
class-1 row is not a registered resolution, so the body change touches none).

## base — surface vertex count repair (2026-09-23)

**Where the defect came from.** The second reader's re-read of the five repaired
chromatic rows (`meta/X211-X229_faithfulness_audit.md`, section *Re-read of the
five repaired chromatic rows (2026-09-23)*, part "What `surface_embeddable`
actually means") derived `base/theories/surface.v` line by line and recorded an
**isolated-vertex wrinkle**: `surface_embedding_vertices E :=
#|porbits (surface_erot E)|` counts only the vertices that CARRY A DART, because
`surface_erot_vertex` makes each rotation orbit exactly the dart set of one
vertex. Isolated vertices were therefore invisible to `V`, so
`surface_euler_genus = (2 + E - V - F) %/ 2` OVERSTATED the genus of every graph
with an isolated vertex; an edgeless graph came out with `V = E = F = 0` and
genus 1, and the reader machine-checked `~ surface_embeddable 0 'K_1` although
`K_1` is planar.

**Direction of the defect: too weak.** Every consumer is of the shape "for every
`g`, every graph with `surface_embeddable g G` satisfies …". An overstated genus
makes the hypothesis HARDER to satisfy, so those statements silently quantified
over fewer graphs than the sources do.

**Fix.** `surface_embedding_vertices (E : surface_embedding) : nat := #|G|` —
the textbook `V`, every vertex counted, isolated ones included. The parameter
`E` is kept, so no call site changed. The comment above `surface_euler_genus`
now states the convention, keeps the connected-graph guard remark (the formula
hard-codes the connected-map relation and understates a `c`-component genus by
`c-1`) and records the one residual truncation wrinkle: the EMPTY graph still
evaluates to `(2 - 0 - 0) %/ 2 = 1`.

**Lemmas added in `base/theories/surface.v`** (all `Qed`, all `Print
Assumptions` → *Closed under the global context*):

* `surface_embedding_vertices_orbits : #|porbits (surface_erot E)| =
  #|[set v : G | [exists d : surface_dart, (sval d).1 == v]]|` — pins down what
  the OLD count was (the number of non-isolated vertices), and shows old and new
  agree as soon as every vertex carries a dart. Proof: the orbit set is the
  image of the dart-carrying vertices under `v ↦ [set d | (sval d).1 == v]`,
  injectively, then `card_in_imset`.
* `surface_edgeless_genus0 : (forall d : surface_dart, False) -> 0 < #|G| ->
  exists E, surface_euler_genus E = 0` — the identity rotation on the empty dart
  type, `(2 - #|G|) %/ 2 = 0`.
* `surface_embeddable_edgeless` — the same as `surface_embeddable 0 G`.
* `surface_no_dart_K1`, `surface_embeddable_K1 : surface_embeddable 0 'K_1` —
  the CANARY. With the old count this was refutable; it is what kills the new
  mutation canary.

**Statements whose meaning moved, and in which direction.** No statement body
changed; all of them got STRICTLY STRONGER, because the repaired `V` is larger,
`2 + E - V - F` is smaller over truncating `nat`, the computed genus is smaller
or equal and `surface_embeddable g G` therefore holds for MORE graphs. The
graphs that re-enter are exactly those with an isolated vertex — in particular
every nonempty edgeless graph now sits at genus 0 instead of 1. Affected rows:
`chromatic-theory` X150, X152, X164, X210, X213 (bm-053) and X219 (the three
toroidal rows), `graph-theory-misc` X167, `topological-graph-theory` X138, X202
and `D3D6_unblocked`. Each of their doc blocks now carries the sentence "V
counts every vertex including isolated ones (base fix 2026-09-23) …".
`grounding_X213.v` keeps `x213_surface_embeddable_no_dart` (the `<= 1` bound is
still true, now with slack) and `x213_connected_guard_has_teeth` (the two-vertex
edgeless graph is still accepted and still disconnected) — both comments were
rewritten, since the arithmetic behind them changed: the witness is now admitted
at computed genus 0 through the whole-graph Euler formula, not through the
isolated-vertex blind spot.

**`topological-graph-theory/theories/foundations/embedding.v`: same defect, same
fix applied.** `emV (E : embedding) := #|porbits (erot E)|` had the identical
blind spot (its `SCOPE CAVEAT` comment already named it). The consumers
(`U2` via `k_connected G 4`, `U13`, `D6emb` and `X80` via `connected [set: G]`)
all carry a connectivity guard, under which the ONLY graph where the two counts
differ is `K_1`, so the defect was provably harmless there — but no proof in the
tree unfolds `emV`, the two foundations are twins, and a future consumer would
inherit the blind spot, so the one-line fix was applied as well: `emV := #|G|`,
plus `emV_orbits`, `edgeless_planar_embedding`, `no_dart_K1`,
`planar_embedding_K1` and `embeds_in_genus_K1_0` (all axiom-free), and the
`SCOPE CAVEAT` comments of `embedding.v` and `signed_embedding.v` rewritten
(the connected-map / `c-1` half stays, the isolated-vertex half is gone, the
empty-graph truncation stays). Consumer meaning: `U2`, `X80`, `D6emb` unchanged
(4-connectivity and min-degree-3 exclude `K_1`; `toroidal K_1` held before and
after); `U13` unchanged as a statement — `K_1` now passes
`planar_embedding`+`triangulation`, so its EXISTENTIAL order threshold `n0`
simply has to exceed 1, which its doc block now says. `seuler_genus` of
`signed_embedding.v` is defined through the same `emV`, so the audited identity
`seuler_genus (emap_of E) = 2 * euler_genus E` is unaffected.

**Not fixed, on purpose.** (1) The EMPTY graph still computes genus 1 in both
layers — pure `nat`-truncation artefact of `2 + E - V - F`; repairing it would
mean changing the formula, not the vertex count. (2) The whole-graph Euler
formula still understates the genus of a disconnected graph by `c-1`; that is
what the connectivity guards every consumer carries are for.

**Verification.** `make all -j4` exit 0; `make digraph-theory -j4` exit 0;
`check_milestone.py` ACCEPTED (11/11 each) for X213, X219, X210, X150, X152,
X164 (chromatic-theory), X167, X80 (graph-theory-misc), X138, X202, X228, U13,
D6emb (topological-graph-theory), U13 (packing-theory), U2
(hamiltonicity-theory); `check_statement_docs.py` 741/741 documented, 0 errors;
`vacuity_probe.py --files base/theories/surface.v
chromatic-theory/theories/conjectures/X213.v
chromatic-theory/theories/conjectures/X219.v` → **13 probed · 0 FLAGGED**
(every row `auto=T False / auto=F False`, the four toroidal rows included);
`faithfulness_mutation.py --mutant base_surface_vertices_orbit_count` 1/1
killed by `[FAIL] package compiles`. Recorded in `tactics-playbook.md`
(entries 229–232).

## Vocabulary equivalences proved (wave V, 2026-09-24)

Wave V discharges the "duplicated vocabulary" obligations of the eight packages
`extremal-graph-theory`, `hypergraph-theory`, `reconstruction-theory`,
`spectral-graph-theory`, `homomorphism-theory`, `packing-theory`,
`topological-graph-theory`, `graph-theory-misc`: for each group of copies listed
in the per-package sections above (and in the `x223` / `x215` ledger items of
`meta/X211-X229_faithfulness_audit.md`), ONE `Qed`-closed lemma now ties the
local spelling to the canonical notion.  **No statement body was changed**;
every lemma is `Print Assumptions`-clean ("Closed under the global context"),
and all eight packages still build (`make <pkg>` exit 0), with
`check_milestone` ACCEPTED for U3 / U11 / X215 / X223 / D5,
`check_statement_docs` 0 errors for all eight, and
`check_edges --assumptions --package extremal-graph-theory` ACCEPTED (3/3).

**Placement convention.**  A lemma mentioning only foundation/library notions
went to a `theories/foundations/` file; a lemma mentioning a notion of a
`theories/conjectures/X*.v` file went to the conjectures layer, since a
foundations file must not import a conjectures file.  Where the phase already
had an `implications_<phase>.v` file the lemma went there (U3, U11, X215, X223);
the remaining phases (X5, X6, X14, X15, X18, X20, X25, X26, X37, X38, X47, X72,
X73, X77, X102, X104, X108, X113, X117, X119, X137, X158, X209, XE1) have no
`implications_`/`grounding_` file, so the bridges were collected in one new
`theories/conjectures/vocabulary_<pkg>.v` per package rather than in
twenty-four new per-phase files.  Three new files were added to
`theories/foundations/`: `extremal-graph-theory/.../degree_bounds.v`,
`topological-graph-theory/.../girth.v` (both registered in the package
`_CoqProject`), plus a new section at the end of
`spectral-graph-theory/theories/foundations/spectral.v`.

### Lemmas

| lemma | file | statement | retires |
| --- | --- | --- | --- |
| `k_uniform_equiv_hg_uniform` | `hypergraph-theory/theories/conjectures/vocabulary_hypergraph.v` | `k_uniform E k <-> hg_uniform E k` | U12's `k_uniform` |
| `x6_uniform_equiv_hg_uniform` | idem | `x6_uniform E r <-> hg_uniform E r` | X6's `x6_uniform` |
| `x104_uniform_equiv_hg_uniform` | idem | `x104_uniform E r <-> hg_uniform E r` | X104's copy |
| `x108_uniform_equiv_hg_uniform` | idem | `x108_uniform E r <-> hg_uniform E r` | X108's copy |
| `x119_uniform_equiv_hg_uniform` | idem | `x119_uniform E r <-> hg_uniform E r` | X119's copy |
| `x137_uniform_equiv_hg_uniform` | idem | `x137_uniform F r <-> hg_uniform F r` | X137's copy |
| `x209_uniform_equiv_hg_uniform` | idem | `x209_uniform E k <-> hg_uniform E k` | X209's copy (all seven "k-uniform" copies now bridged to `foundations/hypergraph.hg_uniform`) |
| `x72_vertex_cover_equiv_hg_cover` | idem | `x72_vertex_cover E X <-> hg_cover X E` | the `~~ [disjoint X & e]` vs `X :&: e != set0` split |
| `x72_transversal_number_equiv_is_cover_number` | idem | `x72_transversal_number E tau <-> is_cover_number E tau` | X72's cover-number wrapper |
| `x6_hg_degreeE`, `x73_hyperdegreeE`, `x73_hyperdegree_equiv_x6_hg_degree` | idem | `x6_hg_degree E v = hg_degree E v`, `x73_hyperdegree E v = hg_degree E v`, and the two local copies agree | the two hyperedge-degree copies |
| `x119_sqrtE` | idem | `x119_sqrt m = sqrt_ceil m` | X119's verbatim copy of `GTBase.asymptotics.sqrt_ceil` |
| `x117_image_edgeE`, `x119_image_edgeE` | idem | `x117_image_edge f e = x108_image_edge f e`, `x119_image_edge f e = x108_image_edge f e` | two of the three hyperedge-image copies |
| `x117_monochromatic_copyE`, `x117_forces_mono_equiv_x108` | idem | the X117 two-colour Ramsey-host notions are the X108 ones | the X117 copies |
| `x108_two_colour_ramsey_at_most_equiv_x119_forces_mono`, `x117_forces_mono_equiv_x119_forces_mono` | idem | `x108_two_colour_ramsey_at_most E N <-> x119_forces_mono E 2 N` (and the X117 form) | states the instance: the X119 q-colour machinery at `q = 2` IS the X108/X117 two-colour machinery |
| `bipartite_relE`, `bipartite_rel_equiv_bipartite` | `homomorphism-theory/theories/conjectures/implications_U3.v` | `bipartite_rel (G := G) (--) = bipartite G` (and `<->`) | U3's relation-level `bipartite_rel` at the adjacency instance |
| `same_deck_equiv_x21_same_l_deck` | `reconstruction-theory/theories/conjectures/implications_U11.v` | `0 < #\|G\| -> #\|H\| = #\|G\| -> (same_deck G H <-> x21_same_l_deck G H #\|G\|.-1)` | the duplication of the deck vocabulary between U11 and X21 (`vdel_card_setC1` and `pred_addn1` are its helpers) |
| `liso_equiv_sgraph_of` | `spectral-graph-theory/theories/foundations/spectral.v` | `liso r r' <-> inhabited (sgraph_of rG ≃ sgraph_of rG')` | the gap between the labelled isomorphism of the "almost all graphs" row and the `sgraph`-level `≃` used by `determined_by_spectrum`; `sgraph_of` / `sgraph_ofE` are new |
| `Delta_lt_of_cln_lt` | `extremal-graph-theory/theories/foundations/degree_bounds.v` | `0 < #\|G\| -> (forall v, d * #\|N[v]\| < p * #\|G\|) -> d * Delta G < p * #\|G\|` | the closed-neighbourhood-to-`Delta` step that was inlined in the e076 edge proof |
| `x223_eps_bounded_implies_x58_epsilon_bounded` | `extremal-graph-theory/theories/conjectures/implications_X223.v` | `0 < #\|G\| -> x223_eps_bounded G p d -> x58_epsilon_bounded G p d` | the two spellings of eps-boundedness (X223 closed neighbourhood, X58 maximum degree); the e076 proof now calls it |
| `x118_edges_betweenE`, `x120_edges_betweenE` | idem | `x118_edges_between A B = x223_edges_between A B`, same for `x120_` | the three verbatim ordered-pair cross-edge counters |
| `x223_edges_between_card_cross` | idem | `[disjoint A & B] -> x223_edges_between A B = #\|[set e in E(G) \| (e :&: A != set0) && (e :&: B != set0)]\|` | the audit's disjoint-case identity `x223_edges_between A B = #\|E(A,B)\|`, with `E(A,B)` spelled with the library's `E(G)` |
| `x215_arrows_equiv_x195_arrows`, `x215_ramsey_number_equiv_x195_ramsey_number` | `extremal-graph-theory/theories/conjectures/implications_X215.v` | `x215_arrows N k <-> x195_arrows 'K_N 2 (fun _ : 'I_1 => 'K_k)` (and the Ramsey-number wrappers) | the X215 diagonal two-colour arrow as an instance of the X195 family arrow |
| `edge_setGE`, `x5_edge_setE`, `x15_edge_setE`, `x25_edge_setE`, `x47_edge_setE`, `xe1_edge_setE` | `packing-theory/theories/conjectures/vocabulary_packing.v` | `..._edge_set G = E(G)` | the six tracked `*_edge_set` copies of packing-theory (`X15alone.v`'s seventh is untracked by `_CoqProject` and deliberately not imported) |
| `hamiltonian_cycleGE` | idem | `hamiltonian_cycleG G c = hamiltonian_cycle G c` | U9's copy of `GTBase.common.hamiltonian_cycle` (itself `ucycleb (--) c && (size c == #\|G\|)`) |
| `x5_is_triangle_equiv_is_triangle`, `x5_tri_edgesE` | idem | the X5 and U9 triangle notions agree | the byte-identical `is_triangle` / `tri_edges` pairs |
| `x18_independent_set_equiv_xe1_stable_set` | idem | `x18_independent_set S <-> xe1_stable_set S` | the two names for one notion |
| `x26_ballE` | idem | `x26_ball r x = x111_ball r x` | the duplicated ball `Fixpoint` |
| `x15_matching_equiv_matching` | idem | `x15_matching M <-> matching M` | X15's edge-set matching vs `connectivity.matching` |
| `x18_perfect_matching_equiv_x25_perfect_matching` | idem | the two perfect-matching copies agree | X18 / X25 duplication |
| `girth_geq4_equiv_triangle_free` | `topological-graph-theory/theories/foundations/girth.v` | `girth_geq G 4 <-> triangle_free G` | the X138 note "triangle-freeness is written `girth_geq G 4` rather than base's `triangle_free`" (`triangle_ucycle` / `ucycle3_triangle` are its halves) |
| `x158_edge_setE` | `topological-graph-theory/theories/conjectures/vocabulary_topological.v` | `x158_edge_set G = E(G)` | X158's `*_edge_set` copy |
| `x14_edge_setE`, `x20_edge_setE`, `x37_edge_setE`, `x38_edge_setE`, `x77_edge_setE`, `x102_edge_setE` | `graph-theory-misc/theories/conjectures/vocabulary_misc.v` | `..._edge_set G = E(G)` | the six `*_edge_set` copies of graph-theory-misc, including `x102_edge_set` = "2-element cliques" |
| `x113_is_cycleE`, `x113_is_cycle_equiv_xe1_rel_cycle` | idem | `x113_is_cycle c = (ucycle (--) c /\ 2 < size c)`, and `x113_is_cycle c <-> xe1_rel_cycle (--) c` | the two `ucycle` wrappers the ledger calls "literally `ucycle r c /\ 2 < size c`" |
| `x14_matching_equiv_matching` | idem | `x14_matching M <-> matching M` | X14's pairwise-disjoint matching vs `connectivity.matching` |

### Findings: claimed duplications that are NOT plain equivalences

- **`same_deck G H <-> x21_same_l_deck G H #\|G\|.-1` needs two hypotheses.**  It
  is FALSE without `0 < #|G|`: at `ell = #|G|.-1 = 0` the index type
  `{S : {set K} | #|S| == 0}` is the singleton `{set0}` for EVERY `K`, so
  `x21_same_l_deck G H 0` holds for every `H` whatsoever while `same_deck G H`
  still forces a vertex bijection `G -> H`.  The same collapse occurs at
  `#|G| = 1`.  With `0 < #|G|` and `#|H| = #|G|` (the hypothesis
  `x21_l_reconstructible` already carries) the equivalence holds and is proved.
  For `2 <= #|G|` the cardinality hypothesis is in fact derivable — an
  `ell`-deck bijection forces `C(#|H|, #|G|-1) = #|G|`, hence `#|H| = #|G|` —
  but that counting argument is not formalised.
- **X223 vs X58 eps-boundedness is an IMPLICATION, not an equivalence.**  X223
  bounds every closed neighbourhood, X58 the maximum degree; since
  `Delta G < #|N[v]|` for a vertex `v` of maximum degree, only
  `x223_eps_bounded -> x58_epsilon_bounded` holds (and it needs `0 < #|G|`).
  The converse fails, so the ledger's "two spellings" are not interchangeable
  and the X223 row is the stronger hypothesis.
- **`x223_edges_between A B = #\|E(A,B)\|` needs `[disjoint A & B]`.**  Without
  disjointness an edge inside `A :&: B` is counted twice as an ordered pair (as
  `(a,b)` and as `(b,a)`) but once as a 2-set, so the two counts differ; the
  in-file comment of X223.v already says so and the lemma now carries the guard.
  Note also that coq-graph-theory / GTBase have NO `edges_between` notion: the
  canonical form of `|E(A,B)|` had to be spelled with the library's `E(G)` as
  `#|[set e in E(G) | (e :&: A != set0) && (e :&: B != set0)]|`.
- **`x23_genuine_path` (topological, X23.v) is a re-encoding, not a copy.**  It is
  a non-empty `seq` carrying `uniq` and `path (--)`, whereas coq-graph-theory's
  `upath` / `Path` are indexed by their two ENDPOINTS; there is no equality or
  `<->` at equal arguments, only a translation that has to name the endpoints.
  No lemma stated.  The same holds for the other `seq`-vs-`Path` entries of the
  per-package "path" groups (`x116_ST_path`, `x39_xy_path`, `x146_A_path`, …).
- **`D3D6_unblocked.v:181 proper_minor` is not a duplicate**: it wraps
  coq-graph-theory's `minor` with a strictness condition, so it is a new notion.
- **`x25_perfect_matching` vs `GTBase.common.perfect_matching` was not bridged.**
  The local copies are "every vertex lies in exactly one member"; base's is
  `matching M /\ cover M = [set: G]`.  The equivalence is true but needs the
  `cover`/`bigcup` layer; the two LOCAL copies are bridged to each other and to
  `connectivity.matching` instead, which is what the rows use.  Left as a
  follow-up.
- **`U9.v:187 is_matching_edges` and `n_edges` were not bridged.**
  `is_matching_edges` is `x15_matching` with the "member is an edge" clause
  spelled existentially rather than by `\subset`; `U13.v:46 n_edges` is
  `#|oedges G|`, already tied to `#|E(G)|` by
  `grounding_U13.oedges_card_edges`, so no new lemma adds information.  Both
  left as follow-ups.
- **The three `r_partite_uniform` / matching / matching-number bridges were
  already proved** by wave E8b in
  `hypergraph-theory/theories/conjectures/implications_U12.v`
  (`x6_r_partite_uniform_equiv_r_partite_uniform`,
  `x6_matching_equiv_hg_matching`,
  `x6_matching_number_equiv_is_matching_number`) and are NOT duplicated here.

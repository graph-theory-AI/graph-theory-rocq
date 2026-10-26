(** * Chromatic.conjectures.X236 -- wave X236: six colouring rows (2026-10-26)

    A six-row wave under the prospective contract of meta/faithfulness_policy.json (hard lint,
    classified local helpers, grounding certificates, an independent verifier).  Rows:
    arxiv:1810.00065#00 (ternary graphs), arxiv:2511.02892#02 (cycles plus K_4's),
    arxiv:1808.01605#00 (fractional chromatic number and girth), arxiv:1804.06104#00 (neighbour sum
    distinguishing edge colourings), arxiv:2310.04265#06 (ordered matchings) and
    arxiv:2506.10227#00 (suns).  Shared vocabulary is reused: [has_ordinal_induced_cycle] and
    [ord_cycle_rel] (GTBase.induced_cycles), [bfold_colouring] (GTBase.bfold_colourings),
    [chi_bounded_via] and [chi_bounded_class] (GTBase.chi_bounding), [induced_free] and
    [has_subgraph] (GTBase.common), [fg_mk_sgraph] and [fg_srel] (GTBase.finite_graph), [girth_geq],
    [Delta] and the library chromatic and clique numbers, and Chromatic X142's neighbour sum
    distinguishing vocabulary.  The grounding certificates are in grounding_X236.v. *)

From GTBase Require Export base.
From GTBase Require Import common induced_cycles chi_bounding bfold_colourings finite_graph.
From Chromatic.conjectures Require Import X142.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x236 vocabulary ************************************************* *)

(** Ternary: no induced cycle has length a multiple of three (arXiv:1810.00065 l.83).  Lengths start
    at 3, since [has_ordinal_induced_cycle G 0] always holds and 3 divides 0. *)
Definition x236_ternary (G : sgraph) : Prop :=
  forall k : nat, 3 <= k -> 3 %| k -> ~ has_ordinal_induced_cycle G k.

(** A vertex-disjoint union of cycles, possibly missing some vertices: every degree is 0 or 2
    (arXiv:2511.02892, Problem 3.1). *)
Definition x236_cycle_union (G : sgraph) : Prop :=
  forall v : G, #|N(v)| = 0 \/ #|N(v)| = 2.

(** The parts of [p] all have four vertices: [p] partitions the vertices into the K_4's of H. *)
Definition x236_k4_parts (G : sgraph) (n : nat) (p : G -> 'I_n) : Prop :=
  forall i : 'I_n, #|[set v | p v == i]| = 4.

(** G union H, H being the disjoint union of the cliques on the parts of [p]. *)
Definition x236_union_k4 (G : sgraph) (n : nat) (p : G -> 'I_n) : sgraph :=
  fg_mk_sgraph (fun x y : G => (x -- y) || (p x == p y)).

(** chi_f(G) >= k: every a:b-colouring with b >= 1 uses at least k b colours
    (arXiv:1808.01605 l.78, the LP optimum being attained by a b-fold colouring). *)
Definition x236_frac_chi_at_least (G : sgraph) (k : nat) : Prop :=
  forall (a b : nat) (f : G -> {set 'I_a}), 0 < b -> bfold_colouring b f -> k * b <= a.

(** No isolated edge: no K_2 component, i.e. every edge has an end of degree at least 2
    (arXiv:1804.06104 l.189). *)
Definition x236_no_isolated_edge (G : sgraph) : Prop :=
  forall x y : G, x -- y -> 1 < #|N(x)| \/ 1 < #|N(y)|.

(** (M, <) is an induced ordered subgraph of (E, <), both ordered graphs on ordinals with the order
    of the ordinals (arXiv:2310.04265 l.1184): an increasing map preserving adjacency both ways. *)
Definition x236_ord_contains (m n : nat) (M : rel 'I_m) (E : rel 'I_n) : Prop :=
  exists phi : 'I_m -> 'I_n,
    (forall i j : 'I_m, (i < j)%N -> (phi i < phi j)%N) /\
    forall i j : 'I_m, fg_srel M i j = fg_srel E (phi i) (phi j).

(** The ordered graph [M] has maximum degree at most 1. *)
Definition x236_max_degree_one (m : nat) (M : rel 'I_m) : Prop :=
  forall i : 'I_m, #|[set j | fg_srel M i j]| <= 1.

(** The t-sun: (i, false) are the vertices of a t-cycle and (i, true) is a pendant vertex at
    (i, false) (arXiv:2506.10227 l.100). *)
Definition x236_sun (t : nat) : sgraph :=
  fg_mk_sgraph (fun x y : 'I_t * bool =>
    if x.2 || y.2 then (x.1 == y.1) && (x.2 != y.2) else ord_cycle_rel t x.1 y.1).

(** ** X236 statements ******************************************************* *)

(** Corpus row: arxiv:1810.00065#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1810.00065__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1810.00065__00.json
    English statement: (arXiv:1810.00065, Chudnovsky, Scott, Seymour and Spirkl, "Proof of the
      Kalai-Meshulam conjecture", the open problem of the introduction)
      Every ternary graph is 3-colourable, a graph being ternary if no induced cycle has length a
      multiple of three.
    Definitions: [x236_ternary G] - G has no induced cycle of length k for any k >= 3 divisible by 3
      (this file); [has_ordinal_induced_cycle G k] - an injective map from 'I_k whose adjacency is
      exactly the k-cycle relation (GTBase.induced_cycles); chi is the library chromatic number.
    Notes: the source is the e-print main.tex of 1810.00065v1: ternary graphs l.83-84 (so they have
      no triangles), the open problem l.95-96 ("it may be that all ternary graphs are 3-colourable,
      and this remains open"), finite simple graphs l.82.  The affirmative form is stated.  Lengths
      start at 3 because the induced-cycle predicate holds trivially at length 0.  Literature status:
      open at the paper and the pinned review.  The paper also records (l.110-113) that Kral's
      question whether some edge of every ternary graph can be deleted keeping it ternary, which
      would have implied the row, was disproved by Wrochna. *)
Definition ternary_three_colourable_statement : Prop :=
  forall G : sgraph, x236_ternary G -> χ([set: G]) <= 3.

(** Corpus row: arxiv:2511.02892#02
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2511.02892__02/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2511.02892__02.json
    English statement: (arXiv:2511.02892, open problems of the 33rd Workshop on Cycles and
      Colourings, Problem 3.1, Haxell)
      If G is a disjoint union of cycles and H is a disjoint union of K_4's on the same vertex set,
      then G union H is 4-colourable.
    Definitions: [x236_cycle_union G] - every vertex of G has degree 0 or 2; [x236_k4_parts p] -
      every part of p : V -> 'I_n has four vertices; [x236_union_k4 p] - the graph on V adjacent in
      G or in the same part (this file); chi is the library chromatic number.
    Notes: the source is PROBLEMS25/Haxell.tex of 2511.02892v1: the problem l.13-15, the K_5 and K_3
      analogues l.21, the strong-colouring frame l.23 (G of maximum degree d, H a union of K_{2d}'s
      on the same vertex set), which fixes one vertex set partitioned by H.  The affirmative form is
      stated.  A graph whose degrees are all 0 or 2 is a vertex-disjoint union of cycles plus
      isolated vertices; this reading is equivalent to the spanning one: put each isolated vertex v
      on a new triangle v x_v y_v, pad the new vertices with a new cycle to a multiple of 4, cover
      them by new K_4's, and restrict a 4-colouring of the enlarged graph to the old vertices.
      Literature status: open at the paper and the pinned review. *)
Definition cycles_plus_k4s_four_colourable_statement : Prop :=
  forall (G : sgraph) (n : nat) (p : G -> 'I_n),
    x236_cycle_union G -> x236_k4_parts p -> χ([set: x236_union_k4 p]) <= 4.

(** Corpus row: arxiv:1808.01605#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1808.01605__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1808.01605__00.json
    English statement: (arXiv:1808.01605, "Triangle-free subgraphs with large fractional chromatic
      number", Conjecture 4)
      For every real x >= 1 and every integer g >= 3 there is a positive k(x, g) such that every
      graph G with chi_f(G) >= k(x, g) contains a subgraph H of girth at least g with
      chi_f(H) >= x.
    Definitions: [x236_frac_chi_at_least G k] - every a:b-colouring of G with b >= 1 has a >= k b,
      i.e. chi_f(G) >= k (this file); [bfold_colouring b f] - f gives every vertex b colours of
      'I_a, disjoint on adjacent vertices (GTBase.bfold_colourings); [has_subgraph G H] - G contains
      a not necessarily induced copy of H (GTBase.common); [girth_geq H g] - every cycle of H has
      length at least g (GTBase).
    Notes: the source is the e-print main.tex of 1808.01605v1: chi_f as the LP minimum over
      independent sets l.78, the conjecture l.91-94 (conj:1, Conjecture 4 with the theorem counter:
      l.66 Conjecture 1, l.73 Theorem 2, l.84 Theorem 3, the case g = 4).  chi_f(G) is the minimum
      over b >= 1 of chi_b(G) / b, attained by a b-fold colouring, since the LP of l.78 has a
      rational optimum; so chi_f(G) >= k iff every a:b-colouring with b >= 1 has a >= k b; b = 0 is
      excluded (the empty colouring is a 0-fold colouring of every graph).  Real x and k reduce to
      naturals: the statement at the ceiling of x implies it at x, and a natural k at least k(x, g)
      only strengthens the hypothesis.  The helper is local because Chromatic X130's
      [x130_frac_chi_le] is the other direction and the canonical fractional chromatic number
      (Extremal.foundations.fractional_colouring) builds after chromatic-theory.  The sibling row
      1808.01605#01 is X31's chromatic-girth average-degree row.  Literature status: open at the
      paper (which proves g = 4) and the pinned review. *)
Definition fractional_girth_subgraph_statement : Prop :=
  forall x g : nat, 1 <= x -> 3 <= g ->
    exists k : nat, 0 < k /\
      forall G : sgraph, x236_frac_chi_at_least G k ->
        exists H : sgraph, [/\ has_subgraph G H, girth_geq H g & x236_frac_chi_at_least H x].

(** Corpus row: arxiv:1804.06104#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1804.06104__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1804.06104__00.json
    English statement: (arXiv:1804.06104, Joret and Lochet, "Progress on the adjacent vertex
      distinguishing edge colouring conjecture", the open problem after Flandrin et al.'s
      conjecture)
      There is a constant C such that every graph with no isolated edge has a neighbour sum
      distinguishing edge colouring with at most Delta(G) + C colours.
    Definitions: [x236_no_isolated_edge G] - every edge has an end of degree at least 2 (this
      file); [x142_neighbour_sum_edge_colourable G k] - a proper edge colouring with colours 'I_k
      (read as 1, ..., k) in which adjacent vertices have different sums of incident colours
      (Chromatic.conjectures.X142); [Delta G] - the maximum degree (GTBase).
    Notes: the source is the e-print AVD.tex of 1804.06104v2: colourings and properness l.145-148,
      neighbour sum distinguishing colourings and Flandrin et al.'s conjecture l.189-190, the best
      bound Delta + O(Delta^(1/2)) l.191, the open problem l.192 ("whether a Delta + O(1) bound
      holds").  An isolated edge is a K_2 component (both ends of degree 1), where no such colouring
      exists.  Delta + O(1) is one constant C for every graph; Flandrin et al.'s Delta >= 3 is
      absorbed by C, paths and cycles needing boundedly many colours.  X142 counts colour c of 'I_k
      as c + 1, so its colours are 1, ..., k as in the source.  Relation (edge candidate): X142's
      Flandrin row (Delta + 2 for connected graphs other than C_5 with at least 3 vertices) implies
      this row with C = 3, componentwise.  Literature status: open at the paper and the pinned
      review. *)
Definition nsd_delta_plus_constant_statement : Prop :=
  exists C : nat, forall G : sgraph, x236_no_isolated_edge G ->
    x142_neighbour_sum_edge_colourable G (Delta G + C).

(** Corpus row: arxiv:2310.04265#06
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2310.04265__06/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2310.04265__06.json
    English statement: (arXiv:2310.04265, "Clique number of tournaments", Conjecture 4.11)
      For every ordered graph (M, <) of maximum degree at most 1, the class of ordered graphs with
      no induced ordered copy of (M, <) is chi-bounded.
    Definitions: [x236_ord_contains M E] - an increasing map from 'I_m to 'I_n preserving adjacency
      both ways; [x236_max_degree_one M] - every vertex of M has at most one neighbour (this file);
      [chi_bounded_via U F] - one f with chi(U x) <= f(omega(U x)) for every x in F
      (GTBase.chi_bounding); [fg_mk_sgraph] and [fg_srel] (GTBase.finite_graph).
    Notes: the source is the e-print main.tex of 2310.04265v1 (the pinned version): ordered graphs
      l.1180, induced ordered subgraphs l.1184, Forb and chi-boundedness of a class of ordered
      graphs as that of the underlying graphs l.1186, the conjecture l.1263-1265 (conj:bartosz).
      Ordered graphs are taken on 'I_n with the order of 'I_n (every finite ordered graph is
      isomorphic to one, and containment, chi and omega are invariant); fg_srel symmetrizes and
      drops loops on both sides.  Literature status: open at the pinned review; the paper reports
      (l.1262) that Brianski, Davies and Walczak claimed a proof in a personal communication.
      Grounding: dropping "maximum degree 1" would need ordered triangle-free graphs of large chi,
      so not_trivially_true uses a false strengthened conclusion (chi <= omega, refuted by C_5),
      which implies the row: a deviation from the contract form, recorded here for the A3
      verifier (Lancelot's routing (22) b; Marcol's design read (70) d). *)
Definition ordered_matching_free_chi_bounded_statement : Prop :=
  forall (m : nat) (M : rel 'I_m), x236_max_degree_one M ->
    chi_bounded_via (fun x : {n : nat & rel 'I_n} => fg_mk_sgraph (projT2 x))
                    (fun x => ~ x236_ord_contains M (projT2 x)).

(** Corpus row: arxiv:2506.10227#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2506.10227__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2506.10227__00.json
    English statement: (arXiv:2506.10227, "Suns in triangle-free graphs of large chromatic number",
      the remark after Problem 1.4)
      The class of sun-free graphs is chi-bounded, a t-sun (t >= 4) being a t-cycle with a pendant
      vertex at each cycle vertex, and a graph sun-free if it has no induced t-sun for any t >= 4.
    Definitions: [x236_sun t] - the t-sun on 'I_t * bool (this file); [induced_free G H] - no
      induced subgraph of G is isomorphic to H (GTBase.common); [chi_bounded_class F] - one f with
      chi(G) <= f(omega(G)) for every G in F (GTBase.chi_bounding); [ord_cycle_rel t] - the t-cycle
      relation (GTBase.induced_cycles).
    Notes: the source is the e-print main.tex of 2506.10227v2: t-suns, t-sun-free and sun-free
      l.100 (t >= 4), chi-bounded and the net l.131, Problem 1.4 (net-free sun-free graphs)
      l.134-135, and the remark l.138 that the class of all sun-free graphs may already be
      chi-bounded, which is the row: nets (3-suns) are allowed.  Literature status: open at the
      paper and the pinned review. *)
Definition sun_free_chi_bounded_statement : Prop :=
  chi_bounded_class (fun G : sgraph => forall t : nat, 4 <= t -> induced_free G (x236_sun t)).

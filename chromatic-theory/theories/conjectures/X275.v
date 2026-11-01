(** * Chromatic.conjectures.X275 -- wave X275: the mod k chromatic index of 0_k-graphs, and the edge density of
    4-critical planar graphs (2026-11-01)

    A two-row wave under the prospective contract of meta/faithfulness_policy.json.  Rows: arxiv:2507.04254#00
    (Conjecture 13 of "On Modular Edge Colourings of Graphs": every 0_k-graph has chi'_k(G) <= k + o(k)) and
    studies:std_yao_zhou_conjecture_on_the_edge_density_of_4_cri (the limsup of |E(G)| / |V(G)| over the 4-critical
    planar graphs G is 7/3).
    Shared vocabulary: GTBase's [wagner_planar] (base.v) and [E(G)] (coq-graph-theory's [sg_edge_set]); Chromatic
    X100's [x100_modular_edge_colourable] and X258's [x258_edge_critical], used unchanged; coq-graph-theory's
    chromatic number.  No local helper.
    Pinned statuses: both open; literature lines are dated against the corpus pin (graph-conjectures b72c5857,
    2026-09-23).  The sources are the Mac's deposit coordination/sources/x275-source-mac-20261101 (2507.04254v2,
    2311.03132v1, 1509.00760v1; TeX line numbers below).  The grounding certificates are in grounding_X275.v. *)

From GTBase Require Import base common colourings.
From Chromatic.conjectures Require Import X100 X258.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X275 statements ********************************************************* *)

(** Corpus row: arxiv:2507.04254#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2507.04254__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2507.04254__00.json
    English statement: (Berthe, Bonamy, Botler, Carenini, Colucci et al., Conjecture 13)
      Let k be a positive integer.  For every 0_k-graph G we have chi'_k(G) <= k + o(k).
    Definitions: (forall v : G, k %| #|N(v)|) - G is a 0_k-graph: every vertex has degree 0 modulo k, degree 0
      included (inlined); [x100_modular_edge_colourable G k q] - a colouring of the edges of G with the q colours
      of 'I_q in which every colour class has all its non-zero degrees congruent to 1 modulo k (Chromatic X100,
      the X100 row's chi'_k); chi'_k(G), the mod k chromatic index, is the least such q.
    Notes: encoded as stated, with the o(k) term uniform over the 0_k-graphs; pinned status open.  The statement is
      Conjecture 13 of arXiv:2507.04254v2 (5 December 2025, main.tex l.394-397), with the paper's definitions: a
      chi'_k-colouring has every colour class with all its degrees 1 modulo k (l.69; its abstract, l.47, says
      non-zero degrees, as X100 reads it), chi'_k(G) the least number of colours (l.70), an l_k-graph has every
      degree l modulo k (l.280-282), and all graphs are simple (l.69).  "chi'_k(G) <= k + o(k)" is read as one
      function: for every epsilon > 0 there is k0 such that chi'_k(G) <= (1 + epsilon) k for every k >= k0 and
      every 0_k-graph G; epsilon = 1 / m loses nothing (a smaller epsilon is a stronger bound), and m q <= (m + 1) k
      is q <= (1 + 1 / m) k.  "Some q at most the bound" is chi'_k(G) <= the bound, since an unused colour keeps a
      colouring.  The paper's k >= 2 default (l.69) and its "positive integer" both fit: the k0 of the body may be
      taken >= 2, and k = 1 is degenerate (every colour-degree is 0 modulo 1, so only edgeless graphs have a
      colouring).  A colouring needs at least one colour here ({set G} -> 'I_0 is empty while {set G} is not), an
      implementation reading: an edgeless graph has chi'_k = 0 in the paper and q = 1 here, below every bound
      (1 + 1 / m) k with k >= 1.  The paper's main theorem (l.93-97) is chi'_k(G) <= 9k + f(k) for one f in o(k),
      every k and every graph: the same uniform reading of o(k), and a bound for all graphs, not this conjecture.
      As chi'_k is bounded over all graphs for each k (that theorem), f(k) := the largest chi'_k(G) - k over the
      0_k-graphs G is defined, and the body says f(k) <= k / m for every k >= k0(m): f is in o(k), and conversely. *)
Definition modular_edge_colouring_zero_mod_k_graphs_k_plus_little_o_statement : Prop :=
  forall m : nat, 0 < m ->
    exists k0 : nat, forall k : nat, k0 <= k ->
      forall G : sgraph, (forall v : G, k %| #|N(v)|) ->
        exists q : nat, m * q <= (m + 1) * k /\ x100_modular_edge_colourable G k q.

(** Corpus row: studies:std_yao_zhou_conjecture_on_the_edge_density_of_4_cri
    Site: none
    Review: none
    English statement: (Yao and Zhou; studies slice of the corpus, record arXiv:2311.03132)
      L := limsup over the 4-critical planar graphs G of |E(G)| / |V(G)| = 7/3.
    Definitions: [wagner_planar G] - G has neither K_5 nor K_(3,3) as a minor (GTBase base.v); [χ([set: G]) = 4 /\
      x258_edge_critical G 4] - G is 4-critical: chromatic number 4, and deleting any edge lowers it (Chromatic
      X258); [#|E(G)|] - the number of edges (coq-graph-theory's [sg_edge_set]); [#|G|] - the number of vertices.
    Notes: encoded as stated; pinned status open, but FALSE at the pin.  L is defined by Grunbaum as the limsup of
      |E(G)| / |V(G)| over all 4-critical planar graphs G (arXiv:2311.03132v1, 6 November 2023, main.tex l.92-94),
      with G k-critical when chi(G - e) < chi(G) = k for every edge e (l.74): X258's edge criticality with chi = 4,
      isolated vertices not excluded (they only lower the density).  Yao and Zhou proved L >= 7/3 and conjectured
      equality (l.94; their arXiv:1509.00760v1 states it for the supremum S, l.277, with a finite-order bound not
      encoded here).  The limsup over the graphs ordered by order is lim over N of the sup over #|G| >= N, so
      L = 7/3 is, for every epsilon = p / q > 0: eventually 3 q |E| <= (7 q + 3 p) |V| (L <= 7/3), and members of
      every large order bound with 7 q |V| <= 3 q |E| + 3 p |V| (L >= 7/3), the subtraction moved to the right.  A
      lower clause asks for orders >= N only: 2311.03132's graphs P_m have at most m vertices (l.102-104).  FALSE at
      the pin: Theorem 1 there (l.98-100) gives L = 2.5 and "refutes the aforementioned conjecture of Yao and Zhou"
      (l.106-107), so the upper clause fails; L >= 7/3 is Yao and Zhou's theorem.  The status correction is a
      separate corpus item. *)
Definition yao_zhou_four_critical_planar_edge_density_limsup_seven_thirds_statement : Prop :=
  forall p q : nat, 0 < p -> 0 < q ->
    (exists n0 : nat, forall G : sgraph, n0 <= #|G| -> wagner_planar G -> χ([set: G]) = 4 ->
       x258_edge_critical G 4 ->
       3 * q * #|E(G)| <= (7 * q + 3 * p) * #|G|) /\
    (forall n0 : nat, exists G : sgraph,
       [/\ n0 <= #|G|, wagner_planar G, χ([set: G]) = 4, x258_edge_critical G 4 &
           7 * q * #|G| <= 3 * q * #|E(G)| + 3 * p * #|G|]).

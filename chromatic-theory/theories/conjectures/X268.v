(** * Chromatic.conjectures.X268 -- wave X268: the Alon-Tarsi number after removing a matching, self-isolating
    graphs, and the Plummer-Zha conjecture (2026-10-31)

    A three-row wave under the prospective contract of meta/faithfulness_policy.json.  Rows: arxiv:2209.09107#01
    (Question 6.2: a constant C such that every graph G of maximum degree Delta has a matching M with
    AT(G - M) <= Delta / 2 + C), arxiv:2202.09118#04 (the question whether all graphs are self-isolating) and
    studies:std_plummer_zha_conjecture (every 3-connected, internally 4-connected pentagraph is three-colourable).
    Shared vocabulary: Chromatic.foundations.alon_tarsi ([at_alon_tarsi], [at_outdegree]), GTBase's [Delta],
    [del_edge_set] and [induced_free] (base.v, common.v), [anticomplete] (set_pairs.v), [girth_geq] and
    [k_connected] (base.v) and [chordless_cycle] (induced_cycles.v), and coq-graph-theory's [matching], chromatic
    number, clique number, induced subgraphs and neighbourhoods.
    Local helpers: AT(G) <= k ([x268_at_le]), self-isolation ([x268_self_isolating]), internal 4-connectivity
    ([x268_internally_four_connected]) and pentagraphs ([x268_pentagraph]).
    Pinned statuses: all three open; literature lines are dated against the corpus pin (graph-conjectures
    b72c5857, 2026-09-23).  The sources are the Mac's deposit coordination/sources/x268-source-mac-20261030 (TeX
    line numbers below).  The grounding certificates are in grounding_X268.v. *)

From GTBase Require Import base common set_pairs induced_cycles.
From Chromatic.foundations Require Import alon_tarsi.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X268 vocabulary ********************************************************* *)

(** AT(G) <= k (Bradshaw, Chen, Ma, Mohar and Wu, arXiv:2209.09107v2, main.tex l.215-222): G has an orientation A,
    every arc an edge of G and every edge of G exactly one arc, whose even and odd Eulerian sub-digraph counts
    differ (an Alon-Tarsi orientation, [at_alon_tarsi] of Chromatic.foundations.alon_tarsi), and whose every
    outdegree is less than k.  AT(G) is the least such k, so for a natural k this is AT(G) <= k. *)
Definition x268_at_le (G : sgraph) (k : nat) : Prop :=
  exists A : {set G * G},
    [/\ forall x y : G, (x, y) \in A -> x -- y,
        forall x y : G, x -- y -> ((x, y) \in A) (+) ((y, x) \in A),
        at_alon_tarsi A &
        forall v : G, (at_outdegree A v).+1 <= k].

(** H is self-isolating (Chudnovsky, Scott, Seymour and Spirkl, arXiv:2202.09118v1, source.tex l.141-150), with
    the polynomials psi and phi as monomials c x^d and c' x^d' (the Notes of the second statement give the
    reduction): every G with chi(G) > c' omega(G)^d' has a vertex set A with chi(A) > c omega(A)^d such that G[A]
    is H-free or G has an induced copy of H on a set S disjoint from and anticomplete to A. *)
Definition x268_self_isolating (H : sgraph) : Prop :=
  forall c d : nat, exists c' d' : nat,
    forall G : sgraph, c' * ω([set: G]) ^ d' < χ([set: G]) ->
      exists A : {set G}, c * ω(A) ^ d < χ(A) /\
        (induced_free (induced A) H \/ exists S : {set G}, inhabited (induced S ≃ H) /\ anticomplete S A).

(** Internal 4-connectivity (Plummer and Zha, Electron. J. Combin. 21(1) (2014) #P1.34, p.1): every set of three
    vertices whose deletion disconnects G is the neighbourhood of a fourth vertex.  Plummer and Zha define it for
    3-connected graphs; the statement asks for [k_connected G 3] separately. *)
Definition x268_internally_four_connected (G : sgraph) : Prop :=
  forall S : {set G}, #|S| = 3 -> ~ connected ([set: G] :\: S) -> exists v : G, N(v) = S.

(** A pentagraph (Chudnovsky and Seymour, arXiv:2201.11505v2, source.tex l.69-70): every cycle has length at least
    five, and every induced cycle of odd length has length five. *)
Definition x268_pentagraph (G : sgraph) : Prop :=
  girth_geq G 5 /\ forall c : seq G, chordless_cycle c -> odd (size c) -> size c = 5.

(** ** X268 statements ********************************************************* *)

(** Corpus row: arxiv:2209.09107#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2209.09107__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2209.09107__01.json
    English statement: (Bradshaw, Chen, Ma, Mohar and Wu, List-avoiding orientations, arXiv:2209.09107, Question
      6.2)
      Does there exist a constant C such that every graph G of maximum degree Delta has a matching M such that
      AT(G - M) <= Delta / 2 + C?
    Definitions: [x268_at_le G k] - AT(G) <= k: an orientation of G with every edge oriented exactly once, whose
      even and odd Eulerian sub-digraph counts differ, and whose outdegrees are less than k (this file);
      [matching M] - a set of pairwise disjoint edges of G (coq-graph-theory; it includes M \subset E(G));
      [del_edge_set G M] - G with the edges of M removed, vertices kept (GTBase common.v); [Delta G] - the maximum
      degree of G (GTBase base.v).
    Notes: encoded as its affirmative answer; pinned status open.  The question is at l.1015-1018 of the source
      (arXiv:2209.09107v2, main.tex; PDF p.14), the Alon-Tarsi number at l.215-222 (PDF p.3): the least k such that
      G has an Alon-Tarsi orientation of maximum outdegree less than k.  Delta is the maximum degree of G, and
      G - M deletes the edges of M.  AT(G - M) is an integer, so AT(G - M) <= Delta / 2 + C iff 2 AT(G - M) <=
      Delta + 2 C; with k = AT(G - M) that is the conjunct 2 k <= Delta G + 2 C.  A real constant C may be
      replaced by any larger natural one, so C ranges over nat.  The paper remarks C >= 1/2 (l.1020, after Huang,
      Wong and Zhu).  Our own inference: an edgeless graph with a vertex has Delta = 0 and AT = 1 (an outdegree 0
      needs k >= 1), so C >= 1.  [x268_at_le] orients every edge of G exactly once; the spanning-subgraph
      orientation of Question 6.1 (the sibling row #00, in applications/alon_tarsi_triangle.v) may leave edges
      unused and is a different notion. *)
Definition alon_tarsi_matching_removal_statement : Prop :=
  exists C : nat, forall G : sgraph, exists M : {set {set G}},
    matching M /\ exists k : nat, 2 * k <= Delta G + 2 * C /\ x268_at_le (del_edge_set G M) k.

(** Corpus row: arxiv:2202.09118#04
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2202.09118__04/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2202.09118__04.json
    English statement: (Chudnovsky, Scott, Seymour and Spirkl, Polynomial bounds for chromatic number VII.
      Disjoint holes, arXiv:2202.09118, Question)
      Could it be that all graphs are self-isolating?
    Definitions: [x268_self_isolating H] - for all c, d some c', d' such that every G with chi(G) > c' omega(G)^d'
      has a vertex set A with chi(A) > c omega(A)^d and G[A] H-free or an induced copy of H disjoint from and
      anticomplete to A (this file); [induced_free G H] - no induced subgraph of G is isomorphic to H (GTBase
      common.v); [anticomplete S A] - S and A are disjoint with no edge between them (GTBase set_pairs.v);
      [χ(A)], [ω(A)] - the chromatic and clique numbers of G[A] (coq-graph-theory).
    Notes: encoded as its affirmative answer; pinned status open.  The question is in the paragraph after the
      definition (arXiv:2202.09118v1, 18 February 2022, the only version; source.tex l.141-150 the definition,
      l.165 the question).  The definition quantifies over every non-decreasing polynomial psi : N -> N and asks
      for some polynomial phi : N -> N.  Monomials suffice both ways.  Every polynomial psi is at most some c x^d
      for x >= 1, and c x^d is itself a non-decreasing polynomial, so "for every psi" may be read on monomials: a
      larger psi gives a stronger conclusion.  A monomial is a polynomial, and every polynomial phi is at most some
      c' x^d' for x >= 1, so "some phi" may be read on monomials: a larger phi gives a weaker hypothesis.  Only
      x >= 1 matters: c omega(A)^d < chi(A) forces A nonempty, so omega(A) >= 1, and likewise for G.  A copy of H
      in G is an induced subgraph isomorphic to H (l.138-140).  The authors remark (l.165-167) that with general
      functions in place of the polynomials every graph is self-isolating, by induction on omega(G): the
      polynomial bounds carry the question. *)
Definition all_graphs_self_isolating_statement : Prop :=
  forall H : sgraph, x268_self_isolating H.

(** Corpus row: studies:std_plummer_zha_conjecture
    Site: none
    Review: none
    English statement: (Plummer and Zha, the Plummer-Zha conjecture, studies slice of the corpus)
      Every 3-connected, internally 4-connected pentagraph is three-colourable.
    Definitions: [k_connected G 3] - more than three vertices, and deleting fewer than three leaves G connected
      (GTBase base.v); [x268_internally_four_connected G] - every three vertices whose deletion disconnects G
      are the neighbourhood of a fourth vertex (this file); [x268_pentagraph G] - girth at least five, and every
      induced (chordless) cycle of odd length has length five (this file).
    Notes: encoded as stated; pinned status open, but TRUE at the pin.  Plummer and Zha (Electron. J. Combin.
      21(1) (2014) #P1.34) define internal 4-connectivity on p.1 and conjecture, in Question 3.4 (p.9), that the
      graphs of their class (3-connected, internally 4-connected, girth five, every odd cycle longer than five with
      a chord) have chromatic number 3; their class is the 3-connected, internally 4-connected pentagraphs with a
      5-cycle.  A pentagraph with no 5-cycle is bipartite (a shortest odd cycle is induced), so the row and
      Question 3.4 differ only by bipartite graphs, and chi = 3 is chi <= 3 on graphs with a 5-cycle.  Chudnovsky
      and Seymour, Proof of a conjecture of Plummer and Zha (arXiv:2201.11505v2, 31 January 2022, source.tex
      l.69-82), Theorem 1.1: every pentagraph is three-colourable, which covers this row.  The status correction is
      a separate corpus item.  The pentagraph cycles are genuine cycles: [girth_geq] reads ucycles of at least three
      vertices, and [chordless_cycle] is a chordless ucycle of at least three vertices. *)
Definition plummer_zha_pentagraph_three_colourable_statement : Prop :=
  forall G : sgraph, k_connected G 3 -> x268_internally_four_connected G -> x268_pentagraph G ->
    χ([set: G]) <= 3.

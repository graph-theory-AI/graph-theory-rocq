(** * GTMisc.conjectures.X312 -- v2 rows: domination against packing in subcubic graphs (Henning, Loewenstein and
      Rautenbach), bounded treewidth of even-hole-free graphs with no diamond and no K_t (Sintiari and Trotignon), and
      two disjoint avoidable paths (Bonamy, Defrain, Hatzel and Thiebaut) *)

From GTBase Require Export base.
From GTBase Require Import induced_paths induced_cycles.
From Minor.conjectures Require Import X42.
From Minor.foundations Require Import width_params.
From GTMisc.conjectures Require Import X91.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X312 helper ************************************************************ *)

(** [x312_packing P]: distinct members of P have disjoint closed neighbourhoods N[u] (coq-graph-theory's closed
    neighbourhood, u and its neighbours), the packing of arXiv:2503.05562v1 (l.24-26, l.58: "a collection of vertices
    whose closed neighborhoods are pairwise disjoint"). *)
Definition x312_packing (G : sgraph) (P : {set G}) : Prop :=
  forall u v : G, u \in P -> v \in P -> u != v -> [disjoint N[u] & N[v]].

(** ** X312 statements ******************************************************** *)

(** Corpus row: studies:std_henning_l_wenstein_rautenbach_conjecture
    Site: none
    Review: none
    English statement: (Henning, Loewenstein and Rautenbach's conjecture [HLR11]; studies slice of the corpus, record
      arXiv:2503.05562, Conjecture 1.2) Let G be a connected graph with maximum degree at most 3; then
      gamma(G) <= 2 rho(G) + 1, where gamma is the domination number and rho the packing number. [The pinned text's
      second sentence, on the cases of equality, is not encoded: see the Notes.]
    Definitions: [connected [set: G]] - G is connected (coq-graph-theory); [subcubic G] - every vertex has at most
      three neighbours, that is maximum degree at most 3 (GTBase base.v); [dominating D] - every vertex is in D or
      adjacent to a member of D (coq-graph-theory dom.v, re-exported by GTBase); [x312_packing P] - distinct members
      of P have disjoint closed neighbourhoods (this file); [N[u]] - the closed neighbourhood of u (coq-graph-theory).
    Notes: PARTIAL. gamma(G) <= 2 rho(G) + 1 is stated as "some dominating set D and some packing P satisfy
      #|D| <= 2 #|P| + 1": gamma(G) <= #|D| for every dominating D and #|P| <= rho(G) for every packing P, and a
      minimum dominating set with a maximum packing gives the converse, so the two are equivalent. The pinned second
      sentence ("The equality holds only for three well-defined graphs, one of which being the Petersen graph") is not
      encoded: the three graphs are named only in [HLR11], not in the record, and the record refutes the clause
      (Theorem 1.12, l.243-246, proved in Section 8.1, l.951-961: an infinite family of graphs with maximum degree at
      most 3 and gamma(G) = 2 rho(G) + 1, connected by their ring construction, l.990-995). The first sentence is open
      in the record (l.1103-1104). Line numbers are those of the deposited text 2503.05562v1.txt. *)
Definition subcubic_domination_packing_statement : Prop :=
  forall G : sgraph,
    connected [set: G] -> subcubic G ->
    exists D P : {set G}, [/\ dominating D, x312_packing P & #|D| <= 2 * #|P| + 1].

(** Corpus row: studies:std_sintiari_trotignon_conjecture_bounded_treewidth
    Site: none
    Review: none
    English statement: (Sintiari and Trotignon's conjecture; studies slice of the corpus, records arXiv:2203.06775 and
      arXiv:2307.13684, the latter's Conjecture 1.1) For every integer t, there exists a constant c_t such that every
      even-hole-free graph G with no diamond and no clique of size t satisfies tw(G) <= c_t.
    Definitions: [hole h] - GTBase's hole (induced_cycles.v): a chordless cycle on at least four vertices; "every
      hole has odd length" is the even-hole-free condition (X27's x27_even_hole_free in the canonical form, no local
      helper); [induced_free G H] - no induced subgraph of G is isomorphic to H (GTBase common.v); [x42_diamond] - the
      diamond, K_4 minus an edge (minor-theory X42.v); ['K_t] - the complete graph on t vertices, so
      [induced_free G 'K_t] says that G has no clique of size t; [tw_le G c] - G has a tree decomposition whose bags
      have at most c + 1 vertices, that is tw(G) <= c (minor-theory width_params.v).
    Notes: the records exclude the diamond and the clique as induced subgraphs (2307.13684v3 l.33-34: "G contains H if
      some induced subgraph of G is isomorphic to H"; 2203.06775v2 l.10-11, l.15); a hole is an induced cycle on at
      least four vertices (2203.06775v2 l.10). 2307.13684v3 l.89: "[21] only states the two conjectures above for
      t = 4"; that form is 2203.06775v2 Conjecture 1.5 (l.131), which X42's
      even_hole_k4_diamond_free_bounded_treewidth_statement encodes. 2307.13684v3 l.89-90 reports Conjecture 1.1
      "recently proved in [6]" (Alecu, Chudnovsky, Hajebi and Spirkl, a manuscript, l.1141); the status change is a
      separate literature item. Line numbers are those of the deposited texts 2203.06775v2.txt and 2307.13684v3.txt. *)
Definition even_hole_diamond_kt_free_bounded_treewidth_statement : Prop :=
  forall t : nat, exists c : nat,
    forall G : sgraph,
      (forall h : seq G, hole h -> odd (size h)) ->
      induced_free G x42_diamond ->
      induced_free G 'K_t ->
      tw_le G c.

(** Corpus row: arxiv:1908.03788#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1908.03788__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1908.03788__00.json
    English statement: (Bonamy, Defrain, Hatzel and Thiebaut 2019, "Avoidable paths in graphs", arXiv:1908.03788,
      Question 1.12) For every positive integer k, does every graph G either not contain two disjoint P_k, or contain
      two disjoint avoidable P_k?
    Definitions: P_k - an induced path on k vertices (l.70): a sequence p of k vertices with
      [nonempty_induced_path p] (GTBase induced_paths.v); [x91_avoidable_path p] - p is an induced path and every
      induced two-sided extension of p lies in a chordless cycle, that is p has no failing extension (graph-theory-misc
      X91.v; the record's Definition 1.7, l.66-68); [disjoint p & q] - p and q have no common vertex.
    Notes: encoded as stated, the question's positive answer as a proposition. The record answers it: positive for
      k in {1, 2} (l.118-119, by [BCG+19, Theorems 3.3 and 6.4]) and negative for every k >= 3 (l.118-129: a cycle on
      2k - 1 vertices with an added vertex adjacent to two consecutive cycle vertices contains two disjoint P_k but no
      two disjoint avoidable P_k; Figure 1 for k = 3). The row is disproved in the corpus; a kernel disproof from that
      graph is a later item. Line numbers are those of the deposited text 1908.03788v1.txt. *)
Definition two_disjoint_avoidable_paths_statement : Prop :=
  forall k : nat, 0 < k ->
    forall G : sgraph,
      ~ (exists p q : seq G,
           [/\ size p = k, size q = k, nonempty_induced_path p, nonempty_induced_path q
             & [disjoint p & q]])
      \/ exists p q : seq G,
           [/\ size p = k, size q = k, x91_avoidable_path p, x91_avoidable_path q & [disjoint p & q]].

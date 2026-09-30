(** * Cycle.conjectures.XE2 -- Erdős solved clean/bounded rows *)

From Cycle.conjectures Require Import XE1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition xe2_same_vertex_set (G : sgraph) (c d : seq G) : Prop :=
  [set v : G | v \in c] = [set v : G | v \in d].

Definition xe2_edge_disjoint_cycles
    (G : sgraph) (k : nat) (C : 'I_k -> seq G) : Prop :=
  forall i j : 'I_k, i != j ->
    [disjoint xe1_cycle_edges (C i) & xe1_cycle_edges (C j)].

Definition xe2_cycle_lengths (G : sgraph) (L : seq nat) : Prop :=
  uniq L /\
  forall ell : nat,
    ell \in L <->
    exists c : seq G, xe1_cycle c /\ size c = ell.

Definition xe2_min_degree_at_least (G : sgraph) (k : nat) : Prop :=
  forall v : G, k <= #|N(v)|.

Definition xe2_distinct_cycle_lengths_at_least (G : sgraph) (q : nat) : Prop :=
  exists L : seq nat, xe2_cycle_lengths G L /\ q <= size L.

Definition xe2_arithmetic_progression (P : nat -> Prop) : Prop :=
  exists a d : nat,
    0 < d /\ forall n : nat, P n <-> exists i : nat, n = a + d * i.

Definition xe2_contains_even (P : nat -> Prop) : Prop :=
  exists n : nat, P n /\ ~~ odd n.

Definition xe2_all_cycle_lengths_in (G : sgraph) (P : nat -> Prop) : Prop :=
  exists c : seq G, xe1_cycle c /\ P (size c).

Definition xe2_proper_induced_subgraphs_min_degree_le2 (G : sgraph) : Prop :=
  forall S : {set G}, S != set0 -> S != [set: G] ->
    exists v : G, v \in S /\ #|N(v) :&: S| <= 2.

(** Corpus row: erdos:641
    Site: none
    Review: none
    English statement: (Erdos problem #641)
      There is a function f from natural numbers to natural numbers such that for every k
      at least 1 and every simple graph G whose chromatic number is at least f(k), there
      are k cycles of G, each through more than two vertices, that all have the same vertex
      set and whose edge sets are pairwise disjoint.
    Definitions: [xe2_same_vertex_set c d] - c and d have the same set of vertices (XE2.v);
      [xe2_edge_disjoint_cycles C] - the edge sets of the cycles are pairwise disjoint
      (XE2.v); [xe1_cycle c] - c is a [ucycle] of length more than two, and
      [xe1_cycle_edges c] - its edge set (cycle-theory/theories/conjectures/XE1.v);
      [chi_mem], written [chi(A)] - the chromatic number of the induced subgraph on A
      (coq-graph-theory coloring.v, re-exported by base/theories/base.v).
    Notes: the corpus records this row as SOLVED, and phrases it as a question; the Rocq
      statement is its affirmative form. The k cycles are indexed by a finite ordinal type,
      so for k = 1 the conditions degenerate to the existence of one cycle. The corpus row
      has no site or review page. *)
Definition erdos_641_statement : Prop :=
  exists f : nat -> nat,
    forall (k : nat) (G : sgraph),
      1 <= k ->
      f k <= χ([set: G]) ->
      exists C : 'I_k -> seq G,
        (forall i : 'I_k, xe1_cycle (C i)) /\
        (forall i j : 'I_k, xe2_same_vertex_set (C i) (C j)) /\
        xe2_edge_disjoint_cycles C.

(** Corpus row: erdos:71
    Site: none
    Review: none
    English statement: (Erdos problem #71)
      For every set P of natural numbers that is an infinite arithmetic progression, that
      is, there are a and d with d positive such that P consists exactly of the numbers
      a + d*i, and that contains at least one even number, there is a natural number c such
      that every simple graph with at least one vertex whose average degree is at least c
      has a cycle through more than two vertices whose length belongs to P.
    Definitions: [xe2_arithmetic_progression P] - P is the set of a + d*i for a fixed a and
      a positive d (XE2.v); [xe2_contains_even P] - some even number belongs to P (XE2.v);
      [xe2_all_cycle_lengths_in G P] - SOME cycle of G of length more than two has its
      length in P (XE2.v); [xe1_cycle] (cycle-theory/theories/conjectures/XE1.v);
      [average_degree_geq G a b] - the average degree is at least a/b, stated as
      a * |V| <= b * the sum of the degrees (base/theories/base.v).
    Notes: the corpus records this row as SOLVED, and phrases it as a question; the Rocq
      statement is its affirmative form. The name [xe2_all_cycle_lengths_in] is misleading:
      the predicate asserts the EXISTENCE of one cycle with length in P, which is what the
      source asks. [average_degree_geq G c 1] is the average degree at least c. The corpus
      row has no site or review page. *)
Definition erdos_71_statement : Prop :=
  forall P : nat -> Prop,
    xe2_arithmetic_progression P ->
    xe2_contains_even P ->
    exists c : nat,
      forall G : sgraph,
        0 < #|G| ->
        average_degree_geq G c 1 ->
        xe2_all_cycle_lengths_in G P.

(** Corpus row: erdos:752
    Site: none
    Review: none
    English statement: (Erdos problem #752)
      For every natural number s at least 1 there are a positive natural number C and a
      threshold k0 such that for every k at least k0 and every simple graph G with at least
      one vertex in which every vertex has at least k neighbours and every cycle has length
      more than 2s, there is a duplicate-free list L of natural numbers containing exactly
      the lengths of the cycles of G, of length more than two, with k to the power s at
      most C times the size of L. In other words, the number of distinct cycle lengths is
      at least k^s / C.
    Definitions: [xe2_min_degree_at_least G k] - every vertex has at least k neighbours
      (XE2.v); [xe2_cycle_lengths G L] - L is duplicate-free and its members are exactly
      the lengths of the cycles of G through more than two vertices (XE2.v);
      [xe2_distinct_cycle_lengths_at_least] - the companion predicate bounding the size of
      such a list (XE2.v); [xe1_cycle] (cycle-theory/theories/conjectures/XE1.v);
      [girth_geq G g] - every cycle through more than two vertices has length at least g
      (base/theories/base.v).
    Notes: the corpus records this row as SOLVED, and phrases it as a question; the Rocq
      statement is its affirmative form. The source's Vinogradov symbol, "at least of the
      order of k^s distinct cycle lengths", is read as: for FIXED s the count is at least
      c(s) * k^s for some positive c(s) and all large enough k. The hidden constant
      c = 1/C is placed on the right-hand side as a DIVISOR, that is, the bound is
      k ^ s <= C * (number of distinct lengths). The multiplicative reading, at least
      C * k^s lengths, would force c >= 1 and is provably false: the complete graph on k+1
      vertices has only k-1 distinct cycle lengths, refuting s = 1 for any k >= 2 and any
      C >= 1, and a near-Moore graph of minimum degree k and girth more than 2s has about
      (k-1)^s vertices, hence fewer than k^s cycle lengths. Both C and the minimum-degree
      threshold k0 are chosen per s, because the asymptotics are in k for fixed s and
      c(s) may tend to 0; k0 excludes low-degree pathologies such as a tree of minimum
      degree 1 or a single long cycle of high girth. The guard [0 < #|G|] rules out the
      empty graph, which satisfies the degree and girth hypotheses vacuously yet has no
      cycle. Girth more than 2s is written [girth_geq G (2 * s).+1]. *)
Definition erdos_752_statement : Prop :=
  forall s : nat, 1 <= s ->
    exists C k0 : nat,
      0 < C /\
      forall (k : nat) (G : sgraph),
        0 < #|G| ->
        k0 <= k ->
        xe2_min_degree_at_least G k ->
        girth_geq G (2 * s).+1 ->
        exists L : seq nat, xe2_cycle_lengths G L /\ k ^ s <= C * size L.

(** Corpus row: erdos:815
    Site: none
    Review: none
    English statement: (Erdos problem #815)
      For every natural number k at least 3 there is a threshold N such that for every n at
      least N and every simple graph G with exactly n vertices and exactly 2n-2 edges in
      which every proper nonempty induced subgraph has a vertex of degree at most 2 inside
      it, G contains a cycle with exactly k vertices.
    Definitions: [xe2_proper_induced_subgraphs_min_degree_le2 G] - every vertex set that is
      neither empty nor the whole vertex set contains a vertex with at most two neighbours
      inside it (XE2.v); [xe1_edge_set G] - the two-element vertex sets that are edges, and
      [xe1_cycle c] - c is a [ucycle] of length more than two
      (cycle-theory/theories/conjectures/XE1.v).
    Notes: the corpus records this row as SOLVED, and phrases it as a question; the Rocq
      statement is its affirmative form. "n sufficiently large" is encoded by a threshold N
      depending on k, quantified after k. The edge count uses truncated natural
      subtraction in [2 * n - 2], harmless for n at least 1. The corpus row has no site or
      review page. *)
Definition erdos_815_statement : Prop :=
  forall k : nat, 3 <= k ->
    exists N : nat,
      forall (n : nat) (G : sgraph),
        N <= n ->
        #|G| = n ->
        #|xe1_edge_set G| = 2 * n - 2 ->
        xe2_proper_induced_subgraphs_min_degree_le2 G ->
        exists c : seq G, xe1_cycle c /\ size c = k.


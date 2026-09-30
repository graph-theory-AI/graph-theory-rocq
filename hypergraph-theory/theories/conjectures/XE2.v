(** * Hypergraph.conjectures.XE2 -- Erdos solved clean/bounded rows *)

From GTBase Require Export base.
From Hypergraph.conjectures Require Import X6.
From Hypergraph.conjectures Require Import XE1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition xe2_hyperclique (T : finType) (E : {set {set T}}) (S : {set T}) : Prop :=
  forall e : {set T}, e \subset S -> #|e| = 3 -> e \in E.

Definition xe2_maximal_hyperclique
    (T : finType) (E : {set {set T}}) (S : {set T}) : Prop :=
  xe2_hyperclique E S /\
  forall U : {set T}, S \proper U -> ~ xe2_hyperclique E U.

Definition xe2_clique_size_set (T : finType) (E : {set {set T}}) (L : seq nat) : Prop :=
  uniq L /\
  forall q : nat,
    q \in L <->
    exists S : {set T}, xe2_maximal_hyperclique E S /\ #|S| = q.

Definition xe2_complete_uniform_on
    (T : finType) (E : {set {set T}}) (r : nat) (S : {set T}) : Prop :=
  E = [set e : {set T} | (e \subset S) && (#|e| == r)].

Definition xe2_fractional_exponential_degree
    (cnum cden r d : nat) : Prop :=
  0 < cden /\ cden ^ r * d >= (cden + cnum) ^ r.

(** Corpus row: erdos:775
    Site: none
    Review: none
    English statement: (Erdos problem #775)
      There is a constant C such that for every n there is a 3-uniform hypergraph on n vertices
      whose maximal complete subhypergraphs realise at least n - C distinct sizes.
    Definitions: [xe2_hyperclique E S] - every three-element subset of S is a hyperedge
      (hypergraph-theory/theories/conjectures/XE2.v); [xe2_maximal_hyperclique E S] - S is a
      hyperclique and no proper superset of S is (same file); [xe2_clique_size_set E L] - L is a
      duplicate-free list whose entries are exactly the sizes of the maximal hypercliques of E
      (same file); [x6_uniform E 3] (hypergraph-theory/theories/conjectures/X6.v).
    Notes: "at least n - O(1) different sizes" is stated without subtraction, as
      n <= size L + C, with the constant C chosen before n.  The set of realised sizes is
      presented as a duplicate-free list characterised by a membership equivalence, so its
      length is exactly the number of distinct sizes.  The corpus records this row as
      solved. *)
Definition erdos_775_statement : Prop :=
  exists C : nat,
    forall n : nat, exists (T : finType) (E : {set {set T}}) (L : seq nat),
      #|T| = n /\
      x6_uniform E 3 /\
      xe2_clique_size_set E L /\
      n <= size L + C.

(** Corpus row: erdos:832
    Site: none
    Review: none
    English statement: (Erdos problem #832)
      For every r at least 3 there is a threshold K such that every r-uniform hypergraph whose
      chromatic number k is at least K has at least ((r-1)(k-1)+1 choose r) hyperedges, with
      equality only when the hypergraph consists of exactly the r-element subsets of a set of
      (r-1)(k-1)+1 vertices.
    Definitions: [xe2_complete_uniform_on E r S] - E is exactly the family of r-element subsets
      of S (hypergraph-theory/theories/conjectures/XE2.v); [x6_uniform E r] - every hyperedge has
      exactly r vertices (hypergraph-theory/theories/conjectures/X6.v); [x6_chromatic_number E k] - k is
      the least number of colours admitting a colouring with no monochromatic hyperedge (same
      file).
    Notes: "k sufficiently large in terms of r" is the threshold K, chosen after r and before
      k and the hypergraph.  The equality case is the second conjunct, phrased as an
      implication from the exact hyperedge count to the existence of the complete witness set,
      rather than as a separate claim.  The corpus records this row as solved. *)
Definition erdos_832_statement : Prop :=
  forall r : nat, 3 <= r ->
    exists K : nat,
      forall (k : nat) (T : finType) (E : {set {set T}}),
        K <= k ->
        x6_uniform E r ->
        x6_chromatic_number E k ->
        'C((r - 1) * (k - 1) + 1, r) <= #|E| /\
        (#|E| = 'C((r - 1) * (k - 1) + 1, r) ->
          exists S : {set T},
            #|S| = (r - 1) * (k - 1) + 1 /\
            xe2_complete_uniform_on E r S).

(** Corpus row: erdos:833
    Site: none
    Review: none
    English statement: (Erdos problem #833)
      There is an absolute positive constant c such that for every r at least 2, every r-uniform
      hypergraph with chromatic number 3 has a vertex lying in at least (1+c) to the power r
      hyperedges.
    Definitions: [xe2_fractional_exponential_degree cnum cden r d] - the denominator cden is
      positive and cden^r * d is at least (cden + cnum)^r, i.e. d >= (1 + cnum/cden)^r
      (hypergraph-theory/theories/conjectures/XE2.v); [x6_uniform E r] (hypergraph-theory/theories/conjectures/X6.v);
      [x6_chromatic_number E 3] - 3 is the least number of colours admitting a colouring with
      no monochromatic hyperedge (same file); [x6_hg_degree E v] - the number of hyperedges
      containing v (same file).
    Notes: the real constant c is presented as a positive rational cnum/cden, chosen before r
      and the hypergraph (it is "absolute"), and the bound d >= (1+c)^r is cleared of
      denominators by multiplying through by cden^r.  The corpus records this row as
      solved. *)
Definition erdos_833_statement : Prop :=
  exists cnum cden : nat,
    0 < cnum /\ 0 < cden /\
    forall (r : nat) (T : finType) (E : {set {set T}}),
      2 <= r ->
      x6_uniform E r ->
      x6_chromatic_number E 3 ->
      exists v : T,
        xe2_fractional_exponential_degree cnum cden r (x6_hg_degree E v).

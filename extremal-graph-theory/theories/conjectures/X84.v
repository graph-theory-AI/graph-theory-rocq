(** * Extremal.conjectures.X84 -- v2 odd-cycle-free cycle extremal row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X84 vocabulary ************************************************)

Definition x84_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

Definition x84_edge_rel (G : sgraph) (F : {set {set G}}) : rel G :=
  fun x y => [set x; y] \in F.

Definition x84_support (G : sgraph) (F : {set {set G}}) : {set G} :=
  [set v : G | [exists e in F, v \in e]].

Definition x84_degree_in (G : sgraph) (F : {set {set G}}) (v : G) : nat :=
  #|[set e in F | v \in e]|.

Definition x84_connected_support (G : sgraph) (F : {set {set G}}) : bool :=
  [forall x in x84_support F,
    [forall y in x84_support F, connect (x84_edge_rel F) x y]].

Definition x84_cycle_edge_set (G : sgraph) (F : {set {set G}}) : bool :=
  [&& F \subset x84_edge_set G,
      2 < #|x84_support F|,
      #|F| == #|x84_support F|,
      [forall v in x84_support F, x84_degree_in F v == 2]
    & x84_connected_support F].

Definition x84_cycle_count (G : sgraph) : nat :=
  #|[set F : {set {set G}} | @x84_cycle_edge_set G F]|.

Definition x84_has_cycle_length (G : sgraph) (l : nat) : Prop :=
  exists F : {set {set G}},
    @x84_cycle_edge_set G F /\ #|x84_support F| = l.

Definition x84_turan2_rel (n : nat) : rel 'I_n :=
  fun i j => (i != j) && ((i < n %/ 2) != (j < n %/ 2)).

Lemma x84_turan2_sym n : symmetric (@x84_turan2_rel n).
Proof.
by move=> i j; rewrite /x84_turan2_rel eq_sym; case: (i < n %/ 2); case: (j < n %/ 2).
Qed.

Lemma x84_turan2_irrefl n : irreflexive (@x84_turan2_rel n).
Proof. by move=> i; rewrite /x84_turan2_rel eqxx. Qed.

Definition x84_turan2 (n : nat) : sgraph :=
  SGraph (@x84_turan2_sym n) (@x84_turan2_irrefl n).

(** Corpus row: studies:std_arman_gunderson_tsaturian_conjecture_maximum_cyc
    Site: none
    Review: none
    English statement: (Arman, Gunderson and Tsaturian, "Arman-Gunderson-Tsaturian Conjecture (maximum cycles in C_{2k+1}-free graphs)")
      For every k > 1 there is a threshold N such that for every n >= N the balanced complete
      bipartite graph T_2(n) has no cycle of length 2k+1, and every graph G on n vertices with
      no cycle of length 2k+1 has at most as many cycles as T_2(n), with equality only if G is
      isomorphic to T_2(n).
    Definitions: [x84_edge_set G] - the edges as 2-element sets (X84.v); [x84_edge_rel F],
      [x84_support F], [x84_degree_in F v], [x84_connected_support F] - the adjacency, the
      vertices touched, the degrees and the connectivity of an edge set (X84.v);
      [x84_cycle_edge_set G F] - F is a set of edges of G spanning more than 2 vertices, with
      as many edges as vertices, every touched vertex of degree 2, and connected support, i.e.
      F is a cycle (X84.v); [x84_cycle_count G] - the number of such edge sets (X84.v);
      [x84_has_cycle_length G l] - some such cycle has exactly l vertices (X84.v);
      [x84_turan2 n] - the Turan graph T_2(n) on 'I_n, i and j adjacent when exactly one of
      them is below n/2 (X84.v); [~=] - graph isomorphism (coq-graph-theory).
    Notes: this row comes from the studies slice of the corpus, which has no site or review page.
      Cycles are counted as edge sets (each cycle once, not once per traversal). The uniqueness
      clause is stated as an implication from equality of counts to isomorphism, which is the
      Prop form of "is the unique extremal graph"; the C_{2k+1}-freeness of T_2(n) itself is
      asserted as part of the conclusion, making the statement non-vacuous. *)
Definition odd_cycle_free_turan2_unique_cycle_extremal_statement : Prop :=
  forall k : nat,
    1 < k ->
    exists N : nat,
      forall n : nat,
        N <= n ->
        ~ x84_has_cycle_length (x84_turan2 n) (2 * k + 1) /\
        forall G : sgraph,
          #|G| = n ->
          ~ x84_has_cycle_length G (2 * k + 1) ->
          x84_cycle_count G <= x84_cycle_count (x84_turan2 n) /\
          (x84_cycle_count G = x84_cycle_count (x84_turan2 n) ->
             inhabited (G ≃ x84_turan2 n)).

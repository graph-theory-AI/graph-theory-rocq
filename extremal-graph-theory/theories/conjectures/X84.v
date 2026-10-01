(** * Extremal.conjectures.X84 -- v2 odd-cycle-free cycle extremal row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X84 vocabulary ************************************************)

Definition x84_edge_set (G : sgraph) : {set {set G}} :=
  simple_edge_set G.

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

(** ** X84 statements ******************************************************)

(** Studies slice: Arman-Gunderson-Tsaturian conjecture that, for fixed k>1
    and large n, the balanced complete bipartite Turan graph uniquely maximizes
    the number of cycles among C_(2k+1)-free n-vertex graphs. *)
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

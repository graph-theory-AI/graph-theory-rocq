(** * Extremal.conjectures.X36 -- v2 divisible-subgraph row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X36 vocabulary ************************************************)

Definition x36_edge_set (G : sgraph) : {set {set G}} :=
  simple_edge_set G.

Definition x36_degree_in_edge_set
    (G : sgraph) (F : {set {set G}}) (v : G) : nat :=
  #|[set e in F | v \in e]|.

Definition x36_nonempty_k_divisible_subgraph (G : sgraph) (k : nat) : Prop :=
  exists F : {set {set G}},
    F != set0 /\
    F \subset x36_edge_set G /\
    forall v : G, x36_degree_in_edge_set F v %% k == 0.

(** ** X36 statements ******************************************************)

(** Studies slice: Alon-Friedland-Kalai k-divisible subgraph conjecture. *)
Definition alon_friedland_kalai_divisible_subgraph_statement : Prop :=
  forall (k : nat) (G : sgraph),
    0 < k ->
    ~ x36_nonempty_k_divisible_subgraph G k ->
    #|x36_edge_set G| <= (k - 1) * #|G|.

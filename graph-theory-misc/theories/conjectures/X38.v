(** * GTMisc.conjectures.X38 -- v2 minimum-degree irregular-subgraph row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X38 vocabulary ************************************************)

Definition x38_edge_set (G : sgraph) : {set {set G}} :=
  simple_edge_set G.

Definition x38_subgraph_degree
    (G : sgraph) (F : {set {set G}}) (v : G) : nat :=
  #|[set e in F | v \in e]|.

Definition x38_degree_class_size
    (G : sgraph) (F : {set {set G}}) (k : nat) : nat :=
  #|[set v : G | x38_subgraph_degree F v == k]|.

Definition x38_min_degree_at_least (G : sgraph) (delta : nat) : Prop :=
  forall v : G, delta <= #|N(v)|.

(** ** X38 statements ******************************************************)

(** arXiv:2108.02685, small maximum degree-class size in a spanning subgraph. *)
Definition min_degree_spanning_subgraph_small_degree_multiplicity_statement : Prop :=
  forall (delta : nat) (G : sgraph),
    x38_min_degree_at_least G delta ->
    exists F : {set {set G}},
      F \subset x38_edge_set G /\
      forall k : nat,
        (delta.+1 * @x38_degree_class_size G F k <= #|G| + 2 * delta.+1)%N.

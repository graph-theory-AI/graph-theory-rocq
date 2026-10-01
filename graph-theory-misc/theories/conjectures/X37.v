(** * GTMisc.conjectures.X37 -- v2 regular irregular-subgraph row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X37 vocabulary ************************************************)

Definition x37_edge_set (G : sgraph) : {set {set G}} :=
  simple_edge_set G.

Definition x37_subgraph_degree
    (G : sgraph) (F : {set {set G}}) (v : G) : nat :=
  #|[set e in F | v \in e]|.

Definition x37_degree_class_size
    (G : sgraph) (F : {set {set G}}) (k : nat) : nat :=
  #|[set v : G | x37_subgraph_degree F v == k]|.

Definition x37_close_to_uniform_degree_class
    (G : sgraph) (d : nat) (F : {set {set G}}) (k : nat) : Prop :=
  let m := x37_degree_class_size F k in
  (d.+1 * m <= #|G| + 2 * d.+1)%N /\
  (#|G| <= d.+1 * (m + 2))%N.

(** ** X37 statements ******************************************************)

(** arXiv:2108.02685, degree-class balancing in regular graphs. *)
Definition regular_graph_spanning_subgraph_degree_class_balance_statement : Prop :=
  forall (d : nat) (G : sgraph),
    regular G d ->
    exists F : {set {set G}},
      F \subset x37_edge_set G /\
      forall k : nat,
        k <= d ->
        @x37_close_to_uniform_degree_class G d F k.

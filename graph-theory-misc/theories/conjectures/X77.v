(** * GTMisc.conjectures.X77 -- v2 separation dimension row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X77 vocabulary ************************************************)

Definition x77_edge_set (G : sgraph) : {set {set G}} :=
  simple_edge_set G.

Definition x77_separates_edges
    (G : sgraph) (pos : G -> nat) (e f : {set G}) : Prop :=
  (forall x y : G, x \in e -> y \in f -> pos x < pos y) \/
  (forall x y : G, x \in e -> y \in f -> pos y < pos x).

Definition x77_separation_dimension_at_most (G : sgraph) (k : nat) : Prop :=
  exists pos : 'I_k -> G -> nat,
    (forall i : 'I_k, injective (pos i)) /\
    forall e f : {set G},
      e \in x77_edge_set G ->
      f \in x77_edge_set G ->
      e != f ->
      [disjoint e & f] ->
      exists i : 'I_k, x77_separates_edges (pos i) e f.

(** ** X77 statements ******************************************************)

(** Studies slice: Alon et al. conjecture that separation dimension is linear
    in maximum degree. *)
Definition separation_dimension_maximum_degree_linear_statement : Prop :=
  exists c : nat,
    forall G : sgraph,
      x77_separation_dimension_at_most G (c * Delta G).

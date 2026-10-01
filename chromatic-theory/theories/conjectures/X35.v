(** * Chromatic.conjectures.X35 -- v2 sparse cut chromatic row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X35 vocabulary ************************************************)

Definition x35_edge_set (G : sgraph) : {set {set G}} :=
  simple_edge_set G.

(** A GENUINE cut/separator (arXiv:2510.01791, Conjecture 1.3): deleting [X]
    disconnects [G], i.e. the subgraph induced on [V(G) \ X] (= [~: X]) is
    disconnected.  Empty [X] is a legitimate cut exactly when [G] itself is
    disconnected -- the folklore [k = 1] case (chi(G[emptyset]) = 0 < 1). *)
Definition x35_nontrivial_cut (G : sgraph) (X : {set G}) : Prop :=
  disconnected (~: X).

(** ** X35 statements ******************************************************)

(** arXiv:2510.01791, sparse graph cut question. *)
Definition sparse_graph_low_chromatic_cut_statement : Prop :=
  forall (k : nat) (G : sgraph),
    0 < k ->
    k <= #|G| ->
    (2 * #|x35_edge_set G| < 2 * k * #|G| - k * k.+1)%N ->
    exists X : {set G},
      x35_nontrivial_cut X /\
      χ([set: induced X]) < k.

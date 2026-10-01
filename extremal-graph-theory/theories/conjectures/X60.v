(** * Extremal.conjectures.X60 -- v2 polynomial induced-saturation row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X60 vocabulary ************************************************)

Fixpoint x60_poly_eval (p : seq nat) (x : nat) : nat :=
  if p is a :: q then a + x * x60_poly_eval q x else 0.

Definition x60_edge_set (G : sgraph) : {set {set G}} :=
  simple_edge_set G.

Definition x60_delete_edge_rel (G : sgraph) (e : {set G}) : rel G :=
  fun x y => (x -- y) && ([set x; y] != e).

Lemma x60_delete_edge_sym (G : sgraph) (e : {set G}) :
  symmetric (@x60_delete_edge_rel G e).
Proof. by move=> x y; rewrite /x60_delete_edge_rel sgP setUC. Qed.

Lemma x60_delete_edge_irrefl (G : sgraph) (e : {set G}) :
  irreflexive (@x60_delete_edge_rel G e).
Proof. by move=> x; rewrite /x60_delete_edge_rel sg_irrefl. Qed.

Definition x60_delete_edge_graph (G : sgraph) (e : {set G}) : sgraph :=
  SGraph (@x60_delete_edge_sym G e) (@x60_delete_edge_irrefl G e).

Definition x60_has_induced_cycle (G : sgraph) (n : nat) : Prop :=
  exists S : {set G}, #|S| = n /\ inhabited (induced S ≃ cycle_graph n).

(** ** X60 statements ******************************************************)

(** arXiv:2505.24100, Question 1.8, with the same even-cycle repair as X49:
    the manifest flags the source's "$H$-free" as garbled in this context. *)
Definition induced_saturation_even_cycle_polynomial_size_statement : Prop :=
  exists p : seq nat,
    forall t : nat,
      3 <= t ->
      exists G : sgraph,
        #|G| <= x60_poly_eval p t /\
        0 < #|x60_edge_set G| /\
        ~ x60_has_induced_cycle G (2 * t - 2) /\
        forall e : {set G},
          e \in x60_edge_set G ->
          x60_has_induced_cycle (@x60_delete_edge_graph G e) (2 * t - 2).

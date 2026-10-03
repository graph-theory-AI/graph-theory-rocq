(** Public-only clients: ordinary chromatic bounds, graph classes and supplied
    representations. No conjecture, area foundation or migration imports. *)
From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph coloring.
From GTBase Require Import chi_bounding.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Example empty_class : chi_bounded_class (fun _ : sgraph => False).
Proof. exact: chi_bounded_class_empty. Qed.

Example one_vertex_class : chi_bounded_class (fun G : sgraph => #|G| <= 1).
Proof. exact: chi_bounded_class_bounded_order. Qed.

Example class_restriction (F H : sgraph -> Prop) :
  (forall G, F G -> H G) -> chi_bounded_class H -> chi_bounded_class F.
Proof. exact: chi_bounded_class_sub. Qed.

Example either_class (F H : sgraph -> Prop) :
  chi_bounded_class F -> chi_bounded_class H ->
  chi_bounded_class (fun G => F G \/ H G).
Proof. exact: chi_bounded_class_union. Qed.

Example labels_do_not_restrict_the_bound (A B : Type) (U : B -> sgraph)
    (h : A -> B) (F : A -> Prop) :
  chi_bounded_via (fun x => U (h x)) F <->
  chi_bounded_via U (fun y => exists x, F x /\ h x = y).
Proof. exact: chi_bounded_via_image. Qed.

Example guard_keeps_the_same_bound (A : Type) (U : A -> sgraph) (F : A -> Prop) :
  chi_bounded_via U F -> chi_bounded_via U (fun x => F x /\ 0 < #|U x|).
Proof. apply: chi_bounded_via_sub; by move=> x []. Qed.

Example empty_members_are_harmless (G : sgraph) (f : nat -> nat) :
  #|G| = 0 -> χ([set: G]) <= f (ω([set: G])).
Proof. exact: empty_graph_chi_bound. Qed.

(** A concrete wrong bound: the zero function cannot bound even K1. This is
    a failed supplied witness, not a claim that the singleton class is unbounded. *)
Example zero_bound_fails_on_K1 : ~ (χ([set: 'K_1]) <= 0).
Proof.
have complete_clique : clique [set: 'K_1] by move=> x y _ _.
by rewrite (chi_clique complete_clique) cardsT card_ord.
Qed.

Example zero_does_bound_K0 : χ([set: 'K_0]) <= 0.
Proof.
have complete_clique : clique [set: 'K_0] by move=> x y _ _.
by rewrite (chi_clique complete_clique) cardsT card_ord.
Qed.

Example fixed_clique_obstruction (A : Type) (U : A -> sgraph) (F : A -> Prop) m :
  (forall n, exists x, [/\ F x, ω([set: U x]) = m & n < χ([set: U x])]) ->
  ~ chi_bounded_via U F.
Proof. exact: not_chi_bounded_via_of_unbounded_at. Qed.

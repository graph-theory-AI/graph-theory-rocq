(** Public-only clients of poset unavoidability.  They import only GTBase, upstream
    minors and the public Minor foundation.  The unit-poset checks show what the
    dimension guard excludes; they do NOT claim that ['K_2] is avoidable for every
    threshold. *)
From GTBase Require Import base.
From GraphTheory Require Import minor.
From Minor.foundations Require Import poset_unavoidability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Example empty_graph_unavoidable : poset_unavoidable 'K_0.
Proof. exact: poset_unavoidable_K0. Qed.

Example threshold_can_be_raised (H : sgraph) (d : nat) :
  (forall P : finite_poset, ~ poset_dimension_at_most P d -> minor (poset_cover_graph P) H) ->
  forall P : finite_poset, ~ poset_dimension_at_most P d.+1 -> minor (poset_cover_graph P) H.
Proof. exact: poset_unavoidable_threshold (leqnSn d). Qed.

Example minors_of_unavoidable_graphs (H K : sgraph) :
  poset_unavoidable H -> minor H K -> poset_unavoidable K.
Proof. exact: poset_unavoidable_minor. Qed.

(** The realizer may be empty: the one-point poset has dimension at most 0, hence at
    most every threshold, so the dimension guard never tests it. *)
Example unit_poset_dimension_zero : poset_dimension_at_most unit_poset 0.
Proof.
by exists [::]; split=> //.
Qed.

Example unit_poset_never_tested (d : nat) : ~ ~ poset_dimension_at_most unit_poset d.
Proof. by move=> nd; apply: nd; exact: poset_dimension_at_mostW (leq0n d) unit_poset_dimension_zero. Qed.

(** The guard has teeth: the unit poset's one-vertex cover graph has no ['K_2] minor,
    so without the guard no threshold could make ['K_2] unavoidable. *)
Example unit_cover_graph_has_no_K2_minor : ~ minor (poset_cover_graph unit_poset) 'K_2.
Proof.
move=> /minor_card; rewrite card_ord.
by have -> : #|poset_cover_graph unit_poset| = 1 by rewrite card_unit.
Qed.

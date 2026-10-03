(** * C10: class closure with all original guards retained
    Frozen at 5f8211a. Strong hereditary means isomorphism AND induced closure;
    the Packing variant has only induced closure. No inhabitance is added. *)
From GTBase Require Import base graph_classes.
From Minor.conjectures Require Import X220.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x220_iso_closed (C : sgraph -> Prop) : Prop :=
  forall G H : sgraph, C G -> diso G H -> C H.

Definition x220_hereditary_class (C : sgraph -> Prop) : Prop :=
  Legacy.x220_iso_closed C /\ forall (G : sgraph) (S : {set G}), C G -> C (induced S).

Definition small_hereditary_class_bounded_twin_width_statement : Prop :=
  forall C : sgraph -> Prop,
    Legacy.x220_hereditary_class C -> x220_small_class C ->
    exists d : nat, forall G : sgraph, C G -> x220_twin_width_le G d.

End Legacy.

Lemma x220_iso_closed_compat (C : sgraph -> Prop) :
  Legacy.x220_iso_closed C <-> x220_iso_closed C.
Proof. by []. Qed.

Lemma x220_hereditary_class_compat (C : sgraph -> Prop) :
  Legacy.x220_hereditary_class C <-> x220_hereditary_class C.
Proof. by []. Qed.

Lemma small_hereditary_class_bounded_twin_width_statement_compat :
  Legacy.small_hereditary_class_bounded_twin_width_statement <->
  small_hereditary_class_bounded_twin_width_statement.
Proof. by []. Qed.

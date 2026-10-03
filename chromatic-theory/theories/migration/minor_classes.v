(** * C11: exact excluded-minor and minor-closure contracts
    Frozen at 6e1a1c4. X192 has a witness ONLY; X168 additionally closes under
    minors. Complete row guards, quantifier order and documented defects stay. *)
From GTBase Require Import base minor_classes.
From Chromatic.conjectures Require Import X192.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x192_proper_minor_closed_class (C : sgraph -> Prop) : Prop :=
  exists H : sgraph, forall G : sgraph, C G -> ~ minor G H.

Definition triangle_free_minor_closed_chromatic_additive_approx_statement : Prop :=
  exists alpha : nat,
    forall C : sgraph -> Prop,
      Legacy.x192_proper_minor_closed_class C ->
      x192_polytime_additive_chromatic_approx C alpha.

End Legacy.

Lemma x192_proper_minor_closed_class_compat (C : sgraph -> Prop) :
  Legacy.x192_proper_minor_closed_class C <-> x192_proper_minor_closed_class C.
Proof. by []. Qed.

Lemma triangle_free_minor_closed_chromatic_additive_approx_statement_compat :
  Legacy.triangle_free_minor_closed_chromatic_additive_approx_statement <->
  triangle_free_minor_closed_chromatic_additive_approx_statement.
Proof. by []. Qed.

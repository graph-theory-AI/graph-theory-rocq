(** * C10: class closure with all original guards retained
    Frozen at 5f8211a. Strong hereditary means isomorphism AND induced closure;
    the Packing variant has only induced closure. No inhabitance is added. *)
From GTBase Require Import base graph_classes.
From Chromatic.conjectures Require Import U8 X3.
From Chromatic.migration Require chi_bounded_classes.
Module ChiLegacy := Chromatic.migration.chi_bounded_classes.Legacy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x3_iso_closed (F : sgraph -> Prop) : Prop :=
  forall G H : sgraph, x3_iso G H -> F G -> F H.

Definition x3_hereditary_class (F : sgraph -> Prop) : Prop :=
  Legacy.x3_iso_closed F /\ forall (G : sgraph) (S : {set G}), F G -> F (induced S).

Definition hereditary_chi_bounded_not_polynomial_statement : Prop :=
  exists F : sgraph -> Prop,
    Legacy.x3_hereditary_class F /\
    chi_bounded F /\
    ~ x3_polynomially_chi_bounded F.

End Legacy.

Module X3Original.

Definition hereditary_chi_bounded_not_polynomial_statement : Prop :=
  exists F : sgraph -> Prop,
    Legacy.x3_hereditary_class F /\
    ChiLegacy.chi_bounded F /\
    ~ x3_polynomially_chi_bounded F.

End X3Original.

Lemma x3_iso_closed_compat (F : sgraph -> Prop) :
  Legacy.x3_iso_closed F <-> x3_iso_closed F.
Proof.
split=> closed G H.
- move=> FG iso; exact: closed G H (inhabits iso) FG.
- move=> [iso] FG; exact: closed G H FG iso.
Qed.

Lemma x3_hereditary_class_compat (F : sgraph -> Prop) :
  Legacy.x3_hereditary_class F <-> x3_hereditary_class F.
Proof.
split=> -[iso sub]; split=> //.
- by apply/x3_iso_closed_compat.
- by apply/x3_iso_closed_compat.
Qed.

Lemma hereditary_chi_bounded_not_polynomial_statement_compat :
  Legacy.hereditary_chi_bounded_not_polynomial_statement <->
  hereditary_chi_bounded_not_polynomial_statement.
Proof.
split=> -[F [hered [bounded notpoly]]]; exists F; split.
- by apply/x3_hereditary_class_compat.
- by split.
- by apply/x3_hereditary_class_compat.
- by split.
Qed.

(** Complete C9/C10 history: the same existential class, with both frozen
    closure and frozen ordinary chi-boundedness, and unchanged polynomial negation. *)
Lemma hereditary_chi_bounded_not_polynomial_statement_original_compat :
  X3Original.hereditary_chi_bounded_not_polynomial_statement <->
  hereditary_chi_bounded_not_polynomial_statement.
Proof. exact: hereditary_chi_bounded_not_polynomial_statement_compat. Qed.

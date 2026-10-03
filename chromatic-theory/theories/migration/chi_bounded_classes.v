(** * C9: frozen ordinary chi-boundedness and complete statements
    Originals are pinned at 0659592. All guards, class quantifiers and status
    discrepancies stay unchanged; only the recorded references use frozen
    dependencies. The A6 Original composes the existing frozen complement. *)
From GTBase Require Import base chi_bounding.
From Chromatic.conjectures Require Import U8 X3 X112 X170.
From Chromatic.foundations Require chi_bounding.
From Chromatic.migration Require complement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module ComplementLegacy := Chromatic.migration.complement.X3Legacy.

Module Legacy.

Definition chi_bounded (F : sgraph -> Prop) : Prop :=
  exists f : nat -> nat,
    forall G : sgraph, F G -> χ([set: G]) <= f (ω([set: G])).

End Legacy.

Module X112Legacy.

Definition x112_chi_bounded (D : sgraph -> Prop) : Prop :=
  exists f : nat -> nat,
    forall G : sgraph, D G -> χ([set: G]) <= f (x112_omega G).

End X112Legacy.

Module X170Legacy.

Definition x170_chi_bounded (C : x170_oriented_graph -> Prop) : Prop :=
  exists f : nat -> nat,
    forall O : x170_oriented_graph,
      C O -> χ([set: x170_underlying O]) <= f (ω([set: x170_underlying O])).

End X170Legacy.

Module FoundationLegacy.

Definition chi_bounded_class (F : sgraph -> Prop) : Prop :=
  exists f : nat -> nat,
    forall G : sgraph, F G -> χ([set: G]) <= f (ω([set: G])).

End FoundationLegacy.

Module U8Legacy.

Definition graphs_with_a_forbidden_induced_tree_are_chi_bounded_statement : Prop :=
  forall T : sgraph, is_tree [set: T] ->
    Legacy.chi_bounded (fun G : sgraph => ~ has_induced T G).

Definition vertex_minor_closed_classes_are_chi_bounded_statement : Prop :=
  forall F : sgraph -> Prop,
    vminor_closed F -> proper_class F -> Legacy.chi_bounded F.

End U8Legacy.

Module X3Legacy.

Definition hereditary_chi_bounded_not_polynomial_statement : Prop :=
  exists F : sgraph -> Prop,
    x3_hereditary_class F /\
    Legacy.chi_bounded F /\
    ~ x3_polynomially_chi_bounded F.

Definition gyarfas_complementation_chi_bounded_statement : Prop :=
  forall (c : nat) (C : sgraph -> Prop),
    x3_chi_omega_plus_bound C c ->
    Legacy.chi_bounded (x3_complement_image C).

Definition gyarfas_alpha_omega_chi_bounded_statement : Prop :=
  Legacy.chi_bounded x3_alpha_omega_large_class.

End X3Legacy.

Module X112StatementsLegacy.

Definition chi_bounded_closure_substitution_gluing_statement : Prop :=
  forall (C : sgraph -> Prop) (b : nat),
    X112Legacy.x112_chi_bounded C -> X112Legacy.x112_chi_bounded (x112_closure C b).

End X112StatementsLegacy.

Module X170StatementsLegacy.

Definition oriented_P4_forb_chi_bounded_statement : Prop :=
  forall P : {set x170_oriented_P4_code},
    x170_nonexceptional P ->
    X170Legacy.x170_chi_bounded (x170_forb_oriented_P4_family P).

End X170StatementsLegacy.

Module X3Original.

Definition gyarfas_complementation_chi_bounded_statement : Prop :=
  forall (c : nat) (C : sgraph -> Prop),
    x3_chi_omega_plus_bound C c ->
    Legacy.chi_bounded (ComplementLegacy.complement_image C).

End X3Original.

Lemma chi_bounded_compat (F : sgraph -> Prop) :
  Legacy.chi_bounded F <-> Chromatic.conjectures.U8.chi_bounded F.
Proof. by []. Qed.

Lemma x112_chi_bounded_compat (F : sgraph -> Prop) :
  X112Legacy.x112_chi_bounded F <-> x112_chi_bounded F.
Proof. by []. Qed.

Lemma x170_chi_bounded_compat (F : x170_oriented_graph -> Prop) :
  X170Legacy.x170_chi_bounded F <-> x170_chi_bounded F.
Proof. by []. Qed.

Lemma chi_bounded_class_compat (F : sgraph -> Prop) :
  FoundationLegacy.chi_bounded_class F <->
  Chromatic.foundations.chi_bounding.chi_bounded_class F.
Proof. by []. Qed.

Lemma graphs_with_a_forbidden_induced_tree_are_chi_bounded_statement_compat :
  U8Legacy.graphs_with_a_forbidden_induced_tree_are_chi_bounded_statement <->
  graphs_with_a_forbidden_induced_tree_are_chi_bounded_statement.
Proof. by []. Qed.

Lemma vertex_minor_closed_classes_are_chi_bounded_statement_compat :
  U8Legacy.vertex_minor_closed_classes_are_chi_bounded_statement <->
  vertex_minor_closed_classes_are_chi_bounded_statement.
Proof. by []. Qed.

Lemma hereditary_chi_bounded_not_polynomial_statement_compat :
  X3Legacy.hereditary_chi_bounded_not_polynomial_statement <->
  hereditary_chi_bounded_not_polynomial_statement.
Proof. by []. Qed.

Lemma gyarfas_complementation_chi_bounded_statement_compat :
  X3Legacy.gyarfas_complementation_chi_bounded_statement <->
  gyarfas_complementation_chi_bounded_statement.
Proof. by []. Qed.

Lemma gyarfas_alpha_omega_chi_bounded_statement_compat :
  X3Legacy.gyarfas_alpha_omega_chi_bounded_statement <->
  gyarfas_alpha_omega_chi_bounded_statement.
Proof. by []. Qed.

Lemma chi_bounded_closure_substitution_gluing_statement_compat :
  X112StatementsLegacy.chi_bounded_closure_substitution_gluing_statement <->
  chi_bounded_closure_substitution_gluing_statement.
Proof. by []. Qed.

Lemma oriented_P4_forb_chi_bounded_statement_compat :
  X170StatementsLegacy.oriented_P4_forb_chi_bounded_statement <->
  oriented_P4_forb_chi_bounded_statement.
Proof. by []. Qed.

(** Complete pre-A6/C9 statement, with the same class and bound witnesses. *)
Lemma gyarfas_complementation_chi_bounded_statement_original_compat :
  X3Original.gyarfas_complementation_chi_bounded_statement <->
  gyarfas_complementation_chi_bounded_statement.
Proof.
split=> h c C bound; have [f hf] := h c C bound; exists f => G image.
all: apply: hf; by apply/Chromatic.migration.complement.x3_complement_image_compat.
Qed.

(** * C10: class closure with all original guards retained
    Frozen at 5f8211a. Strong hereditary means isomorphism AND induced closure;
    the Packing variant has only induced closure. No inhabitance is added. *)
From GTBase Require Import base graph_classes.
From Packing.conjectures Require Import X155.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x155_hereditary_class (C : sgraph -> Prop) : Prop :=
  forall (G : sgraph) (S : {set G}), C G -> C (induced S).

Definition identifying_code_vc_dimension_approximation_dichotomy_statement : Prop :=
  forall C : sgraph -> Prop,
    Legacy.x155_hereditary_class C ->
    (x155_log_lower_bound C /\ x155_log_APX_hard C) \/
    (x155_polynomial_lower_bound C /\ x155_constant_factor_approximation C).

End Legacy.

(** This source retains induced closure ONLY, with no isomorphism or inhabitance
    assumption. The original blocked dichotomy is intentionally unchanged. *)
Lemma x155_hereditary_class_compat (C : sgraph -> Prop) :
  Legacy.x155_hereditary_class C <-> x155_hereditary_class C.
Proof. by []. Qed.

Lemma identifying_code_vc_dimension_approximation_dichotomy_statement_compat :
  Legacy.identifying_code_vc_dimension_approximation_dichotomy_statement <->
  identifying_code_vc_dimension_approximation_dichotomy_statement.
Proof. by []. Qed.

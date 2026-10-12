(** A30: finite-set weights, frozen at the accepted parent 3bdfdae32824d4762ba8105367f7858a706a02e2.
    - [X190Legacy]: X190's [x190_weight], its separator class [x190_strongly_sublinear_separator_class] and the
      WHOLE row, verbatim; the row keeps the live overlay system, whose documented identity-cover vacuity stays
      blocked and unrepaired.
    - [X199Legacy]: X199's [x199_weight], its balanced separator, the constant-M chain and the WHOLE row,
      verbatim, with the documented class, quantifier and bound defects blocked and unrepaired.
    These rows have no earlier family history, so the current chains are the complete originals. The live weights
    are transparent aliases of upstream [weight_set] with the same body, so each certificate is a conversion.
    X190 keeps a, b, K with 0 < a < b, the exponent bound and the weighted connected-part balance; X199 keeps the
    bound chosen before ell >= 1, both cardinality bounds and the balance. Zero weights and empty sets stay
    allowed; no positivity is added. *)
From GTBase Require Import base.
From Minor.conjectures Require Import X190 X199.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module X190Legacy.

Definition x190_weight (G : sgraph) (rho : G -> nat) (S : {set G}) : nat :=
  \sum_(v in S) rho v.

Definition x190_strongly_sublinear_separator_class (C : sgraph -> Prop) : Prop :=
  exists a b K : nat,
    0 < a /\ a < b /\
    forall (G : sgraph) (rho : G -> nat),
      C G ->
      exists S : {set G},
        (#|S| ^ b <= K * (#|G|.+1 ^ a)) /\
        forall A : {set G},
          A \subset ~: S ->
          connected A ->
          2 * X190Legacy.x190_weight rho A <= X190Legacy.x190_weight rho [set: G].

Definition thin_overlay_without_bounded_degree_statement : Prop :=
  forall C : sgraph -> Prop,
    X190Legacy.x190_strongly_sublinear_separator_class C ->
    x190_thin_system_of_overlays C.

End X190Legacy.

Module X199Legacy.

Definition x199_weight (G : sgraph) (rho : G -> nat) (S : {set G}) : nat :=
  \sum_(v in S) rho v.

Definition x199_weighted_balanced_separator
    (G : sgraph) (rho : G -> nat) (S M : {set G}) : Prop :=
  forall A : {set G},
    A \subset ~: (S :|: M) ->
    connected A ->
    2 * X199Legacy.x199_weight rho A <= X199Legacy.x199_weight rho [set: G].

Definition x199_weighted_balanced_separator_with_constant_M
    (C : sgraph -> Prop) (ell bound : nat) : Prop :=
  forall (G : sgraph) (rho : G -> nat),
    C G ->
    exists S M : {set G},
      [/\ #|M| <= bound,
          #|S| <= ell * sqrt_ceil #|G|.+1 + ell &
          X199Legacy.x199_weighted_balanced_separator rho S M].

Definition strongly_sublinear_separator_constant_M_statement : Prop :=
  forall C : sgraph -> Prop,
    exists bound : nat,
      forall ell : nat,
        1 <= ell ->
        X199Legacy.x199_weighted_balanced_separator_with_constant_M C ell bound.

End X199Legacy.

(** The live weights are upstream [weight_set], the same body. *)
Lemma x190_weight_compat (G : sgraph) (rho : G -> nat) (S : {set G}) :
  X190Legacy.x190_weight rho S = x190_weight rho S.
Proof. by []. Qed.

Lemma x190_strongly_sublinear_separator_class_compat (C : sgraph -> Prop) :
  X190Legacy.x190_strongly_sublinear_separator_class C <-> x190_strongly_sublinear_separator_class C.
Proof. exact: iff_refl. Qed.

Lemma thin_overlay_without_bounded_degree_statement_compat :
  X190Legacy.thin_overlay_without_bounded_degree_statement <-> thin_overlay_without_bounded_degree_statement.
Proof. exact: iff_refl. Qed.

Lemma x199_weight_compat (G : sgraph) (rho : G -> nat) (S : {set G}) :
  X199Legacy.x199_weight rho S = x199_weight rho S.
Proof. by []. Qed.

Lemma x199_weighted_balanced_separator_compat (G : sgraph) (rho : G -> nat) (S M : {set G}) :
  X199Legacy.x199_weighted_balanced_separator rho S M <-> x199_weighted_balanced_separator rho S M.
Proof. exact: iff_refl. Qed.

Lemma x199_weighted_balanced_separator_with_constant_M_compat (C : sgraph -> Prop) (ell bound : nat) :
  X199Legacy.x199_weighted_balanced_separator_with_constant_M C ell bound <->
  x199_weighted_balanced_separator_with_constant_M C ell bound.
Proof. exact: iff_refl. Qed.

Lemma strongly_sublinear_separator_constant_M_statement_compat :
  X199Legacy.strongly_sublinear_separator_constant_M_statement <->
  strongly_sublinear_separator_constant_M_statement.
Proof. exact: iff_refl. Qed.

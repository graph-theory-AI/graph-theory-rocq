(** C23: ambient grad bounds, frozen at the fixed C22 pin
    30459e9b9eeebbdb5451c70c529bd2e5dfb64c99.
    - [X128Legacy], [X139Legacy]: the two local grad sources, their expansion chains and both
      WHOLE current rows, verbatim. These per-row copies keep the live C16 model aliases
      [x128_shallow_minor_model] / [x139_shallow_minor_model] and the live A7 public count
      [fg_edge_count], as the sources did; the live grad sources now unfold to
      [GTMisc.foundations.ambient_shallow_minors.ambient_grad_at_most G r d], the same body.
    - The complete histories are the existing A7+C16 Originals
      [GTMisc.migration.ambient_shallow_minors.X128Original] and [X139Original], reused with
      their whole-row iff certificates; no new Original is added.
    X128 keeps p before q, the individual-graph hypothesis and 1 <= t; X139 keeps one p for the
    whole class and all radii, one conclusion f, and its documented blocked defect (the
    backward r-ball omits the internal-order condition of strong reachability), unrepaired. *)
From GTBase Require Import base.
From GTMisc.foundations Require Import ambient_shallow_minors.
From GTMisc.conjectures Require Import X128 X139.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module X128Legacy.

Definition x128_grad_at_most (G : sgraph) (r d : nat) : Prop :=
  forall H : sgraph,
    x128_shallow_minor_model G H r ->
    2 * fg_edge_count H <= d * #|H|.

Definition x128_expansion_bounded (G : sgraph) (p : seq nat) : Prop :=
  forall r : nat, X128Legacy.x128_grad_at_most G r (x128_poly_eval p r).

Definition dvorak_cheap_balanced_separator_bounded_expansion_statement : Prop :=
  forall p : seq nat,
    exists q : nat -> nat,
      forall (G : sgraph) (rho : G -> nat) (t : nat),
        1 <= t ->
        X128Legacy.x128_expansion_bounded G p ->
        x128_cheap_bal_sep rho t (q t).

End X128Legacy.

Module X139Legacy.

Definition x139_grad_at_most (G : sgraph) (r d : nat) : Prop :=
  forall H : sgraph,
    x139_shallow_minor_model G H r ->
    2 * fg_edge_count H <= d * #|H|.

Definition x139_polynomial_expansion_class (C : sgraph -> Prop) : Prop :=
  exists p : seq nat,
    forall (r : nat) (G : sgraph), C G -> X139Legacy.x139_grad_at_most G r (x139_poly_eval p r).

Definition esperet_raymond_polynomial_expansion_scol_statement : Prop :=
  forall C : sgraph -> Prop,
    X139Legacy.x139_polynomial_expansion_class C ->
    exists f : seq nat,
      forall (r : nat) (G : sgraph),
        C G -> x139_scol_at_most G r (x139_poly_eval f r).

End X139Legacy.

(** The live sources are the canonical body over the same C16 model and A7 count. *)
Lemma x128_grad_at_most_compat (G : sgraph) (r d : nat) :
  X128Legacy.x128_grad_at_most G r d <-> x128_grad_at_most G r d.
Proof. exact: iff_refl. Qed.

Lemma x128_expansion_bounded_compat (G : sgraph) (p : seq nat) :
  X128Legacy.x128_expansion_bounded G p <-> x128_expansion_bounded G p.
Proof.
split=> h r.
- exact: (proj1 (x128_grad_at_most_compat G r _) (h r)).
- exact: (proj2 (x128_grad_at_most_compat G r _) (h r)).
Qed.

Lemma dvorak_cheap_balanced_separator_bounded_expansion_statement_compat :
  X128Legacy.dvorak_cheap_balanced_separator_bounded_expansion_statement <->
  dvorak_cheap_balanced_separator_bounded_expansion_statement.
Proof.
split=> st p; have [q hq] := st p; exists q => G rho t t1 bounded.
- exact: hq G rho t t1 (proj2 (x128_expansion_bounded_compat G p) bounded).
- exact: hq G rho t t1 (proj1 (x128_expansion_bounded_compat G p) bounded).
Qed.

Lemma x139_grad_at_most_compat (G : sgraph) (r d : nat) :
  X139Legacy.x139_grad_at_most G r d <-> x139_grad_at_most G r d.
Proof. exact: iff_refl. Qed.

Lemma x139_polynomial_expansion_class_compat (C : sgraph -> Prop) :
  X139Legacy.x139_polynomial_expansion_class C <-> x139_polynomial_expansion_class C.
Proof.
split=> -[p hp]; exists p => r G CG.
- exact: (proj1 (x139_grad_at_most_compat G r _) (hp r G CG)).
- exact: (proj2 (x139_grad_at_most_compat G r _) (hp r G CG)).
Qed.

Lemma esperet_raymond_polynomial_expansion_scol_statement_compat :
  X139Legacy.esperet_raymond_polynomial_expansion_scol_statement <->
  esperet_raymond_polynomial_expansion_scol_statement.
Proof.
split=> st C cls.
- exact: st C (proj2 (x139_polynomial_expansion_class_compat C) cls).
- exact: st C (proj1 (x139_polynomial_expansion_class_compat C) cls).
Qed.

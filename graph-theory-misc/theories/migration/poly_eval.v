(** A31: natural Horner evaluation, frozen at the reviewed candidate parent db16a76376d1a9c29142b38f97d5109d6dd942fa.
    - [X128Legacy] / [X139Legacy]: the raw [Fixpoint]s [x128_poly_eval] / [x139_poly_eval], the expansion chains
      [x128_expansion_bounded] / [x139_polynomial_expansion_class] over them, and the WHOLE current rows, verbatim.  They keep
      the live grad sources (C23), the live A30 separator and the live scol bound, as the sources did.
    - [X128Original] / [X139Original]: the complete deepest rows.  The expansion chain is the deepest existing one
      ([GTMisc.migration.ambient_shallow_minors.X128Original] / [X139Original], aliased [ASM]: frozen A7 count, C16 radius,
      model and grad) with its one remaining live provider, the evaluator, replaced by the raw [Fixpoint] frozen here; X128's
      row also keeps A30's frozen separator and weight ([GTMisc.migration.set_weights.X128Legacy], aliased [SW]), as A30's
      deepest Original did.  Each whole-row iff composes the evaluator equality with the earlier Originals' certificates.
    The live evaluators are transparent aliases of [GTBase.poly_nat.horner_nat]; every evaluator certificate is an
    UNCONDITIONAL pointwise equality, so every row is equivalent in every polarity (X128's expansion bound and X139's class
    are hypotheses).  X128 keeps p before q, the individual-graph hypothesis and 1 <= t; X139 keeps one p for the class and
    one f for the conclusion; its documented blocked defect stays unrepaired. *)
From GTBase Require Import base.
From GTBase Require poly_nat.
From GTMisc.conjectures Require Import X128 X139.
From GTMisc Require migration.ambient_shallow_minors migration.set_weights.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module ASM := GTMisc.migration.ambient_shallow_minors.
Module SW := GTMisc.migration.set_weights.

Module X128Legacy.

Fixpoint x128_poly_eval (p : seq nat) (x : nat) : nat :=
  if p is a :: q then a + x * x128_poly_eval q x else 0.

Definition x128_expansion_bounded (G : sgraph) (p : seq nat) : Prop :=
  forall r : nat, x128_grad_at_most G r (X128Legacy.x128_poly_eval p r).

Definition dvorak_cheap_balanced_separator_bounded_expansion_statement : Prop :=
  forall p : seq nat,
    exists q : nat -> nat,
      forall (G : sgraph) (rho : G -> nat) (t : nat),
        1 <= t ->
        X128Legacy.x128_expansion_bounded G p ->
        x128_cheap_bal_sep rho t (q t).

End X128Legacy.

Module X139Legacy.

Fixpoint x139_poly_eval (p : seq nat) (x : nat) : nat :=
  if p is a :: q then a + x * x139_poly_eval q x else 0.

Definition x139_polynomial_expansion_class (C : sgraph -> Prop) : Prop :=
  exists p : seq nat,
    forall (r : nat) (G : sgraph), C G -> x139_grad_at_most G r (X139Legacy.x139_poly_eval p r).

Definition esperet_raymond_polynomial_expansion_scol_statement : Prop :=
  forall C : sgraph -> Prop,
    X139Legacy.x139_polynomial_expansion_class C ->
    exists f : seq nat,
      forall (r : nat) (G : sgraph),
        C G -> x139_scol_at_most G r (X139Legacy.x139_poly_eval f r).

End X139Legacy.

Module X128Original.

Definition x128_expansion_bounded (G : sgraph) (p : seq nat) : Prop :=
  forall r : nat, ASM.X128Original.x128_grad_at_most G r (X128Legacy.x128_poly_eval p r).

Definition dvorak_cheap_balanced_separator_bounded_expansion_statement : Prop :=
  forall p : seq nat,
    exists q : nat -> nat,
      forall (G : sgraph) (rho : G -> nat) (t : nat),
        1 <= t ->
        X128Original.x128_expansion_bounded G p ->
        SW.X128Legacy.x128_cheap_bal_sep rho t (q t).

End X128Original.

Module X139Original.

Definition x139_polynomial_expansion_class (C : sgraph -> Prop) : Prop :=
  exists p : seq nat,
    forall (r : nat) (G : sgraph), C G -> ASM.X139Original.x139_grad_at_most G r (X139Legacy.x139_poly_eval p r).

Definition esperet_raymond_polynomial_expansion_scol_statement : Prop :=
  forall C : sgraph -> Prop,
    X139Original.x139_polynomial_expansion_class C ->
    exists f : seq nat,
      forall (r : nat) (G : sgraph),
        C G -> x139_scol_at_most G r (X139Legacy.x139_poly_eval f r).

End X139Original.

(** The raw evaluators equal the live ones (the canonical [horner_nat]) at every list and point. *)
Lemma x128_poly_eval_compat (p : seq nat) (x : nat) : X128Legacy.x128_poly_eval p x = x128_poly_eval p x.
Proof.
rewrite /x128_poly_eval; elim: p => [|a p IH]; first by rewrite GTBase.poly_nat.horner_nat_nil.
have -> : X128Legacy.x128_poly_eval (a :: p) x = a + x * X128Legacy.x128_poly_eval p x by [].
by rewrite IH GTBase.poly_nat.horner_nat_cons.
Qed.

Lemma x139_poly_eval_compat (p : seq nat) (x : nat) : X139Legacy.x139_poly_eval p x = x139_poly_eval p x.
Proof.
rewrite /x139_poly_eval; elim: p => [|a p IH]; first by rewrite GTBase.poly_nat.horner_nat_nil.
have -> : X139Legacy.x139_poly_eval (a :: p) x = a + x * X139Legacy.x139_poly_eval p x by [].
by rewrite IH GTBase.poly_nat.horner_nat_cons.
Qed.

Lemma x128_expansion_bounded_compat (G : sgraph) (p : seq nat) :
  X128Legacy.x128_expansion_bounded G p <-> x128_expansion_bounded G p.
Proof.
split=> h r.
- by rewrite -x128_poly_eval_compat; exact: h.
- by rewrite x128_poly_eval_compat; exact: h.
Qed.

Lemma dvorak_cheap_balanced_separator_bounded_expansion_statement_compat :
  X128Legacy.dvorak_cheap_balanced_separator_bounded_expansion_statement <->
  dvorak_cheap_balanced_separator_bounded_expansion_statement.
Proof.
split=> st p; have [q hq] := st p; exists q => G rho t t1 bounded.
- exact: hq G rho t t1 (proj2 (x128_expansion_bounded_compat G p) bounded).
- exact: hq G rho t t1 (proj1 (x128_expansion_bounded_compat G p) bounded).
Qed.

Lemma x139_polynomial_expansion_class_compat (C : sgraph -> Prop) :
  X139Legacy.x139_polynomial_expansion_class C <-> x139_polynomial_expansion_class C.
Proof.
split=> -[p hp]; exists p => r G CG.
- by rewrite -x139_poly_eval_compat; exact: hp.
- by rewrite x139_poly_eval_compat; exact: hp.
Qed.

Lemma esperet_raymond_polynomial_expansion_scol_statement_compat :
  X139Legacy.esperet_raymond_polynomial_expansion_scol_statement <->
  esperet_raymond_polynomial_expansion_scol_statement.
Proof.
split.
- move=> st C cls; have [f hf] := st C (proj2 (x139_polynomial_expansion_class_compat C) cls).
  by exists f => r G CG; rewrite -x139_poly_eval_compat; exact: hf.
- move=> st C cls; have [f hf] := st C (proj1 (x139_polynomial_expansion_class_compat C) cls).
  by exists f => r G CG; rewrite x139_poly_eval_compat; exact: hf.
Qed.

(** The deepest rows: the evaluator equality over C16's frozen grad chains, then the earlier Originals' certificates. *)
Lemma x128_expansion_bounded_original_compat (G : sgraph) (p : seq nat) :
  X128Original.x128_expansion_bounded G p <-> x128_expansion_bounded G p.
Proof.
rewrite -ASM.x128_expansion_bounded_original_compat.
split=> h r.
- by rewrite -x128_poly_eval_compat; exact: h.
- by rewrite x128_poly_eval_compat; exact: h.
Qed.

Lemma dvorak_cheap_balanced_separator_bounded_expansion_statement_original_compat :
  X128Original.dvorak_cheap_balanced_separator_bounded_expansion_statement <->
  dvorak_cheap_balanced_separator_bounded_expansion_statement.
Proof.
rewrite -SW.dvorak_cheap_balanced_separator_bounded_expansion_statement_original_compat.
have E G p : X128Original.x128_expansion_bounded G p <-> ASM.X128Original.x128_expansion_bounded G p.
  by rewrite x128_expansion_bounded_original_compat ASM.x128_expansion_bounded_original_compat.
split=> st p; have [q hq] := st p; exists q => G rho t t1 bounded.
- exact: hq G rho t t1 (proj2 (E G p) bounded).
- exact: hq G rho t t1 (proj1 (E G p) bounded).
Qed.

Lemma x139_polynomial_expansion_class_original_compat (C : sgraph -> Prop) :
  X139Original.x139_polynomial_expansion_class C <-> x139_polynomial_expansion_class C.
Proof.
rewrite -ASM.x139_polynomial_expansion_class_original_compat.
split=> -[p hp]; exists p => r G CG.
- by rewrite -x139_poly_eval_compat; exact: hp.
- by rewrite x139_poly_eval_compat; exact: hp.
Qed.

Lemma esperet_raymond_polynomial_expansion_scol_statement_original_compat :
  X139Original.esperet_raymond_polynomial_expansion_scol_statement <->
  esperet_raymond_polynomial_expansion_scol_statement.
Proof.
split.
- move=> st C cls; have [f hf] := st C (proj2 (x139_polynomial_expansion_class_original_compat C) cls).
  by exists f => r G CG; rewrite -x139_poly_eval_compat; exact: hf.
- move=> st C cls; have [f hf] := st C (proj1 (x139_polynomial_expansion_class_original_compat C) cls).
  by exists f => r G CG; rewrite x139_poly_eval_compat; exact: hf.
Qed.

(** A7 edge counts: X128 and X139, which reach the public count [GTBase.finite_graph.fg_edge_count]
    through their grad bounds.  Chains and rows are frozen at ae0e605 over the frozen public count
    [GTBase.migration.edge_count.Legacy.fg_edge_count] (aliased [FG]). Baseline, hashes and exact
    substitutions are recorded in meta/migration_reports/edge_count.spec.json. *)
From Corelib Require Import Setoid Morphisms.
From GTBase Require Import base.
From GTMisc.conjectures Require Import X128 X139.
From GTBase Require migration.edge_count.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module FG := GTBase.migration.edge_count.

Module X128Legacy.

Definition grad_at_most (G : sgraph) (r d : nat) : Prop :=
  forall H : sgraph,
    x128_shallow_minor_model G H r ->
    2 * FG.Legacy.fg_edge_count H <= d * #|H|.

Definition expansion_bounded (G : sgraph) (p : seq nat) : Prop :=
  forall r : nat, grad_at_most G r (x128_poly_eval p r).

Definition dvorak_cheap_balanced_separator_bounded_expansion_statement : Prop :=
  forall p : seq nat,
    exists q : nat -> nat,
      forall (G : sgraph) (rho : G -> nat) (t : nat),
        1 <= t ->
        expansion_bounded G p ->
        x128_cheap_bal_sep rho t (q t).

End X128Legacy.

Module X139Legacy.

Definition grad_at_most (G : sgraph) (r d : nat) : Prop :=
  forall H : sgraph,
    x139_shallow_minor_model G H r ->
    2 * FG.Legacy.fg_edge_count H <= d * #|H|.

Definition polynomial_expansion_class (C : sgraph -> Prop) : Prop :=
  exists p : seq nat,
    forall (r : nat) (G : sgraph), C G -> grad_at_most G r (x139_poly_eval p r).

Definition esperet_raymond_polynomial_expansion_scol_statement : Prop :=
  forall C : sgraph -> Prop,
    polynomial_expansion_class C ->
    exists f : seq nat,
      forall (r : nat) (G : sgraph),
        C G -> x139_scol_at_most G r (x139_poly_eval f r).

End X139Legacy.

Lemma x128_grad_at_most_compat (G : sgraph) (r d : nat) :
  @X128Legacy.grad_at_most G r d <-> @x128_grad_at_most G r d.
Proof. rewrite /X128Legacy.grad_at_most /x128_grad_at_most; setoid_rewrite FG.fg_edge_count_compat; reflexivity. Qed.

Lemma x128_expansion_bounded_compat (G : sgraph) (p : seq nat) :
  @X128Legacy.expansion_bounded G p <-> @x128_expansion_bounded G p.
Proof. rewrite /X128Legacy.expansion_bounded /x128_expansion_bounded; setoid_rewrite x128_grad_at_most_compat; reflexivity. Qed.

Lemma dvorak_cheap_balanced_separator_bounded_expansion_statement_compat :
  X128Legacy.dvorak_cheap_balanced_separator_bounded_expansion_statement <-> dvorak_cheap_balanced_separator_bounded_expansion_statement.
Proof. rewrite /X128Legacy.dvorak_cheap_balanced_separator_bounded_expansion_statement /dvorak_cheap_balanced_separator_bounded_expansion_statement; setoid_rewrite x128_expansion_bounded_compat; reflexivity. Qed.

Lemma x139_grad_at_most_compat (G : sgraph) (r d : nat) :
  @X139Legacy.grad_at_most G r d <-> @x139_grad_at_most G r d.
Proof. rewrite /X139Legacy.grad_at_most /x139_grad_at_most; setoid_rewrite FG.fg_edge_count_compat; reflexivity. Qed.

Lemma x139_polynomial_expansion_class_compat (C : sgraph -> Prop) :
  @X139Legacy.polynomial_expansion_class C <-> @x139_polynomial_expansion_class C.
Proof. rewrite /X139Legacy.polynomial_expansion_class /x139_polynomial_expansion_class; setoid_rewrite x139_grad_at_most_compat; reflexivity. Qed.

Lemma esperet_raymond_polynomial_expansion_scol_statement_compat :
  X139Legacy.esperet_raymond_polynomial_expansion_scol_statement <-> esperet_raymond_polynomial_expansion_scol_statement.
Proof. rewrite /X139Legacy.esperet_raymond_polynomial_expansion_scol_statement /esperet_raymond_polynomial_expansion_scol_statement; setoid_rewrite x139_polynomial_expansion_class_compat; reflexivity. Qed.

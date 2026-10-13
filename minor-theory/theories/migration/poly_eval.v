(** A31: natural Horner evaluation, frozen at the reviewed candidate parent db16a76376d1a9c29142b38f97d5109d6dd942fa.
    - [X220Legacy]: X220's raw [foldr] evaluator [x220_poly_eval], its expansion chain [x220_polynomial_expansion] and the
      three WHOLE current rows that use the evaluator (the two tree-alpha rows directly, the twin-width row through the
      chain), verbatim; the chain keeps the live shallow minor, as the source did.
    - [X220Original]: the complete deepest twin-width row: the deepest existing chain
      ([Minor.migration.shallow_minors.Legacy.x220_polynomial_expansion], over the frozen shallow minor, aliased [SM]) with its
      one remaining live provider, the evaluator, replaced by the raw [foldr] frozen here; its whole-row iff composes the
      evaluator equality with that chain's own certificate.  The tree-alpha rows have no earlier history.
    The live evaluator is a transparent alias of [GTBase.poly_nat.horner_nat]; the evaluator certificate is an UNCONDITIONAL
    pointwise equality, so every row is equivalent in every polarity (the twin-width class is a hypothesis).  The
    [0 < m] guard, quantifier order and every other hypothesis are unchanged. *)
From GTBase Require Import base.
From GTBase Require poly_nat.
From Minor.foundations Require Import containment width_params shallow_minors.
From Minor.conjectures Require Import X220.
From Minor.migration Require shallow_minors.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module SM := Minor.migration.shallow_minors.

Module X220Legacy.

Definition x220_poly_eval (p : seq nat) (x : nat) : nat :=
  foldr (fun a acc => a + x * acc) 0 p.

Definition x220_polynomial_expansion (C : sgraph -> Prop) : Prop :=
  exists p : seq nat,
    forall G : sgraph, C G ->
      forall (r : nat) (H : sgraph),
        x220_shallow_minor G H r -> #|E(H)| <= X220Legacy.x220_poly_eval p r * #|H|.

Definition tree_mu_ktt_free_polynomial_tree_alpha_statement : Prop :=
  forall m : nat, 0 < m ->
    exists p : seq nat,
      forall (t : nat) (G : sgraph),
        ~ has_induced_copy G (KB t t) ->
        tree_mu_le G m ->
        tree_alpha_le G (X220Legacy.x220_poly_eval p t).

Definition bounded_tree_mu_polynomial_biclique_tree_alpha_statement : Prop :=
  forall m : nat,
    exists p : seq nat,
      forall (G : sgraph) (t : nat),
        tree_mu_le G m -> x220_ibn G t -> tree_alpha_le G (X220Legacy.x220_poly_eval p t).

Definition polynomial_expansion_bounded_twin_width_statement : Prop :=
  forall C : sgraph -> Prop,
    X220Legacy.x220_polynomial_expansion C ->
    exists d : nat, forall G : sgraph, C G -> x220_twin_width_le G d.

End X220Legacy.

Module X220Original.

Definition x220_polynomial_expansion (C : sgraph -> Prop) : Prop :=
  exists p : seq nat,
    forall G : sgraph, C G ->
      forall (r : nat) (H : sgraph),
        SM.Legacy.x220_shallow_minor G H r -> #|E(H)| <= X220Legacy.x220_poly_eval p r * #|H|.

Definition polynomial_expansion_bounded_twin_width_statement : Prop :=
  forall C : sgraph -> Prop,
    X220Original.x220_polynomial_expansion C ->
    exists d : nat, forall G : sgraph, C G -> x220_twin_width_le G d.

End X220Original.

(** The raw evaluator equals the live one (the canonical [horner_nat]) at every list and point. *)
Lemma x220_poly_eval_compat (p : seq nat) (x : nat) : X220Legacy.x220_poly_eval p x = x220_poly_eval p x.
Proof. by rewrite /x220_poly_eval GTBase.poly_nat.horner_nat_foldr /X220Legacy.x220_poly_eval. Qed.

Lemma x220_polynomial_expansion_compat (C : sgraph -> Prop) :
  X220Legacy.x220_polynomial_expansion C <-> x220_polynomial_expansion C.
Proof.
split=> -[p h]; exists p => G CG r H sm.
- by rewrite -x220_poly_eval_compat; exact: (h G CG r H sm).
- by rewrite x220_poly_eval_compat; exact: (h G CG r H sm).
Qed.

Lemma tree_mu_ktt_free_polynomial_tree_alpha_statement_compat :
  X220Legacy.tree_mu_ktt_free_polynomial_tree_alpha_statement <-> tree_mu_ktt_free_polynomial_tree_alpha_statement.
Proof.
split=> st m m0; have [p hp] := st m m0; exists p => t G nk tm.
- by rewrite -x220_poly_eval_compat; exact: hp.
- by rewrite x220_poly_eval_compat; exact: hp.
Qed.

Lemma bounded_tree_mu_polynomial_biclique_tree_alpha_statement_compat :
  X220Legacy.bounded_tree_mu_polynomial_biclique_tree_alpha_statement <->
  bounded_tree_mu_polynomial_biclique_tree_alpha_statement.
Proof.
split=> st m; have [p hp] := st m; exists p => G t tm ibn.
- by rewrite -x220_poly_eval_compat; exact: hp.
- by rewrite x220_poly_eval_compat; exact: hp.
Qed.

Lemma polynomial_expansion_bounded_twin_width_statement_compat :
  X220Legacy.polynomial_expansion_bounded_twin_width_statement <-> polynomial_expansion_bounded_twin_width_statement.
Proof.
split=> st C pe.
- exact: st C (proj2 (x220_polynomial_expansion_compat C) pe).
- exact: st C (proj1 (x220_polynomial_expansion_compat C) pe).
Qed.

(** The deepest row: the evaluator equality over the frozen shallow minor, then that chain's own certificate. *)
Lemma x220_polynomial_expansion_original_compat (C : sgraph -> Prop) :
  X220Original.x220_polynomial_expansion C <-> x220_polynomial_expansion C.
Proof.
rewrite -SM.x220_polynomial_expansion_compat.
split=> -[p h]; exists p => G CG r H sm.
- by rewrite -x220_poly_eval_compat; exact: (h G CG r H sm).
- by rewrite x220_poly_eval_compat; exact: (h G CG r H sm).
Qed.

Lemma polynomial_expansion_bounded_twin_width_statement_original_compat :
  X220Original.polynomial_expansion_bounded_twin_width_statement <-> polynomial_expansion_bounded_twin_width_statement.
Proof.
split=> st C pe.
- exact: st C (proj2 (x220_polynomial_expansion_original_compat C) pe).
- exact: st C (proj1 (x220_polynomial_expansion_original_compat C) pe).
Qed.

(** A31: natural Horner evaluation, frozen at the reviewed candidate parent db16a76376d1a9c29142b38f97d5109d6dd942fa.
    - [Legacy]: the public foundation's original [foldr] evaluator [Chromatic.foundations.chi_bounding.horner_nat].
    - [X3Legacy] / [X124Legacy]: the raw [Fixpoint]s [x3_poly_eval] / [x124_poly_eval], the list-form classes
      [x3_polynomially_chi_bounded] / [x124_poly_chi_bounded] over them, and the WHOLE X3 / X124 rows, verbatim;
      [X65Legacy], [X66Legacy]: X65's row and X66's [x66_good] with its row, which reach X3's class.
    - [X3Original]: the complete deepest X3 row, the deepest existing Original
      [Chromatic.migration.graph_classes.X3Original] (frozen hereditary class and C9 chi-bounded class) with its one remaining
      live provider, the list-form class, replaced by the raw class frozen here.  [X124Original]: X124's class over the
      raw evaluator and the clique-number family's frozen clique number [Chromatic.migration.clique_number.Legacy.x124_omega], and the row.
    The live evaluators are transparent aliases of [GTBase.poly_nat.horner_nat]; every evaluator certificate is an
    UNCONDITIONAL pointwise equality, so every row is equivalent in every polarity, including X3's negated class.  Quantifier
    order and every conjunct are unchanged; X66's live disjoint union is not touched here. *)
From GTBase Require Import base.
From GTBase Require poly_nat.
From Chromatic.foundations Require chi_bounding.
From Chromatic.conjectures Require Import U8 X3 X65 X66 X124.
From Chromatic.migration Require graph_classes chi_bounded_classes clique_number.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module GC := Chromatic.migration.graph_classes.
Module ChiLegacy := Chromatic.migration.chi_bounded_classes.Legacy.
Module CN := Chromatic.migration.clique_number.

Module Legacy.

Definition horner_nat (p : seq nat) (x : nat) : nat :=
  foldr (fun a r => a + x * r) 0 p.

End Legacy.

Module X3Legacy.

Fixpoint x3_poly_eval (p : seq nat) (x : nat) : nat :=
  if p is a :: q then a + x * x3_poly_eval q x else 0.

Definition x3_polynomially_chi_bounded (F : sgraph -> Prop) : Prop :=
  exists p : seq nat,
    forall G : sgraph, F G -> χ([set: G]) <= X3Legacy.x3_poly_eval p (ω([set: G])).

Definition hereditary_chi_bounded_not_polynomial_statement : Prop :=
  exists F : sgraph -> Prop,
    x3_hereditary_class F /\
    chi_bounded F /\
    ~ X3Legacy.x3_polynomially_chi_bounded F.

End X3Legacy.

Module X65Legacy.

Definition forest_free_polynomial_chi_bound_statement : Prop :=
  forall H : sgraph,
    is_forest [set: H] ->
    X3Legacy.x3_polynomially_chi_bounded (fun G : sgraph => ~ has_induced H G).

End X65Legacy.

Module X66Legacy.

Definition x66_good (H : sgraph) : Prop :=
  X3Legacy.x3_polynomially_chi_bounded (fun G : sgraph => ~ has_induced H G).

Definition good_trees_disjoint_union_good_statement : Prop :=
  forall H1 H2 : sgraph,
    is_tree [set: H1] ->
    is_tree [set: H2] ->
    X66Legacy.x66_good H1 ->
    X66Legacy.x66_good H2 ->
    X66Legacy.x66_good (x66_disjoint_union H1 H2).

End X66Legacy.

Module X124Legacy.

Fixpoint x124_poly_eval (p : seq nat) (x : nat) : nat :=
  if p is a :: q then a + x * x124_poly_eval q x else 0.

Definition x124_poly_chi_bounded (C : sgraph -> Prop) : Prop :=
  exists p : seq nat,
    forall G : sgraph, C G -> χ([set: G]) <= X124Legacy.x124_poly_eval p (x124_omega G).

Definition dreier_torunczyk_merge_width_poly_chi_bounded_statement : Prop :=
  forall C : sgraph -> Prop,
    x124_bounded_merge_width C -> X124Legacy.x124_poly_chi_bounded C.

End X124Legacy.

Module X3Original.

Definition hereditary_chi_bounded_not_polynomial_statement : Prop :=
  exists F : sgraph -> Prop,
    GC.Legacy.x3_hereditary_class F /\
    ChiLegacy.chi_bounded F /\
    ~ X3Legacy.x3_polynomially_chi_bounded F.

End X3Original.

Module X124Original.

Definition x124_poly_chi_bounded (C : sgraph -> Prop) : Prop :=
  exists p : seq nat,
    forall G : sgraph, C G -> χ([set: G]) <= X124Legacy.x124_poly_eval p (CN.Legacy.x124_omega G).

Definition dreier_torunczyk_merge_width_poly_chi_bounded_statement : Prop :=
  forall C : sgraph -> Prop,
    x124_bounded_merge_width C -> X124Original.x124_poly_chi_bounded C.

End X124Original.

(** The raw evaluators equal the live ones (the canonical [horner_nat]) at every list and point. *)
Lemma horner_nat_compat (p : seq nat) (x : nat) :
  Legacy.horner_nat p x = Chromatic.foundations.chi_bounding.horner_nat p x.
Proof. by rewrite /Chromatic.foundations.chi_bounding.horner_nat GTBase.poly_nat.horner_nat_foldr. Qed.

Lemma x3_poly_eval_compat (p : seq nat) (x : nat) : X3Legacy.x3_poly_eval p x = x3_poly_eval p x.
Proof.
rewrite /x3_poly_eval; elim: p => [|a p IH]; first by rewrite GTBase.poly_nat.horner_nat_nil.
have -> : X3Legacy.x3_poly_eval (a :: p) x = a + x * X3Legacy.x3_poly_eval p x by [].
by rewrite IH GTBase.poly_nat.horner_nat_cons.
Qed.

Lemma x124_poly_eval_compat (p : seq nat) (x : nat) : X124Legacy.x124_poly_eval p x = x124_poly_eval p x.
Proof.
rewrite /x124_poly_eval; elim: p => [|a p IH]; first by rewrite GTBase.poly_nat.horner_nat_nil.
have -> : X124Legacy.x124_poly_eval (a :: p) x = a + x * X124Legacy.x124_poly_eval p x by [].
by rewrite IH GTBase.poly_nat.horner_nat_cons.
Qed.

Lemma x3_polynomially_chi_bounded_compat (F : sgraph -> Prop) :
  X3Legacy.x3_polynomially_chi_bounded F <-> x3_polynomially_chi_bounded F.
Proof.
split=> -[p h]; exists p => G FG; move: (h G FG); rewrite x3_poly_eval_compat => le; exact: le.
Qed.

Lemma hereditary_chi_bounded_not_polynomial_statement_compat :
  X3Legacy.hereditary_chi_bounded_not_polynomial_statement <-> hereditary_chi_bounded_not_polynomial_statement.
Proof.
split.
- move=> [F [hF [cF npF]]]; exists F; split; [exact: hF | split; [exact: cF | move=> pF]].
  exact (npF (proj2 (x3_polynomially_chi_bounded_compat F) pF)).
- move=> [F [hF [cF npF]]]; exists F; split; [exact: hF | split; [exact: cF | move=> pF]].
  exact (npF (proj1 (x3_polynomially_chi_bounded_compat F) pF)).
Qed.

Lemma forest_free_polynomial_chi_bound_statement_compat :
  X65Legacy.forest_free_polynomial_chi_bound_statement <-> forest_free_polynomial_chi_bound_statement.
Proof. by split=> h H fH; apply/x3_polynomially_chi_bounded_compat; exact: h. Qed.

Lemma x66_good_compat (H : sgraph) : X66Legacy.x66_good H <-> x66_good H.
Proof. exact: x3_polynomially_chi_bounded_compat. Qed.

Lemma good_trees_disjoint_union_good_statement_compat :
  X66Legacy.good_trees_disjoint_union_good_statement <-> good_trees_disjoint_union_good_statement.
Proof.
split=> h H1 H2 t1 t2 g1 g2; apply/x66_good_compat; apply: h => //; exact/x66_good_compat.
Qed.

Lemma x124_poly_chi_bounded_compat (C : sgraph -> Prop) :
  X124Legacy.x124_poly_chi_bounded C <-> x124_poly_chi_bounded C.
Proof.
split=> -[p h]; exists p => G CG; move: (h G CG); rewrite x124_poly_eval_compat => le; exact: le.
Qed.

Lemma dreier_torunczyk_merge_width_poly_chi_bounded_statement_compat :
  X124Legacy.dreier_torunczyk_merge_width_poly_chi_bounded_statement <->
  dreier_torunczyk_merge_width_poly_chi_bounded_statement.
Proof. by split=> h C mw; apply/x124_poly_chi_bounded_compat; exact: h. Qed.

(** The deepest rows: the raw class or evaluator, then the earlier frozen provider's own registered certificate. *)
Lemma hereditary_chi_bounded_not_polynomial_statement_original_compat :
  X3Original.hereditary_chi_bounded_not_polynomial_statement <-> hereditary_chi_bounded_not_polynomial_statement.
Proof.
rewrite -GC.hereditary_chi_bounded_not_polynomial_statement_original_compat.
split.
- move=> [F [hF [cF npF]]]; exists F; split; [exact: hF | split; [exact: cF | move=> pF]].
  exact (npF (proj2 (x3_polynomially_chi_bounded_compat F) pF)).
- move=> [F [hF [cF npF]]]; exists F; split; [exact: hF | split; [exact: cF | move=> pF]].
  exact (npF (proj1 (x3_polynomially_chi_bounded_compat F) pF)).
Qed.

Lemma x124_poly_chi_bounded_original_compat (C : sgraph -> Prop) :
  X124Original.x124_poly_chi_bounded C <-> x124_poly_chi_bounded C.
Proof.
rewrite -CN.x124_poly_chi_bounded_compat.
split=> -[p h]; exists p => G CG.
- by rewrite -x124_poly_eval_compat; exact: h.
- by rewrite x124_poly_eval_compat; exact: h.
Qed.

Lemma dreier_torunczyk_merge_width_poly_chi_bounded_statement_original_compat :
  X124Original.dreier_torunczyk_merge_width_poly_chi_bounded_statement <->
  dreier_torunczyk_merge_width_poly_chi_bounded_statement.
Proof. by split=> h C mw; apply/x124_poly_chi_bounded_original_compat; exact: h. Qed.

(** A32: the list-form polynomially chi-bounded class, frozen at the A31 candidate 0449699300e18f2ddf0773ede1c81976e632a284
    (stage 1 of the polynomial scope, itself on the reviewed A30 candidate db16a76; neither is accepted main).
    - [X3Legacy] / [X124Legacy]: the classes [x3_polynomially_chi_bounded] / [x124_poly_chi_bounded] and the WHOLE X3 / X124
      rows, verbatim at that commit (over A31's live evaluator aliases [x3_poly_eval] / [x124_poly_eval] and X124's
      [x124_omega]); [X65Legacy], [X66Legacy]: X65's row and X66's [x66_good] with its row, which reach X3's class.
    The live classes are transparent aliases of [Chromatic.foundations.chi_bounding.poly_list_chi_bounded].  Every class
    certificate is a CONVERSION (the evaluator aliases unfold to [GTBase.poly_nat.horner_nat] and [x124_omega G] to
    [ω([set: G])]), so every row is equivalent in every polarity, including X3's negated class.
    - The deepest Originals of X3 and X124 are A31's [PE.X3Original] / [PE.X124Original], whose closures reach no live
      list-form class (A31 froze the class over the raw evaluator).  Their certificates here compose the earlier registered
      provider certificates (C10's hereditary class row, A16's clique number), A31's unconditional evaluator equality and the
      conversion above, so no raw text is lost.
    Quantifier order and every conjunct are unchanged; X66's live disjoint union is not touched here (A28 is pending). *)
From GTBase Require Import base.
From Chromatic.foundations Require chi_bounding.
From Chromatic.conjectures Require Import U8 X3 X65 X66 X124.
From Chromatic.migration Require graph_classes clique_number poly_eval.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module GC := Chromatic.migration.graph_classes.
Module CN := Chromatic.migration.clique_number.
Module PE := Chromatic.migration.poly_eval.

Module X3Legacy.

Definition x3_polynomially_chi_bounded (F : sgraph -> Prop) : Prop :=
  exists p : seq nat,
    forall G : sgraph, F G -> χ([set: G]) <= x3_poly_eval p (ω([set: G])).

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

Definition x124_poly_chi_bounded (C : sgraph -> Prop) : Prop :=
  exists p : seq nat,
    forall G : sgraph, C G -> χ([set: G]) <= x124_poly_eval p (x124_omega G).

Definition dreier_torunczyk_merge_width_poly_chi_bounded_statement : Prop :=
  forall C : sgraph -> Prop,
    x124_bounded_merge_width C -> X124Legacy.x124_poly_chi_bounded C.

End X124Legacy.

(** The classes: conversions to the list-form owner (same coefficient list, same bound). *)
Lemma x3_polynomially_chi_bounded_compat (F : sgraph -> Prop) :
  X3Legacy.x3_polynomially_chi_bounded F <-> x3_polynomially_chi_bounded F.
Proof. exact: iff_refl. Qed.

Lemma x124_poly_chi_bounded_compat (C : sgraph -> Prop) :
  X124Legacy.x124_poly_chi_bounded C <-> x124_poly_chi_bounded C.
Proof. exact: iff_refl. Qed.

(** The rows, through the class certificates. *)
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

Lemma dreier_torunczyk_merge_width_poly_chi_bounded_statement_compat :
  X124Legacy.dreier_torunczyk_merge_width_poly_chi_bounded_statement <->
  dreier_torunczyk_merge_width_poly_chi_bounded_statement.
Proof. by split=> h C mw; apply/x124_poly_chi_bounded_compat; exact: h. Qed.

(** The deepest rows.  A31's raw class against this file's freeze: A31's unconditional evaluator equality. *)
Lemma x3_raw_class_compat (F : sgraph -> Prop) :
  PE.X3Legacy.x3_polynomially_chi_bounded F <-> X3Legacy.x3_polynomially_chi_bounded F.
Proof.
split=> -[p h]; exists p => G FG; move: (h G FG); rewrite PE.x3_poly_eval_compat => le; exact: le.
Qed.

(** X3: C10's registered Original certificate (frozen hereditary class and C9's frozen chi-bounded class, over the live
    list-form class), then A31's raw class to the freeze and the conversion. *)
Lemma hereditary_chi_bounded_not_polynomial_statement_original_compat :
  Chromatic.migration.poly_eval.X3Original.hereditary_chi_bounded_not_polynomial_statement <-> hereditary_chi_bounded_not_polynomial_statement.
Proof.
rewrite -GC.hereditary_chi_bounded_not_polynomial_statement_original_compat.
have cls F : PE.X3Legacy.x3_polynomially_chi_bounded F <-> x3_polynomially_chi_bounded F.
  exact: iff_trans (x3_raw_class_compat F) (x3_polynomially_chi_bounded_compat F).
split.
- move=> [F [hF [cF npF]]]; exists F; split; [exact: hF | split; [exact: cF | move=> pF]].
  exact (npF (proj2 (cls F) pF)).
- move=> [F [hF [cF npF]]]; exists F; split; [exact: hF | split; [exact: cF | move=> pF]].
  exact (npF (proj1 (cls F) pF)).
Qed.

(** X124: A31's raw evaluator and A16's frozen bigmax clique number (A31's and A16's equalities), then the conversion. *)
Lemma x124_poly_chi_bounded_original_compat (C : sgraph -> Prop) :
  Chromatic.migration.poly_eval.X124Original.x124_poly_chi_bounded C <-> x124_poly_chi_bounded C.
Proof.
apply: (iff_trans _ (x124_poly_chi_bounded_compat C)).
split=> -[p h]; exists p => G CG; move: (h G CG).
  by rewrite PE.x124_poly_eval_compat CN.x124_omega_compat => le; exact: le.
by rewrite PE.x124_poly_eval_compat CN.x124_omega_compat => le; exact: le.
Qed.

Lemma dreier_torunczyk_merge_width_poly_chi_bounded_statement_original_compat :
  Chromatic.migration.poly_eval.X124Original.dreier_torunczyk_merge_width_poly_chi_bounded_statement <->
  dreier_torunczyk_merge_width_poly_chi_bounded_statement.
Proof. by split=> h C mw; apply/x124_poly_chi_bounded_original_compat; exact: h. Qed.

Print Assumptions x3_polynomially_chi_bounded_compat.
Print Assumptions x124_poly_chi_bounded_compat.
Print Assumptions hereditary_chi_bounded_not_polynomial_statement_compat.
Print Assumptions forest_free_polynomial_chi_bound_statement_compat.
Print Assumptions x66_good_compat.
Print Assumptions good_trees_disjoint_union_good_statement_compat.
Print Assumptions dreier_torunczyk_merge_width_poly_chi_bounded_statement_compat.
Print Assumptions x3_raw_class_compat.
Print Assumptions hereditary_chi_bounded_not_polynomial_statement_original_compat.
Print Assumptions x124_poly_chi_bounded_original_compat.
Print Assumptions dreier_torunczyk_merge_width_poly_chi_bounded_statement_original_compat.

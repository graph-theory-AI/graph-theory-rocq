(** * Chromatic.migration.surface_embeddable — surface-embeddable certificates: X150, X152, X154, X164

    Family [surface-embeddable] (meta/library_primitives/surface-embeddable.json).  The canonical contract is the
    existing public [GTBase.surface.surface_embeddable surface G]: [G] has a finite rotation system [E] whose encoded
    orientable-genus value [surface_euler_genus E] (the connected-map formula [(2 + edges - vertices - faces) %/ 2] in
    truncated [nat] arithmetic) is at most [surface].  On a disconnected graph this unchanged formula can understate
    the genus, so it is used under each row's own connectedness guard, where the row has one; non-orientable surfaces
    are not modelled.  Nothing here changes that contract or substitutes [surface_embeddable_with_boundary].

    The local wrappers were already direct aliases of the canonical when they were authored (8800958) and are
    unchanged at the baseline 3bdfdae (tree ade432af), so no conjecture file changes: this family classifies them
    and certifies them.  [Legacy] freezes, verbatim at the baseline, the three Chromatic wrappers
    [x150_embeddable_in_fixed_surface], [x152_embeddable_in_fixed_surface] and
    [x164_embedded_in_fixed_surface_with_boundary] (whose [boundary] argument is unused, exactly as authored), and
    every same-file declaration through which a row reaches them: [x150_polytime_decides_3_colourability_on_surface],
    [x152_polytime_decides_four_colourability], [x164_instance_class] (triangle-free, the wrapper, and the separate
    instance constraint [#|x164_boundary I| <= boundary]) and [x164_linear_time_outputs_three_colouring].
    [X150Legacy], [X152Legacy], [X154Legacy] (the duplicate row, literally X152's statement) and [X164Legacy] freeze
    the four complete rows.  No earlier library family froze any of these rows, so they are already the deepest
    originals.  Every certificate is a kernel conversion.

    The [_canonical] lemmas state each wrapper and each complete current row in the canonical vocabulary, with
    [surface_embeddable] written out in place of the wrapper and every guard, bound and quantifier in place.  The X164
    row stays the documented blocked, unfaithful encoding (no extension precondition; orientable surface only; the
    boundary parameter does not constrain the embedding; no connectedness guard); a compatibility certificate is not
    a claim that its English statement is faithful.  X164's output decoder [x164_data_nth_nat] and the chain above it
    belong to the separately queued family natural-data-decoder and are applied live here. *)

From GTBase Require Import base.
From Chromatic.conjectures Require Import X150 X152 X154 X164.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x150_embeddable_in_fixed_surface (surface : nat) (G : sgraph) : Prop :=
  surface_embeddable surface G.

Definition x150_polytime_decides_3_colourability_on_surface (surface : nat) : Prop :=
  polytime_decides_graph_on
    (fun G : sgraph =>
       connected [set: G] /\ Legacy.x150_embeddable_in_fixed_surface surface G /\ girth_geq G 4)
    (fun G : sgraph => χ([set: G]) <= 3).

Definition x152_embeddable_in_fixed_surface (surface : nat) (G : sgraph) : Prop :=
  surface_embeddable surface G.

Definition x152_polytime_decides_four_colourability (surface : nat) : Prop :=
  polytime_decides_graph_on
    (fun G : sgraph => connected [set: G] /\ Legacy.x152_embeddable_in_fixed_surface surface G)
    (fun G : sgraph => χ([set: G]) <= 4).

Definition x164_embedded_in_fixed_surface_with_boundary
    (surface boundary : nat) (G : sgraph) : Prop :=
  surface_embeddable surface G.

Definition x164_instance_class (surface boundary : nat) (I : x164_instance) : Prop :=
  triangle_free (x164_graph I) /\
  Legacy.x164_embedded_in_fixed_surface_with_boundary surface boundary (x164_graph I) /\
  #|x164_boundary I| <= boundary.

Definition x164_linear_time_outputs_three_colouring (surface boundary : nat) : Prop :=
  linear_time_outputs_on_class
    x164_enc_instance (Legacy.x164_instance_class surface boundary) x164_valid_output.

End Legacy.

Module X150Legacy.

Definition gimbel_thomassen_triangle_free_surface_three_colourability_polytime_statement : Prop :=
  forall surface : nat, Legacy.x150_polytime_decides_3_colourability_on_surface surface.

End X150Legacy.

Module X152Legacy.

Definition fixed_surface_four_colourability_polytime_statement : Prop :=
  forall surface : nat,
    0 < surface -> Legacy.x152_polytime_decides_four_colourability surface.

End X152Legacy.

Module X154Legacy.

Definition fixed_surface_four_colourability_polytime_duplicate_statement : Prop :=
  X152Legacy.fixed_surface_four_colourability_polytime_statement.

End X154Legacy.

Module X164Legacy.

Definition linear_time_surface_triangle_free_three_colouring_output_statement : Prop :=
  forall surface boundary : nat,
    Legacy.x164_linear_time_outputs_three_colouring surface boundary.

End X164Legacy.

(** ** Certificates: frozen = live *)

Lemma x150_embeddable_in_fixed_surface_compat (surface : nat) (G : sgraph) :
  Legacy.x150_embeddable_in_fixed_surface surface G <-> x150_embeddable_in_fixed_surface surface G.
Proof. exact: iff_refl. Qed.

Lemma x150_polytime_decides_3_colourability_on_surface_compat (surface : nat) :
  Legacy.x150_polytime_decides_3_colourability_on_surface surface <->
  x150_polytime_decides_3_colourability_on_surface surface.
Proof. exact: iff_refl. Qed.

Lemma gimbel_thomassen_triangle_free_surface_three_colourability_polytime_statement_compat :
  X150Legacy.gimbel_thomassen_triangle_free_surface_three_colourability_polytime_statement <->
  gimbel_thomassen_triangle_free_surface_three_colourability_polytime_statement.
Proof. exact: iff_refl. Qed.

Lemma x152_embeddable_in_fixed_surface_compat (surface : nat) (G : sgraph) :
  Legacy.x152_embeddable_in_fixed_surface surface G <-> x152_embeddable_in_fixed_surface surface G.
Proof. exact: iff_refl. Qed.

Lemma x152_polytime_decides_four_colourability_compat (surface : nat) :
  Legacy.x152_polytime_decides_four_colourability surface <->
  x152_polytime_decides_four_colourability surface.
Proof. exact: iff_refl. Qed.

Lemma fixed_surface_four_colourability_polytime_statement_compat :
  X152Legacy.fixed_surface_four_colourability_polytime_statement <->
  fixed_surface_four_colourability_polytime_statement.
Proof. exact: iff_refl. Qed.

Lemma fixed_surface_four_colourability_polytime_duplicate_statement_compat :
  X154Legacy.fixed_surface_four_colourability_polytime_duplicate_statement <->
  fixed_surface_four_colourability_polytime_duplicate_statement.
Proof. exact: iff_refl. Qed.

Lemma x164_embedded_in_fixed_surface_with_boundary_compat (surface boundary : nat) (G : sgraph) :
  Legacy.x164_embedded_in_fixed_surface_with_boundary surface boundary G <->
  x164_embedded_in_fixed_surface_with_boundary surface boundary G.
Proof. exact: iff_refl. Qed.

Lemma x164_instance_class_compat (surface boundary : nat) (I : x164_instance) :
  Legacy.x164_instance_class surface boundary I <-> x164_instance_class surface boundary I.
Proof. exact: iff_refl. Qed.

Lemma x164_linear_time_outputs_three_colouring_compat (surface boundary : nat) :
  Legacy.x164_linear_time_outputs_three_colouring surface boundary <->
  x164_linear_time_outputs_three_colouring surface boundary.
Proof. exact: iff_refl. Qed.

Lemma linear_time_surface_triangle_free_three_colouring_output_statement_compat :
  X164Legacy.linear_time_surface_triangle_free_three_colouring_output_statement <->
  linear_time_surface_triangle_free_three_colouring_output_statement.
Proof. exact: iff_refl. Qed.

(** ** The wrappers and the complete current rows in the canonical vocabulary *)

Lemma x150_embeddable_in_fixed_surface_canonical (surface : nat) (G : sgraph) :
  x150_embeddable_in_fixed_surface surface G <-> surface_embeddable surface G.
Proof. exact: iff_refl. Qed.

Lemma x152_embeddable_in_fixed_surface_canonical (surface : nat) (G : sgraph) :
  x152_embeddable_in_fixed_surface surface G <-> surface_embeddable surface G.
Proof. exact: iff_refl. Qed.

(** The [boundary] argument of the X164 wrapper is ignored, for every value. *)
Lemma x164_embedded_in_fixed_surface_with_boundary_canonical (surface boundary : nat) (G : sgraph) :
  x164_embedded_in_fixed_surface_with_boundary surface boundary G <-> surface_embeddable surface G.
Proof. exact: iff_refl. Qed.

Lemma gimbel_thomassen_triangle_free_surface_three_colourability_polytime_statement_canonical :
  gimbel_thomassen_triangle_free_surface_three_colourability_polytime_statement <->
  forall surface : nat,
    polytime_decides_graph_on
      (fun G : sgraph => connected [set: G] /\ surface_embeddable surface G /\ girth_geq G 4)
      (fun G : sgraph => χ([set: G]) <= 3).
Proof. exact: iff_refl. Qed.

Lemma fixed_surface_four_colourability_polytime_statement_canonical :
  fixed_surface_four_colourability_polytime_statement <->
  forall surface : nat,
    0 < surface ->
    polytime_decides_graph_on
      (fun G : sgraph => connected [set: G] /\ surface_embeddable surface G)
      (fun G : sgraph => χ([set: G]) <= 4).
Proof. exact: iff_refl. Qed.

Lemma fixed_surface_four_colourability_polytime_duplicate_statement_canonical :
  fixed_surface_four_colourability_polytime_duplicate_statement <->
  forall surface : nat,
    0 < surface ->
    polytime_decides_graph_on
      (fun G : sgraph => connected [set: G] /\ surface_embeddable surface G)
      (fun G : sgraph => χ([set: G]) <= 4).
Proof. exact: iff_refl. Qed.

(** X164 keeps its instance constraint [#|x164_boundary I| <= boundary] and no connectedness guard; the output
    validity [x164_valid_output] is the live (natural-data-decoder) chain. *)
Lemma linear_time_surface_triangle_free_three_colouring_output_statement_canonical :
  linear_time_surface_triangle_free_three_colouring_output_statement <->
  forall surface boundary : nat,
    linear_time_outputs_on_class x164_enc_instance
      (fun I : x164_instance =>
         triangle_free (x164_graph I) /\ surface_embeddable surface (x164_graph I) /\
         #|x164_boundary I| <= boundary)
      x164_valid_output.
Proof. exact: iff_refl. Qed.

Print Assumptions x150_embeddable_in_fixed_surface_compat.
Print Assumptions x150_polytime_decides_3_colourability_on_surface_compat.
Print Assumptions gimbel_thomassen_triangle_free_surface_three_colourability_polytime_statement_compat.
Print Assumptions x152_embeddable_in_fixed_surface_compat.
Print Assumptions x152_polytime_decides_four_colourability_compat.
Print Assumptions fixed_surface_four_colourability_polytime_statement_compat.
Print Assumptions fixed_surface_four_colourability_polytime_duplicate_statement_compat.
Print Assumptions x164_embedded_in_fixed_surface_with_boundary_compat.
Print Assumptions x164_instance_class_compat.
Print Assumptions x164_linear_time_outputs_three_colouring_compat.
Print Assumptions linear_time_surface_triangle_free_three_colouring_output_statement_compat.
Print Assumptions x150_embeddable_in_fixed_surface_canonical.
Print Assumptions x152_embeddable_in_fixed_surface_canonical.
Print Assumptions x164_embedded_in_fixed_surface_with_boundary_canonical.
Print Assumptions gimbel_thomassen_triangle_free_surface_three_colourability_polytime_statement_canonical.
Print Assumptions fixed_surface_four_colourability_polytime_statement_canonical.
Print Assumptions fixed_surface_four_colourability_polytime_duplicate_statement_canonical.
Print Assumptions linear_time_surface_triangle_free_three_colouring_output_statement_canonical.

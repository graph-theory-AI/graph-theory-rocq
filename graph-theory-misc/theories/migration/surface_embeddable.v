(** * GTMisc.migration.surface_embeddable — surface-embeddable certificates: X167

    Family [surface-embeddable] (meta/library_primitives/surface-embeddable.json); the canonical contract is the
    existing public [GTBase.surface.surface_embeddable] (a rotation system whose encoded orientable-genus value
    [surface_euler_genus] is at most the bound; the unchanged formula can understate the genus of a disconnected
    graph), unchanged.  X167's wrapper [x167_embedded_in_fixed_surface] was already a direct alias of it
    when authored (8800958) and is unchanged at the baseline 3bdfdae; [Legacy] freezes it verbatim, [X167Legacy] the
    complete row with its connectedness guard, both kernel conversions.

    [X167Original] composes the end-to-end pre-migration row.  The earlier family B18 (spanning-tree, certificate
    [GTMisc.migration.spanning_trees], bound here as [Module B18]) froze X167's spanning-tree chain (the five-field
    Record, whose two linking fields conclude [True], and the existence wrapper) and kept the surface wrapper live;
    this family freezes the wrapper and keeps that chain live.  Over B18's frozen
    [B18.X167Legacy.x167_spanning_tree_polytope_xc] and the frozen wrapper here, [X167Original.statement] is the row
    with every migrated helper at its original body, certified through B18's own row certificate.  The row stays
    BLOCKED (KNOWN UNFAITHFUL: the extension system carries no polytope content); nothing here repairs it. *)

From GTBase Require Import base.
From GTMisc.conjectures Require Import X167.
Require GTMisc.migration.spanning_trees.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** B18's certificate, bound explicitly: its frozen spanning-tree chain is reused by the Original. *)
Module B18 := GTMisc.migration.spanning_trees.

Module Legacy.

Definition x167_embedded_in_fixed_surface (surface : nat) (G : sgraph) : Prop :=
  surface_embeddable surface G.

End Legacy.

Module X167Legacy.

Definition fixed_surface_spanning_tree_polytope_linear_xc_statement : Prop :=
  forall surface : nat,
    exists C : nat,
      forall G : sgraph,
        connected [set: G] ->
        Legacy.x167_embedded_in_fixed_surface surface G ->
        x167_spanning_tree_polytope_xc G (C * #|G|.+1).

End X167Legacy.

Module X167Original.

Definition statement : Prop :=
  forall surface : nat,
    exists C : nat,
      forall G : sgraph,
        connected [set: G] ->
        Legacy.x167_embedded_in_fixed_surface surface G ->
        B18.X167Legacy.x167_spanning_tree_polytope_xc G (C * #|G|.+1).

End X167Original.

(** ** Certificates *)

Lemma x167_embedded_in_fixed_surface_compat (surface : nat) (G : sgraph) :
  Legacy.x167_embedded_in_fixed_surface surface G <-> x167_embedded_in_fixed_surface surface G.
Proof. exact: iff_refl. Qed.

Lemma fixed_surface_spanning_tree_polytope_linear_xc_statement_compat :
  X167Legacy.fixed_surface_spanning_tree_polytope_linear_xc_statement <->
  fixed_surface_spanning_tree_polytope_linear_xc_statement.
Proof. exact: iff_refl. Qed.

(** B18's row certificate, whose frozen row applies the (unchanged) live wrapper, is the Original's by conversion. *)
Lemma fixed_surface_spanning_tree_polytope_linear_xc_statement_original_compat :
  X167Original.statement <-> fixed_surface_spanning_tree_polytope_linear_xc_statement.
Proof. exact: B18.fixed_surface_spanning_tree_polytope_linear_xc_statement_compat. Qed.

(** ** The wrapper and the complete current row in the canonical vocabulary *)

Lemma x167_embedded_in_fixed_surface_canonical (surface : nat) (G : sgraph) :
  x167_embedded_in_fixed_surface surface G <-> surface_embeddable surface G.
Proof. exact: iff_refl. Qed.

Lemma fixed_surface_spanning_tree_polytope_linear_xc_statement_canonical :
  fixed_surface_spanning_tree_polytope_linear_xc_statement <->
  forall surface : nat,
    exists C : nat,
      forall G : sgraph,
        connected [set: G] ->
        surface_embeddable surface G ->
        x167_spanning_tree_polytope_xc G (C * #|G|.+1).
Proof. exact: iff_refl. Qed.

Print Assumptions x167_embedded_in_fixed_surface_compat.
Print Assumptions fixed_surface_spanning_tree_polytope_linear_xc_statement_compat.
Print Assumptions fixed_surface_spanning_tree_polytope_linear_xc_statement_original_compat.
Print Assumptions x167_embedded_in_fixed_surface_canonical.
Print Assumptions fixed_surface_spanning_tree_polytope_linear_xc_statement_canonical.

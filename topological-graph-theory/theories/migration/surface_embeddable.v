(** * Topological.migration.surface_embeddable — surface-embeddable certificates: X138

    Family [surface-embeddable] (meta/library_primitives/surface-embeddable.json); the canonical contract is the
    existing public [GTBase.surface.surface_embeddable] (a rotation system whose encoded orientable-genus value
    [surface_euler_genus] is at most the bound; the unchanged formula can understate the genus of a disconnected
    graph), unchanged.  X138's wrapper [x138_embeddable_on_surface] was already a direct alias of it
    when authored (8800958) and is unchanged at the baseline 3bdfdae; [Legacy] freezes it verbatim, [X138Legacy] the
    complete row with its quantifier order ([exists c] before [forall G]) and guards (girth at least 4, maximum degree,
    connectedness), both kernel conversions.

    [X138Original] composes the end-to-end pre-migration row.  The earlier family C8 (monochromatic subsets,
    certificate [Topological.migration.monochromatic], bound here as [Module C8]) froze X138's clustered-colouring
    chain over its frozen base vocabulary and kept the surface wrapper live; this family freezes the wrapper and keeps
    that chain live.  Over C8's frozen [C8.X138Legacy.x138_clustered_two_colourable_with_clustering] and the frozen
    wrapper here, [X138Original.statement] is the row with every migrated helper at its original body, certified
    through C8's own row certificate.  The row stays partial (orientable surfaces only); nothing here changes it. *)

From GTBase Require Import base.
From Topological.conjectures Require Import X138.
Require Topological.migration.monochromatic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** C8's certificate, bound explicitly: its frozen clustered-colouring chain is reused by the Original. *)
Module C8 := Topological.migration.monochromatic.

Module Legacy.

Definition x138_embeddable_on_surface (surface : nat) (G : sgraph) : Prop :=
  surface_embeddable surface G.

End Legacy.

Module X138Legacy.

Definition esperet_joret_surface_triangle_free_clustered_two_colouring_statement : Prop :=
  forall surface Delta0 : nat,
    exists c : nat,
      forall G : sgraph,
        girth_geq G 4 ->
        Delta G <= Delta0 ->
        connected [set: G] ->
        Legacy.x138_embeddable_on_surface surface G ->
        x138_clustered_two_colourable_with_clustering c G.

End X138Legacy.

Module X138Original.

Definition statement : Prop :=
  forall surface Delta0 : nat,
    exists c : nat,
      forall G : sgraph,
        girth_geq G 4 ->
        Delta G <= Delta0 ->
        connected [set: G] ->
        Legacy.x138_embeddable_on_surface surface G ->
        C8.X138Legacy.x138_clustered_two_colourable_with_clustering c G.

End X138Original.

(** ** Certificates *)

Lemma x138_embeddable_on_surface_compat (surface : nat) (G : sgraph) :
  Legacy.x138_embeddable_on_surface surface G <-> x138_embeddable_on_surface surface G.
Proof. exact: iff_refl. Qed.

Lemma esperet_joret_surface_triangle_free_clustered_two_colouring_statement_compat :
  X138Legacy.esperet_joret_surface_triangle_free_clustered_two_colouring_statement <->
  esperet_joret_surface_triangle_free_clustered_two_colouring_statement.
Proof. exact: iff_refl. Qed.

(** C8's row certificate, whose frozen row applies the (unchanged) live wrapper, is the Original's by conversion. *)
Lemma esperet_joret_surface_triangle_free_clustered_two_colouring_statement_original_compat :
  X138Original.statement <-> esperet_joret_surface_triangle_free_clustered_two_colouring_statement.
Proof. exact: C8.esperet_joret_surface_triangle_free_clustered_two_colouring_statement_compat. Qed.

(** ** The wrapper and the complete current row in the canonical vocabulary *)

Lemma x138_embeddable_on_surface_canonical (surface : nat) (G : sgraph) :
  x138_embeddable_on_surface surface G <-> surface_embeddable surface G.
Proof. exact: iff_refl. Qed.

Lemma esperet_joret_surface_triangle_free_clustered_two_colouring_statement_canonical :
  esperet_joret_surface_triangle_free_clustered_two_colouring_statement <->
  forall surface Delta0 : nat,
    exists c : nat,
      forall G : sgraph,
        girth_geq G 4 ->
        Delta G <= Delta0 ->
        connected [set: G] ->
        surface_embeddable surface G ->
        x138_clustered_two_colourable_with_clustering c G.
Proof. exact: iff_refl. Qed.

Print Assumptions x138_embeddable_on_surface_compat.
Print Assumptions esperet_joret_surface_triangle_free_clustered_two_colouring_statement_compat.
Print Assumptions esperet_joret_surface_triangle_free_clustered_two_colouring_statement_original_compat.
Print Assumptions x138_embeddable_on_surface_canonical.
Print Assumptions esperet_joret_surface_triangle_free_clustered_two_colouring_statement_canonical.

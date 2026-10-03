(** * Frozen monochromatic subsets and complete reaching statements (C8)
    Original source: 47eed16, before C8. Every frozen body below preserves
    the original binders, guards and witnesses; only the recorded family
    references are redirected to other frozen bodies. Existing source
    discrepancies and partial/blocked statuses are not repaired. *)
From GTBase Require Import base monochromatic.
From GTBase.migration Require monochromatic.
From Topological.conjectures Require Import X138.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module BaseLegacy := GTBase.migration.monochromatic.Legacy.

Module X138Legacy.

Definition x138_clustered_two_colourable (G : sgraph) : Prop :=
  BaseLegacy.clustered_chromatic_at_most G 2.

Definition x138_clustered_two_colourable_with_clustering
    (c : nat) (G : sgraph) : Prop :=
  BaseLegacy.clustered_colouring G 2 c.

Definition esperet_joret_surface_triangle_free_clustered_two_colouring_statement : Prop :=
  forall surface Delta0 : nat,
    exists c : nat,
      forall G : sgraph,
        girth_geq G 4 ->
        Delta G <= Delta0 ->
        connected [set: G] ->
        x138_embeddable_on_surface surface G ->
        X138Legacy.x138_clustered_two_colourable_with_clustering c G.

End X138Legacy.

Lemma x138_clustered_two_colourable_compat (G : sgraph) :
  X138Legacy.x138_clustered_two_colourable G <-> x138_clustered_two_colourable G.
Proof. exact: GTBase.migration.monochromatic.clustered_chromatic_at_most_compat. Qed.

Lemma x138_clustered_two_colourable_with_clustering_compat c (G : sgraph) :
  X138Legacy.x138_clustered_two_colourable_with_clustering c G <->
  x138_clustered_two_colourable_with_clustering c G.
Proof. exact: GTBase.migration.monochromatic.clustered_colouring_compat. Qed.

Lemma esperet_joret_surface_triangle_free_clustered_two_colouring_statement_compat :
  X138Legacy.esperet_joret_surface_triangle_free_clustered_two_colouring_statement <->
  esperet_joret_surface_triangle_free_clustered_two_colouring_statement.
Proof.
split=> h surface Delta0; have [c hc] := h surface Delta0; exists c.
all: move=> G girth degree conn emb; have hg := hc G girth degree conn emb.
all: by apply/x138_clustered_two_colourable_with_clustering_compat.
Qed.

(** * Topological.migration.linear_forest -- frozen X23 linear-forest certificates

    Library migration D14, family "linear-forest"
    (meta/library_primitives/linear-forest.json).  [Legacy] freezes the X23 source
    [x23_linear_forest_colour] verbatim as it stood at the D14 baseline (A28P
    1123673d, byte-identical to the discovery pin e2a6bf47): the forest and
    maximum-degree conjunction over D12's LIVE colour class [x23_colour_graph].
    The live source now unfolds to [GTBase.path_trees.linear_forest
    (x23_colour_graph col i)], the same conjunction, so the source, chain and row
    certificates are kernel-checked conversions.

    [X23Legacy] freezes the attained-and-universal-minimum chain
    [x23_linear_arboricity_at_most] / [x23_linear_arboricity] over the frozen
    source and the row with the planar and [5 <= Delta G] guards and the
    [ceil_div (Delta G) 2] bound.  X23's complete row before D12 and D14 is D12's
    [X23Legacy] row in Topological.migration.edge_colour_class, borrowed with its
    certificate.  The regeneration spec is
    meta/migration_reports/linear_forest.spec.json. *)

From GTBase Require Import base.
From Topological.conjectures Require Import X23.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x23_linear_forest_colour
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) : Prop :=
  is_forest [set: x23_colour_graph col i] /\
  Delta (x23_colour_graph col i) <= 2.

End Legacy.

(** Kernel-checked conversion: [GTBase.path_trees.linear_forest] is the frozen
    conjunction, on the same colour class. *)
Lemma x23_linear_forest_colour_compat
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) :
  Legacy.x23_linear_forest_colour col i <-> x23_linear_forest_colour col i.
Proof. exact: iff_refl. Qed.

(** ** X23 *)

Module X23Legacy.

Definition linear_arboricity_at_most (G : sgraph) (q : nat) : Prop :=
  exists col : {set G} -> 'I_q, forall i : 'I_q, Legacy.x23_linear_forest_colour col i.

Definition linear_arboricity (G : sgraph) (q : nat) : Prop :=
  linear_arboricity_at_most G q /\
  forall q' : nat, linear_arboricity_at_most G q' -> q <= q'.

Definition planar_linear_arboricity_statement : Prop :=
  forall G : sgraph,
    wagner_planar G -> 5 <= Delta G -> linear_arboricity G (ceil_div (Delta G) 2).

End X23Legacy.

Lemma x23_linear_arboricity_at_most_compat (G : sgraph) (q : nat) :
  X23Legacy.linear_arboricity_at_most G q <-> x23_linear_arboricity_at_most G q.
Proof. exact: iff_refl. Qed.

Lemma x23_linear_arboricity_compat (G : sgraph) (q : nat) :
  X23Legacy.linear_arboricity G q <-> x23_linear_arboricity G q.
Proof. exact: iff_refl. Qed.

Lemma planar_linear_arboricity_statement_compat :
  X23Legacy.planar_linear_arboricity_statement <-> planar_linear_arboricity_statement.
Proof. exact: iff_refl. Qed.

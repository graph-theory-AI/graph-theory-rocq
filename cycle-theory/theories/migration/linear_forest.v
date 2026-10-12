(** * Cycle.migration.linear_forest -- frozen X212 linear-forest certificates

    Library migration D14, family "linear-forest"
    (meta/library_primitives/linear-forest.json).  [Legacy] freezes the X212 source
    [x212_linear_forest_colour] verbatim as it stood at the D14 baseline (A28P
    1123673d, byte-identical to the discovery pin e2a6bf47): the forest and
    maximum-degree conjunction over D12's LIVE colour class [x212_colour_graph].
    The live source now unfolds to [GTBase.path_trees.linear_forest
    (x212_colour_graph col i)], the same conjunction, so the source, chain and row
    certificates are kernel-checked conversions.

    [X212Legacy] freezes the attained-and-universal-minimum chain
    [x212_linear_arboricity_at_most] / [x212_linear_arboricity] over the frozen
    source and the row with the [0 < #|G|] and [regular G k] guards and the
    [ceil_div (k + 1) 2] bound.  The documented divergence is kept: no colouring
    into ['I_0] exists, so the encoded minimum is at least 1 and the edgeless k = 0
    instance holds.  [regular] here is GTBase.base.regular (simple-graph
    neighbourhood regularity).  X212's complete row before D12 and D14 is D12's
    [X212Legacy] row in Cycle.migration.edge_colour_class, borrowed with its
    certificate.  The regeneration spec is
    meta/migration_reports/linear_forest.spec.json. *)

From GTBase Require Import base.
From Cycle.conjectures Require Import X212.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x212_linear_forest_colour
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) : Prop :=
  is_forest [set: x212_colour_graph col i] /\
  Delta (x212_colour_graph col i) <= 2.

End Legacy.

(** Kernel-checked conversion: [GTBase.path_trees.linear_forest] is the frozen
    conjunction, on the same colour class. *)
Lemma x212_linear_forest_colour_compat
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) :
  Legacy.x212_linear_forest_colour col i <-> x212_linear_forest_colour col i.
Proof. exact: iff_refl. Qed.

(** ** X212 *)

Module X212Legacy.

Definition linear_arboricity_at_most (G : sgraph) (q : nat) : Prop :=
  exists col : {set G} -> 'I_q, forall i : 'I_q, Legacy.x212_linear_forest_colour col i.

Definition linear_arboricity (G : sgraph) (q : nat) : Prop :=
  linear_arboricity_at_most G q /\
  forall q' : nat, linear_arboricity_at_most G q' -> q <= q'.

Definition linear_arboricity_regular_statement : Prop :=
  forall (k : nat) (G : sgraph),
    0 < #|G| -> regular G k -> linear_arboricity G (ceil_div (k + 1) 2).

End X212Legacy.

Lemma x212_linear_arboricity_at_most_compat (G : sgraph) (q : nat) :
  X212Legacy.linear_arboricity_at_most G q <-> x212_linear_arboricity_at_most G q.
Proof. exact: iff_refl. Qed.

Lemma x212_linear_arboricity_compat (G : sgraph) (q : nat) :
  X212Legacy.linear_arboricity G q <-> x212_linear_arboricity G q.
Proof. exact: iff_refl. Qed.

Lemma linear_arboricity_regular_statement_compat :
  X212Legacy.linear_arboricity_regular_statement <-> linear_arboricity_regular_statement.
Proof. exact: iff_refl. Qed.

(** * Chromatic.migration.linear_forest -- frozen X34 linear-forest certificates

    Library migration D14, family "linear-forest"
    (meta/library_primitives/linear-forest.json).  [Legacy] freezes the X34 source
    [x34_linear_forest_colour] verbatim as it stood at the D14 baseline (A28P
    1123673d, byte-identical to the discovery pin e2a6bf47): the forest and
    maximum-degree conjunction over D12's LIVE colour class [x34_colour_graph].
    The live source now unfolds to [GTBase.path_trees.linear_forest
    (x34_colour_graph col i)], the same conjunction, so the source, chain and row
    certificates are kernel-checked conversions.

    [X34Legacy] freezes the chain [x34_linear_forests_and_matching] over the frozen
    source, with the live matching clause, and the row with its exact [let q], the
    same colouring for the widened linear-forest colours and the [ord_max] matching,
    and the full planar / odd / [9 <= Delta G] guards (the documented 9-vs-7 defect
    is kept).  The complete row before M1, D12 and D14 is D12's [X34Original] in
    Chromatic.migration.edge_colour_class, borrowed with its certificate.  The
    regeneration spec is meta/migration_reports/linear_forest.spec.json. *)

From GTBase Require Import base.
From Chromatic.conjectures Require Import X34.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x34_linear_forest_colour
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) : Prop :=
  is_forest [set: x34_colour_graph col i] /\
  Delta (x34_colour_graph col i) <= 2.

End Legacy.

(** Kernel-checked conversion: [GTBase.path_trees.linear_forest] is the frozen
    conjunction, on the same colour class. *)
Lemma x34_linear_forest_colour_compat
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) :
  Legacy.x34_linear_forest_colour col i <-> x34_linear_forest_colour col i.
Proof. exact: iff_refl. Qed.

(** ** X34 *)

Module X34Legacy.

Definition linear_forests_and_matching
    (G : sgraph) (q : nat) (col : {set G} -> 'I_(q.+1)) : Prop :=
  (forall i : 'I_q,
      Legacy.x34_linear_forest_colour col (widen_ord (leqnSn q) i)) /\
  x34_matching_colour col ord_max.

Definition planar_odd_degree_linear_forests_plus_matching_statement : Prop :=
  forall G : sgraph,
    wagner_planar G ->
    odd (Delta G) ->
    9 <= Delta G ->
    let q := (Delta G - 1) %/ 2 in
    exists col : {set G} -> 'I_(q.+1),
      linear_forests_and_matching col.

End X34Legacy.

Lemma x34_linear_forests_and_matching_compat
    (G : sgraph) (q : nat) (col : {set G} -> 'I_(q.+1)) :
  X34Legacy.linear_forests_and_matching col <-> x34_linear_forests_and_matching col.
Proof. exact: iff_refl. Qed.

Lemma planar_odd_degree_linear_forests_plus_matching_statement_compat :
  X34Legacy.planar_odd_degree_linear_forests_plus_matching_statement <->
  planar_odd_degree_linear_forests_plus_matching_statement.
Proof. exact: iff_refl. Qed.

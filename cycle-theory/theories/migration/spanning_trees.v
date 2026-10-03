(** * Cycle.migration.spanning_trees — frozen multigraph spanning-tree helper and row of U6
    (library migration B19)

    Multigraph contract of family [spanning-tree] (meta/library_primitives/spanning-tree.json,
    semantic class multigraph-edge-carrier; registry override 2026-10-03: the same family as B18's
    labelled contract, following the B17 degree-balance pattern, with a distinct Cycle canonical).
    [Legacy] freezes, verbatim as they stood at the recorded prerequisite union d2a23f1 (fixed B18
    51f1200 with reviewed A13 004cf63), U6's [spanning_tree] ([spanning_connected T /\ acyclic T]) together
    with copies of its two unchanged supports [spanning_connected] (an undirected walk inside [T]
    between every two HOST vertices) and [acyclic] (no circuit inside [T]), so that the frozen
    contract is fully independent; the live supports are not rewritten and are not sources of this
    family.  The live helper now unfolds to the public [Cycle.foundations.spanning_trees.spanning_tree_edge_set]
    (the same conjunction over [spanning_connected_edge_set] and the public [acyclic_edge_set]), so the
    helper certificate is a conversion.  No equivalence with B18's labelled [GTBase.spanning_trees.fg_spanning_tree]
    is stated: the supplied carriers differ.

    [U6Legacy] freezes the complete row [three_decomposition_statement] (opg:3_decomposition_conjecture:
    positive vertex count, guarded cubicity, all-vertex connectivity, then T/F/M in order with F's
    2-regularity, M's matching bound and the exact edge partition) over the frozen tree and the live
    [cubic] alias of A13.  [U6Original] composes the complete pre-A13, pre-B19 row over A13's frozen
    [Legacy.cubic] (certificate [Cycle.migration.mregular], bound here as [Module A13]; its own per-row
    snapshot of this row keeps the live tree and stays byte-exact) and the frozen tree, certified end to end
    through [A13.cubic_compat].  No guard, order, status or doc block changes.  Hashes and substitutions:
    meta/migration_reports/spanning_trees.md. *)

From GraphTheory Require Import mgraph.
From GTBase Require Import base.
From Cycle.foundations Require Import connectivity path_subgraphs spanning_trees.
From Cycle.migration Require mregular.
From Cycle.conjectures Require Import U6.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A13's certificate, bound explicitly: its frozen cubic body is reused by the Original. *)
Module A13 := Cycle.migration.mregular.

Module Legacy.

Definition acyclic (G : mgraph) (H : {set edge G}) : Prop :=
  forall C : {set edge G}, C \subset H -> ~ is_circuit C.

Definition spanning_connected (G : mgraph) (T : {set edge G}) : Prop :=
  forall x y : G, exists w, uwalk x y w /\ all (fun e => e \in T) w.

Definition spanning_tree (G : mgraph) (T : {set edge G}) : Prop :=
  Legacy.spanning_connected T /\ Legacy.acyclic T.

End Legacy.

Module U6Legacy.

Definition three_decomposition_statement : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> cubic G -> mconnected G ->
    exists T F M : {set edge G},
      [/\ Legacy.spanning_tree T, subgraph_kregular F 2, is_matching M
        & edge_partitionT [:: T; F; M]].

End U6Legacy.

Module U6Original.

Definition three_decomposition_statement : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> A13.Legacy.cubic G -> mconnected G ->
    exists T F M : {set edge G},
      [/\ Legacy.spanning_tree T, subgraph_kregular F 2, is_matching M
        & edge_partitionT [:: T; F; M]].

End U6Original.

(** ** Certificates *)

(** The two unchanged supports: their copies are their live bodies, by conversion. *)
Lemma acyclic_compat (G : mgraph) (H : {set edge G}) :
  Legacy.acyclic H <-> Cycle.conjectures.U6.acyclic H.
Proof. exact: iff_refl. Qed.

Lemma spanning_connected_compat (G : mgraph) (T : {set edge G}) :
  Legacy.spanning_connected T <-> Cycle.conjectures.U6.spanning_connected T.
Proof. exact: iff_refl. Qed.

(** The helper: the conjunction of the public [spanning_connected_edge_set] and [acyclic_edge_set],
    by conversion (each frozen support unfolds to the same body as its public counterpart). *)
Lemma spanning_tree_compat (G : mgraph) (T : {set edge G}) :
  Legacy.spanning_tree T <-> Cycle.conjectures.U6.spanning_tree T.
Proof. exact: iff_refl. Qed.

(** opg:3_decomposition_conjecture (unchanged): the per-row copy over the frozen tree and the live
    cubic alias. *)
Lemma three_decomposition_statement_compat :
  U6Legacy.three_decomposition_statement <-> three_decomposition_statement.
Proof. exact: iff_refl. Qed.

(** The complete pre-A13, pre-B19 row, end to end: A13's frozen arc-end cubic through its own
    certificate [A13.cubic_compat] (not a conversion), the tree by conversion. *)
Lemma three_decomposition_statement_original_compat :
  U6Original.three_decomposition_statement <-> three_decomposition_statement.
Proof.
by split=> h G n0 /A13.cubic_compat cG conn; exact: h G n0 cG conn.
Qed.

Print Assumptions acyclic_compat.
Print Assumptions spanning_connected_compat.
Print Assumptions spanning_tree_compat.
Print Assumptions three_decomposition_statement_compat.
Print Assumptions three_decomposition_statement_original_compat.

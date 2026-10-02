(** * GTMisc.migration.induced_free -- frozen induced-free certificates

    Batch A, family [induced_free].  [Legacy] freezes the two conjecture-local
    helpers verbatim as they stood at 9e03072, before the migration; X41's
    helper keeps its argument order [H G].  [X41Legacy] and [X102Legacy] freeze
    the affected dependency chains, the statements included, with every
    reference to a helper of this family replaced by its frozen copy (X102
    through [x102_free_class_tree_alpha_bounded]).  The live helpers now unfold
    to [GTBase.common.induced_free]; the theorems below prove each frozen body
    equivalent to its live counterpart.

    M1 snapshot limitation.  [simple_edges.X102Legacy.statement] froze only the
    edge-set chain and still resolves through the live
    [x102_free_class_tree_alpha_bounded], so after this migration its body uses
    the canonical [induced_free]: it is no longer the pre-M1 statement.
    [X102Original] restores a fully frozen statement from M1's frozen edge-set
    chain ([simple_edges.X102Legacy.line_graph_of_subdivided_multiclaw], over
    [simple_edges.Legacy.clique_edge_set]) and this file's frozen induced-free
    chain; [x102_statement_original_compat] relates it to the live statement.
    Source hashes and the per-row theorem names are recorded in
    meta/migration_reports/induced_free.md. *)

From GTBase Require Import base.
From GTMisc.conjectures Require Import X41 X102.
From GTMisc.migration Require simple_edges.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x41_induced_H_free (H G : sgraph) : Prop :=
  forall S : {set G}, ~ inhabited (induced S ≃ H).

Definition x102_induced_free (G H : sgraph) : Prop :=
  forall S : {set G}, ~ inhabited (induced S ≃ H).

End Legacy.

Lemma x41_induced_H_free_compat (H G : sgraph) :
  Legacy.x41_induced_H_free H G <-> x41_induced_H_free H G.
Proof. exact: iff_sym (induced_free_inhabited G H). Qed.

(** The alias keeps the historical argument order: pattern first, host second. *)
Lemma x41_induced_H_free_order (H G : sgraph) :
  x41_induced_H_free H G = induced_free G H.
Proof. by []. Qed.

Lemma x102_induced_free_compat (G H : sgraph) :
  Legacy.x102_induced_free G H <-> x102_induced_free G H.
Proof. exact: iff_sym (induced_free_inhabited G H). Qed.

(** ** X41 *)

Module X41Legacy.

Definition statement : Prop :=
  forall H : sgraph, exists eps_num eps_den : nat,
    0 < eps_num /\
    eps_num <= eps_den /\
    forall G : sgraph,
      1 < #|G| ->
      Legacy.x41_induced_H_free H G ->
      exists A B : {set G},
        x41_pure_pair A B /\
        eps_den ^ eps_den * #|A| ^ eps_den >= eps_num ^ eps_den * #|G| ^ eps_num /\
        eps_den * #|B| >= eps_num * #|G|.

End X41Legacy.

Lemma x41_statement_compat :
  X41Legacy.statement <-> sparse_linear_pure_pair_statement.
Proof.
split=> statement H; have [n [d [n0 [nd bound]]]] := statement H;
  exists n, d; do 2!split=> //; move=> G G1 free.
- by apply: bound G1 _; apply/x41_induced_H_free_compat.
- by apply: bound G1 _; apply/x41_induced_H_free_compat.
Qed.

(** ** X102 *)

Module X102Legacy.

Definition free_class_tree_alpha_bounded
    (I : finType) (F : I -> sgraph) : Prop :=
  exists a : nat,
    forall G : sgraph,
      (forall i : I, Legacy.x102_induced_free G (F i)) ->
      x102_tree_alpha_at_most G a.

Definition statement : Prop :=
  forall (I : finType) (F : I -> sgraph),
    free_class_tree_alpha_bounded F <->
    exists i1 i2 i3 : I,
      x102_complete_bipartite_graph (F i1) /\
      x102_subdivided_multiclaw (F i2) /\
      x102_line_graph_of_subdivided_multiclaw (F i3).

End X102Legacy.

Lemma x102_free_class_tree_alpha_bounded_compat (I : finType) (F : I -> sgraph) :
  X102Legacy.free_class_tree_alpha_bounded F <-> x102_free_class_tree_alpha_bounded F.
Proof.
split=> -[a bound]; exists a => G free; apply: bound => i.
- exact/x102_induced_free_compat.
- exact/x102_induced_free_compat.
Qed.

Lemma x102_statement_compat :
  X102Legacy.statement <-> bounded_tree_independence_forbidden_family_statement.
Proof.
split=> statement I F.
- exact: iff_trans (iff_sym (x102_free_class_tree_alpha_bounded_compat F)) (statement I F).
- exact: iff_trans (x102_free_class_tree_alpha_bounded_compat F) (statement I F).
Qed.

Module X102Original.

Definition statement : Prop :=
  forall (I : finType) (F : I -> sgraph),
    X102Legacy.free_class_tree_alpha_bounded F <->
    exists i1 i2 i3 : I,
      x102_complete_bipartite_graph (F i1) /\
      x102_subdivided_multiclaw (F i2) /\
      simple_edges.X102Legacy.line_graph_of_subdivided_multiclaw (F i3).

End X102Original.

Lemma x102_statement_original_compat :
  X102Original.statement <-> bounded_tree_independence_forbidden_family_statement.
Proof.
split=> statement I F.
- apply: iff_trans (iff_sym (x102_free_class_tree_alpha_bounded_compat F)) _.
  exact: iff_trans (statement I F) (simple_edges.x102_statement_rhs_compat F).
- apply: iff_trans (x102_free_class_tree_alpha_bounded_compat F) _.
  exact: iff_trans (statement I F) (iff_sym (simple_edges.x102_statement_rhs_compat F)).
Qed.

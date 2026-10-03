(** * Digraph.migration.internal_vertices — internal-vertex certificates for X2, X52, X90 (B2)

    Batch B, family [internal-vertices] (meta/library_primitives/internal-vertices.json).
    The live helper [x2_path_internal] now unfolds to
    [GTBase.walks_paths.seq_interior (branch u) (branch v) (branch u :: s)], keeping
    its head-plus-tail representation.

    Family B1 already froze, at 9e03072, the whole chain from [x2_path_vertices]
    upwards in [Digraph.migration.path_vertices]: [Legacy.x2_path_vertices],
    [X2Legacy.path_internal] (this family's helper), [contains_subdivision], the Mader
    bounds, the three X2 statements and the cross-module X52 and X90 rows.  Those
    snapshots therefore freeze this family's helper too.  This module does not copy
    them again: it is this family's entry point, stating its certificates over B1's
    frozen bodies.  Every live definition is convertible to its frozen copy
    ([seq_interior x y s] is [seq_vertices s :\: [set x; y]] and [seq_vertices s] is
    [[set:: s]]), so the certificates are kernel-checked conversions.  Source hashes,
    the exact substitutions and the per-row theorem names are recorded in
    meta/migration_reports/internal_vertices.md. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude interop_graph_theory digraph oriented dipath tournament.
From Digraph Require Import automorphism domination strong.
From Digraph Require Import classic_core heroes chi_bounded dichromatic.
From GTBase Require Import walks_paths.
From Digraph.conjectures Require Import X2 X52 X90.
From Digraph.migration Require path_vertices.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Helper certificate *)

Lemma x2_path_internal_compat
    (F D : diGraphType) (branch : F -> D) (u v : F) (s : seq D) :
  Digraph.migration.path_vertices.X2Legacy.path_internal branch u v s =
  x2_path_internal branch u v s.
Proof. by rewrite /x2_path_internal /seq_interior seq_verticesE. Qed.

(** ** Row certificates over the frozen B1 bodies *)

Lemma mader_delta0_transitive_tournament_statement_compat :
  Digraph.migration.path_vertices.X2MaderDelta0Legacy.statement <->
  mader_delta0_transitive_tournament_statement.
Proof. exact: iff_refl. Qed.

Lemma oriented_trees_delta_plus_maderian_statement_compat :
  Digraph.migration.path_vertices.X2TreesLegacy.statement <->
  oriented_trees_delta_plus_maderian_statement.
Proof. exact: iff_refl. Qed.

Lemma delta_plus_maderian_disjoint_union_statement_compat :
  Digraph.migration.path_vertices.X2UnionLegacy.statement <->
  delta_plus_maderian_disjoint_union_statement.
Proof. exact: iff_refl. Qed.

Lemma oriented_tree_mader_chi_linear_bound_statement_compat :
  Digraph.migration.path_vertices.X52Legacy.statement <->
  oriented_tree_mader_chi_linear_bound_statement.
Proof. exact: iff_refl. Qed.

Lemma f_subdivision_complexity_dichotomy_statement_compat :
  Digraph.migration.path_vertices.X90Legacy.statement <->
  f_subdivision_complexity_dichotomy_statement.
Proof. exact: iff_refl. Qed.

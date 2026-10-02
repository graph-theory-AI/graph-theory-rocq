(** * Digraph.migration.path_vertices — frozen path-vertex chains (library migration B1)

    Batch B family [path-vertices] (meta/library_primitives.json): the local
    helper [x2_path_vertices x s], the vertex set of the head-plus-tail
    sequence [x :: s], now unfolds to [GTBase.walks_paths.seq_vertices (x :: s)];
    the head-plus-tail signature is unchanged.

    [X2Legacy] holds verbatim copies, taken at base commit 9e03072, of every
    definition on the affected dependency chain of the X2 rows: the helper,
    [x2_path_internal] (copied inside the same section scaffolding, so its
    section arguments are unchanged), [contains_subdivision] and the Mader
    bounds that reach it, and the three X2 statements.  Rows X52 and X90 reach
    the helper through [contains_subdivision], so [X52Legacy] and [X90Legacy]
    import [X2Legacy] and copy their own affected definitions.  Inside a
    module the copies shadow the live names, so no frozen statement resolves
    through the migrated helper; definitions that do not reach it
    ([x2_branch_set], the degree conditions, [oriented_tree],
    [x2_disjoint_union], the X90 complexity notions) are the live, unchanged
    ones.

    [seq_vertices (x :: s)] is MathComp's [[set:: x :: s]], which unfolds to
    the frozen comprehension [[set y | y \in x :: s]]; so every live
    definition is convertible to its frozen copy and the certificates below
    are kernel-checked conversions ([x2_path_vertices_compat] goes through
    [seq_verticesE]).  Source hashes, the per-row theorem table and the
    [Print All Dependencies] check of the frozen closures:
    meta/migration_reports/path_vertices.md. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude interop_graph_theory digraph oriented dipath tournament.
From Digraph Require Import automorphism domination strong.
From Digraph Require Import classic_core heroes chi_bounded dichromatic.
From GTBase Require Import walks_paths.
From Digraph.conjectures Require Import X2 X52 X90.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module X2Legacy.

Section SubdivisionModel.
Variables (F D : diGraphType) (branch : F -> D).

Definition x2_path_vertices (x : D) (s : seq D) : {set D} :=
  [set y | y \in x :: s].

Definition x2_path_internal (u v : F) (s : seq D) : {set D} :=
  x2_path_vertices (branch u) s :\: [set branch u; branch v].

End SubdivisionModel.

Definition contains_subdivision (F D : diGraphType) : Prop :=
  exists branch : F -> D,
    injective branch /\
    exists paths : F -> F -> seq D,
      (forall u v : F, u --> v ->
        [/\ (0 < size (paths u v))%N,
            dipath (branch u) (paths u v),
            last (branch u) (paths u v) = branch v
          & [disjoint x2_path_internal branch u v (paths u v)
             & x2_branch_set branch]]) /\
      (forall u v x y : F, u --> v -> x --> y ->
        ((u != x) || (v != y)) ->
        [disjoint x2_path_internal branch u v (paths u v)
         & x2_path_internal branch x y (paths x y)]).

Definition mader_delta_plus_bound (F : diGraphType) (m : nat) : Prop :=
  forall D : diGraphType, (0 < #|D|)%N ->
    min_outdegree_at_least D m -> contains_subdivision F D.

Definition mader_delta_zero_bound (F : diGraphType) (m : nat) : Prop :=
  forall D : diGraphType, (0 < #|D|)%N ->
    min_semidegree_at_least D m -> contains_subdivision F D.

Definition delta_plus_maderian (F : diGraphType) : Prop :=
  exists m : nat, mader_delta_plus_bound F m.

Definition least_mader_delta_zero (F : diGraphType) (m : nat) : Prop :=
  mader_delta_zero_bound F m /\
  forall c : nat, mader_delta_zero_bound F c -> (m <= c)%N.

Definition mader_delta0_transitive_tournament_statement : Prop :=
  forall k : nat, exists m : nat, least_mader_delta_zero (TT k) m.

Definition oriented_trees_delta_plus_maderian_statement : Prop :=
  forall F : orientedDigraph, oriented_tree F -> delta_plus_maderian F.

Definition delta_plus_maderian_disjoint_union_statement : Prop :=
  forall F1 F2 : diGraphType,
    delta_plus_maderian F1 -> delta_plus_maderian F2 ->
    delta_plus_maderian (x2_disjoint_union F1 F2).

End X2Legacy.

Module X52Legacy.
Import X2Legacy.

Definition x52_mader_chi_bound (F : diGraphType) (m : nat) : Prop :=
  forall D : diGraphType, (0 < #|D|)%N ->
    (m <= χ([set: chi_bounded.underlying D]))%N ->
    contains_subdivision F D.

Definition oriented_tree_mader_chi_linear_bound_statement : Prop :=
  forall (T : orientedDigraph) (k : nat),
    oriented_tree T ->
    #|T| = k ->
    x52_mader_chi_bound T (2 * k - 2).

End X52Legacy.

Module X90Legacy.
Import X2Legacy.

Definition x90_f_subdivision_problem (F : diGraphType) : x90_problem :=
  fun D : diGraphType => contains_subdivision F D.

Definition f_subdivision_complexity_dichotomy_statement : Prop :=
  forall F : diGraphType,
    x90_polynomial_time_decidable (x90_f_subdivision_problem F) \/
    x90_np_complete (x90_f_subdivision_problem F).

End X90Legacy.

(** ** Certificates: X2 *)

Lemma x2_path_vertices_compat (D : diGraphType) (x : D) (s : seq D) :
  X2Legacy.x2_path_vertices x s = x2_path_vertices x s.
Proof. by rewrite /x2_path_vertices seq_verticesE. Qed.

Lemma x2_path_internal_compat
    (F D : diGraphType) (branch : F -> D) (u v : F) (s : seq D) :
  X2Legacy.x2_path_internal branch u v s = x2_path_internal branch u v s.
Proof.
by rewrite /X2Legacy.x2_path_internal /x2_path_internal x2_path_vertices_compat.
Qed.

Lemma contains_subdivision_compat (F D : diGraphType) :
  X2Legacy.contains_subdivision F D <-> contains_subdivision F D.
Proof. exact: iff_refl. Qed.

Lemma mader_delta_plus_bound_compat (F : diGraphType) (m : nat) :
  X2Legacy.mader_delta_plus_bound F m <-> mader_delta_plus_bound F m.
Proof. exact: iff_refl. Qed.

Lemma mader_delta_zero_bound_compat (F : diGraphType) (m : nat) :
  X2Legacy.mader_delta_zero_bound F m <-> mader_delta_zero_bound F m.
Proof. exact: iff_refl. Qed.

Lemma delta_plus_maderian_compat (F : diGraphType) :
  X2Legacy.delta_plus_maderian F <-> delta_plus_maderian F.
Proof. exact: iff_refl. Qed.

Lemma least_mader_delta_zero_compat (F : diGraphType) (m : nat) :
  X2Legacy.least_mader_delta_zero F m <-> least_mader_delta_zero F m.
Proof. exact: iff_refl. Qed.

Lemma mader_delta0_transitive_tournament_statement_compat :
  X2Legacy.mader_delta0_transitive_tournament_statement <->
  mader_delta0_transitive_tournament_statement.
Proof. exact: iff_refl. Qed.

Lemma oriented_trees_delta_plus_maderian_statement_compat :
  X2Legacy.oriented_trees_delta_plus_maderian_statement <->
  oriented_trees_delta_plus_maderian_statement.
Proof. exact: iff_refl. Qed.

Lemma delta_plus_maderian_disjoint_union_statement_compat :
  X2Legacy.delta_plus_maderian_disjoint_union_statement <->
  delta_plus_maderian_disjoint_union_statement.
Proof. exact: iff_refl. Qed.

(** ** Certificates: X52 (through [contains_subdivision]) *)

Lemma x52_mader_chi_bound_compat (F : diGraphType) (m : nat) :
  X52Legacy.x52_mader_chi_bound F m <-> x52_mader_chi_bound F m.
Proof. exact: iff_refl. Qed.

Lemma oriented_tree_mader_chi_linear_bound_statement_compat :
  X52Legacy.oriented_tree_mader_chi_linear_bound_statement <->
  oriented_tree_mader_chi_linear_bound_statement.
Proof. exact: iff_refl. Qed.

(** ** Certificates: X90 (through [contains_subdivision]) *)

Lemma x90_f_subdivision_problem_compat (F D : diGraphType) :
  X90Legacy.x90_f_subdivision_problem F D <-> x90_f_subdivision_problem F D.
Proof. exact: iff_refl. Qed.

Lemma f_subdivision_complexity_dichotomy_statement_compat :
  X90Legacy.f_subdivision_complexity_dichotomy_statement <->
  f_subdivision_complexity_dichotomy_statement.
Proof. exact: iff_refl. Qed.

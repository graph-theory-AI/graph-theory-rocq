(** * Digraph.migration.path_vertices — frozen path-vertex chains (library migration B1)

    Batch B, family [path-vertices] (meta/library_primitives.json).  [Legacy]
    freezes the conjecture-local helper [x2_path_vertices x s], the vertex set of
    the head-plus-tail sequence [x :: s], verbatim as it stood at 9e03072, inside a
    copy of its section scaffolding; the live helper now unfolds to
    [GTBase.walks_paths.seq_vertices (x :: s)] and keeps its signature.

    The affected chain of the X2 rows is frozen in dependency order, every
    reference to a frozen declaration being renamed or module-qualified so that no
    frozen body resolves through a live helper of this family: [X2Legacy] holds
    [path_internal] (from [x2_path_internal], in the same section scaffolding) and
    [contains_subdivision]; [X2BoundsLegacy] the two Mader bounds;
    [X2MaderianLegacy] [delta_plus_maderian] and [least_mader_delta_zero]; and
    [X2MaderDelta0Legacy], [X2TreesLegacy], [X2UnionLegacy] one statement each.
    Rows X52 and X90 reach the helper through [contains_subdivision], so
    [X52Legacy] and [X90Legacy] refer to [X2Legacy.contains_subdivision].
    Definitions that do not reach the helper ([x2_branch_set], the degree
    conditions, [oriented_tree], [x2_disjoint_union], the X90 complexity notions)
    are the live, unchanged ones.

    [seq_vertices (x :: s)] is MathComp's [[set:: x :: s]], which unfolds to the
    frozen comprehension [[set y | y \in x :: s]], so every live definition is
    convertible to its frozen copy: the certificates below are kernel-checked
    conversions, the helper certificate going through [seq_verticesE].  Source
    hashes, the exact substitutions and the per-row theorem names are recorded in
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

Module Legacy.

Section SubdivisionModel.
Variables (F D : diGraphType) (branch : F -> D).

Definition x2_path_vertices (x : D) (s : seq D) : {set D} :=
  [set y | y \in x :: s].

End SubdivisionModel.

End Legacy.

Module X2Legacy.

Section SubdivisionModel.
Variables (F D : diGraphType) (branch : F -> D).

Definition path_internal (u v : F) (s : seq D) : {set D} :=
  Legacy.x2_path_vertices (branch u) s :\: [set branch u; branch v].

End SubdivisionModel.

Definition contains_subdivision (F D : diGraphType) : Prop :=
  exists branch : F -> D,
    injective branch /\
    exists paths : F -> F -> seq D,
      (forall u v : F, u --> v ->
        [/\ (0 < size (paths u v))%N,
            dipath (branch u) (paths u v),
            last (branch u) (paths u v) = branch v
          & [disjoint path_internal branch u v (paths u v)
             & x2_branch_set branch]]) /\
      (forall u v x y : F, u --> v -> x --> y ->
        ((u != x) || (v != y)) ->
        [disjoint path_internal branch u v (paths u v)
         & path_internal branch x y (paths x y)]).

End X2Legacy.

Module X2BoundsLegacy.

Definition mader_delta_plus_bound (F : diGraphType) (m : nat) : Prop :=
  forall D : diGraphType, (0 < #|D|)%N ->
    min_outdegree_at_least D m -> X2Legacy.contains_subdivision F D.

Definition mader_delta_zero_bound (F : diGraphType) (m : nat) : Prop :=
  forall D : diGraphType, (0 < #|D|)%N ->
    min_semidegree_at_least D m -> X2Legacy.contains_subdivision F D.

End X2BoundsLegacy.

Module X2MaderianLegacy.

Definition delta_plus_maderian (F : diGraphType) : Prop :=
  exists m : nat, X2BoundsLegacy.mader_delta_plus_bound F m.

Definition least_mader_delta_zero (F : diGraphType) (m : nat) : Prop :=
  X2BoundsLegacy.mader_delta_zero_bound F m /\
  forall c : nat, X2BoundsLegacy.mader_delta_zero_bound F c -> (m <= c)%N.

End X2MaderianLegacy.

Module X2MaderDelta0Legacy.

Definition statement : Prop :=
  forall k : nat, exists m : nat, X2MaderianLegacy.least_mader_delta_zero (TT k) m.

End X2MaderDelta0Legacy.

Module X2TreesLegacy.

Definition statement : Prop :=
  forall F : orientedDigraph, oriented_tree F -> X2MaderianLegacy.delta_plus_maderian F.

End X2TreesLegacy.

Module X2UnionLegacy.

Definition statement : Prop :=
  forall F1 F2 : diGraphType,
    X2MaderianLegacy.delta_plus_maderian F1 -> X2MaderianLegacy.delta_plus_maderian F2 ->
    X2MaderianLegacy.delta_plus_maderian (x2_disjoint_union F1 F2).

End X2UnionLegacy.

Module X52Legacy.

Definition mader_chi_bound (F : diGraphType) (m : nat) : Prop :=
  forall D : diGraphType, (0 < #|D|)%N ->
    (m <= χ([set: chi_bounded.underlying D]))%N ->
    X2Legacy.contains_subdivision F D.

Definition statement : Prop :=
  forall (T : orientedDigraph) (k : nat),
    oriented_tree T ->
    #|T| = k ->
    mader_chi_bound T (2 * k - 2).

End X52Legacy.

Module X90Legacy.

Definition f_subdivision_problem (F : diGraphType) : x90_problem :=
  fun D : diGraphType => X2Legacy.contains_subdivision F D.

Definition statement : Prop :=
  forall F : diGraphType,
    x90_polynomial_time_decidable (f_subdivision_problem F) \/
    x90_np_complete (f_subdivision_problem F).

End X90Legacy.

(** ** Certificates: X2 *)

Lemma x2_path_vertices_compat (D : diGraphType) (x : D) (s : seq D) :
  Legacy.x2_path_vertices x s = x2_path_vertices x s.
Proof. by rewrite /x2_path_vertices seq_verticesE. Qed.

Lemma x2_path_internal_compat
    (F D : diGraphType) (branch : F -> D) (u v : F) (s : seq D) :
  X2Legacy.path_internal branch u v s = x2_path_internal branch u v s.
Proof. by rewrite /X2Legacy.path_internal /x2_path_internal x2_path_vertices_compat. Qed.

Lemma contains_subdivision_compat (F D : diGraphType) :
  X2Legacy.contains_subdivision F D <-> contains_subdivision F D.
Proof. exact: iff_refl. Qed.

Lemma mader_delta_plus_bound_compat (F : diGraphType) (m : nat) :
  X2BoundsLegacy.mader_delta_plus_bound F m <-> mader_delta_plus_bound F m.
Proof. exact: iff_refl. Qed.

Lemma mader_delta_zero_bound_compat (F : diGraphType) (m : nat) :
  X2BoundsLegacy.mader_delta_zero_bound F m <-> mader_delta_zero_bound F m.
Proof. exact: iff_refl. Qed.

Lemma delta_plus_maderian_compat (F : diGraphType) :
  X2MaderianLegacy.delta_plus_maderian F <-> delta_plus_maderian F.
Proof. exact: iff_refl. Qed.

Lemma least_mader_delta_zero_compat (F : diGraphType) (m : nat) :
  X2MaderianLegacy.least_mader_delta_zero F m <-> least_mader_delta_zero F m.
Proof. exact: iff_refl. Qed.

Lemma mader_delta0_transitive_tournament_statement_compat :
  X2MaderDelta0Legacy.statement <-> mader_delta0_transitive_tournament_statement.
Proof. exact: iff_refl. Qed.

Lemma oriented_trees_delta_plus_maderian_statement_compat :
  X2TreesLegacy.statement <-> oriented_trees_delta_plus_maderian_statement.
Proof. exact: iff_refl. Qed.

Lemma delta_plus_maderian_disjoint_union_statement_compat :
  X2UnionLegacy.statement <-> delta_plus_maderian_disjoint_union_statement.
Proof. exact: iff_refl. Qed.

(** ** Certificates: X52 (through [contains_subdivision]) *)

Lemma x52_mader_chi_bound_compat (F : diGraphType) (m : nat) :
  X52Legacy.mader_chi_bound F m <-> x52_mader_chi_bound F m.
Proof. exact: iff_refl. Qed.

Lemma oriented_tree_mader_chi_linear_bound_statement_compat :
  X52Legacy.statement <-> oriented_tree_mader_chi_linear_bound_statement.
Proof. exact: iff_refl. Qed.

(** ** Certificates: X90 (through [contains_subdivision]) *)

Lemma x90_f_subdivision_problem_compat (F D : diGraphType) :
  X90Legacy.f_subdivision_problem F D <-> x90_f_subdivision_problem F D.
Proof. exact: iff_refl. Qed.

Lemma f_subdivision_complexity_dichotomy_statement_compat :
  X90Legacy.statement <-> f_subdivision_complexity_dichotomy_statement.
Proof. exact: iff_refl. Qed.

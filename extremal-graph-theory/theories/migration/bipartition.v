(** Frozen C7 source and complete statement declarations; baseline and exact substitutions
    are recorded in meta/migration_reports/bipartition.spec.json. *)
From GTBase Require Import base.
From Extremal.conjectures Require Import X4 XE1 X223 XE2.
From Extremal.migration Require Import subgraph_of.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module X223Legacy.

Definition x223_bipartite_dg (B : diGraph) : Prop :=
  exists f : B -> bool, forall x y : B, x -- y -> f x != f y.

Definition directed_sidorenko_bipartite_statement : Prop :=
  forall B : diGraph,
    oriented B ->
    X223Legacy.x223_bipartite_dg B ->
    x223_hom_to_arc B ->
    x223_directed_sidorenko B.

End X223Legacy.

Module XE2Legacy.

Definition xe2_bipartition_sizes (G : sgraph) (a b : nat) : Prop :=
  exists A B : {set G},
    [disjoint A & B] /\
    A :|: B = [set: G] /\
    #|A| = a /\
    #|B| = b /\
    forall x y : G, x -- y ->
      (x \in A /\ y \in B) \/ (x \in B /\ y \in A).

Definition erdos_1080_statement : Prop :=
  exists cnum cden : nat,
    0 < cnum /\ 0 < cden /\
    forall (n : nat) (G : sgraph),
      #|G| = n ->
      (exists a b : nat, xe2_cube_square_floor n a /\ XE2Legacy.xe2_bipartition_sizes G a b) ->
      cden * x4_edge_count G >= cnum * n ->
      xe1_subgraph_of (cycle_graph 6) G.

Definition erdos_549_statement : Prop :=
  forall (k R : nat) (T : sgraph),
    xe1_tree T -> XE2Legacy.xe2_bipartition_sizes T k (2 * k) ->
    xe1_diagonal_ramsey_number T R ->
    R = 4 * k - 1.

End XE2Legacy.

Lemma x223_bipartite_dg_compat (G : diGraph) :
  X223Legacy.x223_bipartite_dg G = x223_bipartite_dg G.
Proof. by []. Qed.
Lemma directed_sidorenko_bipartite_statement_compat :
  X223Legacy.directed_sidorenko_bipartite_statement <->
  directed_sidorenko_bipartite_statement.
Proof. exact: iff_refl. Qed.
Lemma xe2_bipartition_sizes_compat (G : sgraph) a b :
  XE2Legacy.xe2_bipartition_sizes G a b = xe2_bipartition_sizes G a b.
Proof. by []. Qed.
Lemma erdos_1080_statement_compat :
  XE2Legacy.erdos_1080_statement <-> erdos_1080_statement.
Proof. exact: iff_refl. Qed.
Lemma erdos_549_statement_compat :
  XE2Legacy.erdos_549_statement <-> erdos_549_statement.
Proof. exact: iff_refl. Qed.

(** Complete pre-A5/pre-C7 rows. Older per-step snapshots remain unchanged.
    [Legacy] and [XE1Legacy] here are the frozen modules imported from
    [Extremal.migration.subgraph_of]; [XE2Legacy] is this family's frozen part predicate. *)
Module XE2Original.

Definition erdos_1080_statement : Prop :=
  exists cnum cden : nat,
    0 < cnum /\ 0 < cden /\
    forall (n : nat) (G : sgraph),
      #|G| = n ->
      (exists a b : nat, xe2_cube_square_floor n a /\ XE2Legacy.xe2_bipartition_sizes G a b) ->
      cden * x4_edge_count G >= cnum * n ->
      Legacy.xe1_subgraph_of (cycle_graph 6) G.

Definition erdos_549_statement : Prop :=
  forall (k R : nat) (T : sgraph),
    xe1_tree T -> XE2Legacy.xe2_bipartition_sizes T k (2 * k) ->
    XE1Legacy.diagonal_ramsey_number T R ->
    R = 4 * k - 1.

End XE2Original.

Lemma erdos_1080_statement_original_compat :
  XE2Original.erdos_1080_statement <-> erdos_1080_statement.
Proof. exact: subgraph_of.erdos_1080_statement_compat. Qed.

Lemma erdos_549_statement_original_compat :
  XE2Original.erdos_549_statement <-> erdos_549_statement.
Proof. exact: subgraph_of.erdos_549_statement_compat. Qed.

(** Complete pre-A5/pre-A6/pre-C7 #549. Load A6 without importing its
    identically named Legacy modules; all earlier C7 bindings stay unchanged. *)
From Extremal.migration Require complement.

Module XE2ComplementOriginal.

Definition erdos_549_statement : Prop :=
  forall (k R : nat) (T : sgraph),
    xe1_tree T -> XE2Legacy.xe2_bipartition_sizes T k (2 * k) ->
    Extremal.migration.complement.XE1Original.diagonal_ramsey_number T R ->
    R = 4 * k - 1.

End XE2ComplementOriginal.

Lemma erdos_549_statement_complement_original_compat :
  XE2ComplementOriginal.erdos_549_statement <-> erdos_549_statement.
Proof. exact: Extremal.migration.complement.erdos_549_statement_original_compat. Qed.

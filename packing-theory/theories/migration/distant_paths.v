(** * Packing.migration.distant_paths — B27 certificates: X26's distant path family and its row

    Frozen verbatim at the fixed prerequisite 058da18 (B26 plus the A22 ball delta): X26's raw pairwise
    relation (unequal sequence values; the closed [d.-1]-set-ball around one support misses the other, with no
    separate disjointness conjunct), its existence wrapper (exact size [k], [uniq], endpoint-set paths) and
    the complete current row [bounded_degree_distant_induced_menger_statement] (for all [d] and [Dmax] a
    constant [C > 0] before [k], [G], [X] and [Y]; maximum degree at most [Dmax]; fewer than [C * k] separator
    vertices; [d = 0] kept).  Since B27 both sources are aliases of [GTBase.distant_paths] and the same bodies
    by conversion, so the three certificates below are kernel-checked conversions.  The copies keep the live
    B1 / B5 / A22 / B26 vocabulary.  The complete earlier row is A22's [X26Original] in
    Packing.migration.balls, reused with A22's certificate. *)

From GTBase Require Import base balls.
From GTBase Require distant_paths.
From Packing.conjectures Require Import X26.
From Packing.migration Require balls.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module A22 := Packing.migration.balls.

Module Legacy.

Definition x26_pairwise_distant_paths
    (G : sgraph) (d : nat) (paths : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in paths -> q \in paths -> p != q ->
    [disjoint x26_set_ball (d.-1) (x26_path_vertices p) & x26_path_vertices q].

Definition x26_has_k_distant_xy_paths
    (G : sgraph) (d k : nat) (X Y : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> x26_xy_path X Y p) /\
    Legacy.x26_pairwise_distant_paths d paths.

End Legacy.

Module X26Legacy.

Definition bounded_degree_distant_induced_menger_statement : Prop :=
  forall d Dmax : nat, exists C : nat,
    0 < C /\
    forall (k : nat) (G : sgraph) (X Y : {set G}),
      Delta G <= Dmax ->
      Legacy.x26_has_k_distant_xy_paths d k X Y \/
      exists Z : {set G},
        #|Z| < C * k /\
        x26_separates_xy X Y Z.

End X26Legacy.

Lemma x26_pairwise_distant_paths_compat (G : sgraph) (d : nat) (paths : seq (seq G)) :
  Legacy.x26_pairwise_distant_paths d paths <-> x26_pairwise_distant_paths d paths.
Proof. exact: iff_refl. Qed.

Lemma x26_has_k_distant_xy_paths_compat (G : sgraph) (d k : nat) (X Y : {set G}) :
  Legacy.x26_has_k_distant_xy_paths d k X Y <-> x26_has_k_distant_xy_paths d k X Y.
Proof. exact: iff_refl. Qed.

Lemma bounded_degree_distant_induced_menger_statement_compat :
  X26Legacy.bounded_degree_distant_induced_menger_statement <->
  bounded_degree_distant_induced_menger_statement.
Proof. exact: iff_refl. Qed.

(** The complete earlier row, reused from A22 with A22's own certificate. *)
Lemma bounded_degree_distant_induced_menger_statement_original_compat :
  Packing.migration.balls.X26Original.bounded_degree_distant_induced_menger_statement <->
  bounded_degree_distant_induced_menger_statement.
Proof. exact: A22.bounded_degree_distant_induced_menger_statement_original_compat. Qed.

Print Assumptions x26_pairwise_distant_paths_compat.
Print Assumptions x26_has_k_distant_xy_paths_compat.
Print Assumptions bounded_degree_distant_induced_menger_statement_compat.
Print Assumptions bounded_degree_distant_induced_menger_statement_original_compat.

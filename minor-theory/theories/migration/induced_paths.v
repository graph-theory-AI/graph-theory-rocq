(** * Minor.migration.induced_paths — B22 certificates: the X67 induced path, theta and row

    Frozen verbatim at the private baseline (byte-identical at B21 66279eb and C20 97605dd): the
    full-endpoint induced path with its length guard [x67_induced_path_between] (at least three
    vertices), the chain [x67_theta] over the frozen path, and the complete row
    [theta_triangle_free_bounded_degree_treewidth_statement] (arxiv:2001.01607#01, solved).  Since
    B22 the live [x67_induced_path_between] is a transparent alias of
    [GTBase.induced_paths.long_induced_path_between], the same body by conversion (its consecutive-pair
    test was already B3's alias of [seq_consecutive]); every certificate here is a conversion.  The
    copies keep the other families' live aliases ([x67_consecutive_in_path],
    [x67_internal_vertices], [x67_no_cross_edges], [x27_treewidth_at_most]); the complete
    pre-B1/B2/B3/C13/B22 row is C13's [X67Original.theta_triangle_free_bounded_degree_treewidth_statement],
    reused with its own certificate. *)

From GTBase Require Import base induced_paths.
From Minor.conjectures Require Import X27 X67.
From Minor.migration Require bag_decompositions.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module C13 := Minor.migration.bag_decompositions.

Module Legacy.

Definition x67_induced_path_between (G : sgraph) (a b : G) (p : seq G) : Prop :=
  match p with
  | [::] => False
  | x :: q =>
      x = a /\
      last x q = b /\
      3 <= size p /\
      uniq p /\
      path (--) x q /\
      forall u v : G,
        u \in p -> v \in p -> u -- v -> u != v ->
        x67_consecutive_in_path p u v
  end.

End Legacy.

Module X67Legacy.

Definition x67_theta (G : sgraph) : Prop :=
  exists (a b : G) (p1 p2 p3 : seq G),
    a != b /\
    Legacy.x67_induced_path_between a b p1 /\
    Legacy.x67_induced_path_between a b p2 /\
    Legacy.x67_induced_path_between a b p3 /\
    [disjoint x67_internal_vertices a b p1 & x67_internal_vertices a b p2] /\
    [disjoint x67_internal_vertices a b p1 & x67_internal_vertices a b p3] /\
    [disjoint x67_internal_vertices a b p2 & x67_internal_vertices a b p3] /\
    x67_no_cross_edges a b p1 p2 /\
    x67_no_cross_edges a b p1 p3 /\
    x67_no_cross_edges a b p2 p3.

Definition theta_triangle_free_bounded_degree_treewidth_statement : Prop :=
  exists f : nat -> nat,
    forall (t : nat) (G : sgraph),
      4 <= t ->
      Delta G <= t ->
      triangle_free G ->
      ~ X67Legacy.x67_theta G ->
      x27_treewidth_at_most G (f t).

End X67Legacy.

(** ** Certificates (conversions) *)

Lemma x67_induced_path_between_compat (G : sgraph) (a b : G) (p : seq G) :
  Legacy.x67_induced_path_between a b p <-> x67_induced_path_between a b p.
Proof. by []. Qed.

Lemma x67_theta_compat (G : sgraph) : X67Legacy.x67_theta G <-> x67_theta G.
Proof. by []. Qed.

Lemma theta_triangle_free_bounded_degree_treewidth_statement_compat :
  X67Legacy.theta_triangle_free_bounded_degree_treewidth_statement <->
  theta_triangle_free_bounded_degree_treewidth_statement.
Proof. by []. Qed.

(** ** The complete Original, reused from C13 *)

Lemma theta_triangle_free_bounded_degree_treewidth_statement_original_compat :
  Minor.migration.bag_decompositions.X67Original.theta_triangle_free_bounded_degree_treewidth_statement <->
  theta_triangle_free_bounded_degree_treewidth_statement.
Proof. exact: C13.theta_triangle_free_bounded_degree_treewidth_statement_original_compat. Qed.

Print Assumptions x67_induced_path_between_compat.
Print Assumptions x67_theta_compat.
Print Assumptions theta_triangle_free_bounded_degree_treewidth_statement_compat.
Print Assumptions theta_triangle_free_bounded_degree_treewidth_statement_original_compat.

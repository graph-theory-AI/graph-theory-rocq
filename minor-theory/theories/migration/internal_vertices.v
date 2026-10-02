(** * Minor.migration.internal_vertices — frozen internal-vertex chain (library migration B2)

    Batch B, family [internal-vertices] (meta/library_primitives/internal-vertices.json).  [Legacy]
    freezes the conjecture-local helper [x175_path_internal] verbatim as it stood
    at 9e03072, before the migration: the vertices of the head-plus-tail sequence
    [x :: p] other than [x] and [y].  The live helper now unfolds to
    [GTBase.walks_paths.seq_interior x y (x :: p)], keeping the head-plus-tail
    representation.  [X175Legacy] freezes the affected chain of row
    [kt_subdivision_clique_count_asymptotic_statement], the statement included,
    with the wave prefix dropped from the copied names and the frozen helper
    referred to as [Legacy.x175_path_internal].  Definitions that do not reach
    the helper (simple paths, the clique count and the asymptotic bound) are the
    live, unchanged ones.

    Row X67's internal-vertex helper [x67_internal_vertices] is also migrated by
    this family; its whole affected chain was frozen at 9e03072 by family B1 in
    [Minor.migration.path_vertices] ([Legacy.x67_path_vertices], [X67Legacy]); this
    module does not copy it again, and states this family's X67 certificates over
    those frozen bodies (section X67 below), by conversion through [seq_interior].

    The frozen helper is a boolean comprehension and [seq_interior] a set
    difference: they are extensionally equal, not convertible.
    [x175_path_internal_compat] proves the equality by membership
    ([in_seq_interior]); the chain certificates transport it under the binders.
    Source hashes, the exact substitutions and the per-row theorem names are
    recorded in meta/migration_reports/internal_vertices.md. *)

From GTBase Require Import base.
From Minor.conjectures Require Import X67 X175.
From Minor.migration Require path_vertices.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x175_path_internal {G : sgraph} (x y : G) (p : seq G) : {set G} :=
  [set z : G | (z \in x :: p) && (z != x) && (z != y)].

End Legacy.

Module X175Legacy.

Definition Kt_subdivision (G : sgraph) (t : nat) : Prop :=
  exists branch : 'I_t -> G,
    injective branch /\
    exists route : 'I_t -> 'I_t -> seq G,
      [/\ (forall i j : 'I_t,
             i < j -> x175_simple_path_between (branch i) (branch j) (route i j)),
          (forall i j k : 'I_t,
             i < j ->
             branch k \notin Legacy.x175_path_internal (branch i) (branch j) (route i j)) &
          forall i j i' j' : 'I_t,
             i < j -> i' < j' -> (i != i') || (j != j') ->
             [disjoint Legacy.x175_path_internal (branch i) (branch j) (route i j) &
                       Legacy.x175_path_internal (branch i') (branch j') (route i' j')]].

Definition statement : Prop :=
  forall a b : nat,
    0 < a -> 0 < b ->
    eventually (fun t =>
      forall G : sgraph,
        ~ Kt_subdivision G t ->
        x175_subdivision_clique_asymptotic_bound
          a b t #|G| (x175_clique_count G)).

End X175Legacy.

(** ** Certificates *)

Lemma x175_path_internal_compat (G : sgraph) (x y : G) (p : seq G) :
  Legacy.x175_path_internal x y p = x175_path_internal x y p.
Proof. by apply/setP => z; rewrite /x175_path_internal in_seq_interior inE andbA. Qed.

Lemma x175_Kt_subdivision_compat (G : sgraph) (t : nat) :
  X175Legacy.Kt_subdivision G t <-> x175_Kt_subdivision G t.
Proof.
rewrite /X175Legacy.Kt_subdivision /x175_Kt_subdivision.
split=> -[branch [inj [route [paths avoid dis]]]]; exists branch; split=> //;
  exists route; split=> // [i j k ij | i j i' j' ij ij' ne].
- by move: (avoid i j k ij); rewrite x175_path_internal_compat.
- by move: (dis i j i' j' ij ij' ne); rewrite !x175_path_internal_compat.
- by move: (avoid i j k ij); rewrite x175_path_internal_compat.
- by move: (dis i j i' j' ij ij' ne); rewrite !x175_path_internal_compat.
Qed.

Lemma kt_subdivision_clique_count_asymptotic_statement_compat :
  X175Legacy.statement <-> kt_subdivision_clique_count_asymptotic_statement.
Proof.
rewrite /X175Legacy.statement /kt_subdivision_clique_count_asymptotic_statement.
split=> h a b a0 b0; have [N hN] := h a b a0 b0; exists N => t Nt G noKt;
  apply: (hN t Nt G); by move/x175_Kt_subdivision_compat.
Qed.

(** ** X67, over family B1's frozen chain

    [x67_internal_vertices] now unfolds to [seq_interior a b p].  B1 froze the X67
    chain at 9e03072 in [Minor.migration.path_vertices] ([Legacy.x67_path_vertices],
    [X67Legacy.internal_vertices], [X67Legacy.no_cross_edges], [X67Legacy.theta],
    [X67Legacy.statement]), freezing this family's helper too; the certificates below
    are stated over those bodies and are kernel-checked conversions. *)

Lemma x67_internal_vertices_compat (G : sgraph) (a b : G) (p : seq G) :
  Minor.migration.path_vertices.X67Legacy.internal_vertices a b p =
  x67_internal_vertices a b p.
Proof. by rewrite /x67_internal_vertices /seq_interior seq_verticesE. Qed.

Lemma theta_triangle_free_bounded_degree_treewidth_statement_compat :
  Minor.migration.path_vertices.X67Legacy.statement <->
  theta_triangle_free_bounded_degree_treewidth_statement.
Proof. exact: iff_refl. Qed.

(** * Chromatic.migration.path_vertices — frozen path-vertex chain (library migration B1)

    Batch B family [path-vertices] (meta/library_primitives.json): the local
    helper [x3_path_vertices] now unfolds to [GTBase.walks_paths.seq_vertices].

    [X3Legacy] holds verbatim copies, taken at base commit 9e03072, of every
    definition on the affected dependency chain of row
    [stable_cover_unique_induced_path_statement]: the helper and each
    definition that reaches it.  Inside the module the copies shadow the live
    names, so the frozen statement never resolves through the migrated helper;
    definitions that do not reach the helper are the live, unchanged ones.

    [seq_vertices s] is MathComp's [[set:: s]], which unfolds to the frozen
    comprehension [[set v | v \in s]]; so every live definition is convertible
    to its frozen copy and the certificates below are kernel-checked
    conversions ([x3_path_vertices_compat] goes through [seq_verticesE]).
    Source hashes, the per-row theorem table and the [Print All Dependencies]
    check of the frozen closure: meta/migration_reports/path_vertices.md. *)

From Chromatic.conjectures Require Import U8.
From GTBase Require Import walks_paths.
From Chromatic.conjectures Require Import X3.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module X3Legacy.

Definition x3_path_vertices (G : sgraph) (p : seq G) : {set G} :=
  [set v | v \in p].

Definition x3_uniquely_covers_path_vertex
    (G : sgraph) (I : finType) (A : I -> {set G}) (p : seq G) (v : G) : Prop :=
  exists i : I, A i :&: x3_path_vertices p = [set v].

Definition stable_cover_unique_induced_path_statement : Prop :=
  forall s : nat, exists n : nat,
    forall (G : sgraph) (I : finType) (A : I -> {set G}),
      triangle_free G ->
      n <= χ([set: G]) ->
      (forall i : I, x3_stable_set (A i)) ->
      x3_family_covers_vertices A ->
      exists p : seq G,
        size p = s /\
        x3_induced_path p /\
        forall v : G, v \in p -> x3_uniquely_covers_path_vertex A p v.

End X3Legacy.

(** ** Certificates *)

Lemma x3_path_vertices_compat (G : sgraph) (p : seq G) :
  X3Legacy.x3_path_vertices p = x3_path_vertices p.
Proof. by rewrite /x3_path_vertices seq_verticesE. Qed.

Lemma x3_uniquely_covers_path_vertex_compat
    (G : sgraph) (I : finType) (A : I -> {set G}) (p : seq G) (v : G) :
  X3Legacy.x3_uniquely_covers_path_vertex A p v <->
  x3_uniquely_covers_path_vertex A p v.
Proof. exact: iff_refl. Qed.

Lemma stable_cover_unique_induced_path_statement_compat :
  X3Legacy.stable_cover_unique_induced_path_statement <->
  stable_cover_unique_induced_path_statement.
Proof. exact: iff_refl. Qed.

(** * Chromatic.migration.path_vertices — frozen path-vertex chain (library migration B1)

    Batch B, family [path-vertices] (meta/library_primitives.json).  [Legacy]
    freezes the conjecture-local helper [x3_path_vertices] verbatim as it stood at
    9e03072, before the migration; the live helper now unfolds to
    [GTBase.walks_paths.seq_vertices].  [X3Legacy] freezes the affected chain of
    row [stable_cover_unique_induced_path_statement], the statement included: the
    copies drop the wave prefix of their names and refer to the frozen helper as
    [Legacy.x3_path_vertices], so no frozen body resolves through a live helper of
    this family.  Definitions that do not reach the helper are the live, unchanged
    ones.

    [seq_vertices s] is MathComp's [[set:: s]], which unfolds to the frozen
    comprehension [[set v | v \in s]], so every live definition is convertible to
    its frozen copy: the certificates below are kernel-checked conversions, the
    helper certificate going through [seq_verticesE].  Source hashes, the exact
    substitutions and the per-row theorem names are recorded in
    meta/migration_reports/path_vertices.md. *)

From Chromatic.conjectures Require Import U8 X3.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x3_path_vertices (G : sgraph) (p : seq G) : {set G} :=
  [set v | v \in p].

End Legacy.

Module X3Legacy.

Definition uniquely_covers_path_vertex
    (G : sgraph) (I : finType) (A : I -> {set G}) (p : seq G) (v : G) : Prop :=
  exists i : I, A i :&: Legacy.x3_path_vertices p = [set v].

Definition statement : Prop :=
  forall s : nat, exists n : nat,
    forall (G : sgraph) (I : finType) (A : I -> {set G}),
      triangle_free G ->
      n <= χ([set: G]) ->
      (forall i : I, x3_stable_set (A i)) ->
      x3_family_covers_vertices A ->
      exists p : seq G,
        size p = s /\
        x3_induced_path p /\
        forall v : G, v \in p -> uniquely_covers_path_vertex A p v.

End X3Legacy.

(** ** Certificates *)

Lemma x3_path_vertices_compat (G : sgraph) (p : seq G) :
  Legacy.x3_path_vertices p = x3_path_vertices p.
Proof. by rewrite /x3_path_vertices seq_verticesE. Qed.

Lemma x3_uniquely_covers_path_vertex_compat
    (G : sgraph) (I : finType) (A : I -> {set G}) (p : seq G) (v : G) :
  X3Legacy.uniquely_covers_path_vertex A p v <-> x3_uniquely_covers_path_vertex A p v.
Proof. exact: iff_refl. Qed.

Lemma stable_cover_unique_induced_path_statement_compat :
  X3Legacy.statement <-> stable_cover_unique_induced_path_statement.
Proof. exact: iff_refl. Qed.

(** * Chromatic.migration.consecutive_in_path — frozen consecutive-entry chains (library migration B3)

    Batch B, family [consecutive-in-path]
    (meta/library_primitives/consecutive-in-path.json).  [Legacy] freezes the
    conjecture-local helper [x3_consecutive_in_path] verbatim as it stood at
    787a996, before the migration: the pair [(u, v)] or the pair [(v, u)] occurs
    among the adjacent pairs [zip p (behead p)] of [p].  The live helper now
    unfolds to [GTBase.walks_paths.seq_consecutive p u v], whose body is that
    same disjunction, so every live definition below is convertible to its frozen
    copy and the certificates are kernel-checked conversions.

    [X3Legacy] freezes the affected chain of row
    [stable_cover_unique_induced_path_statement]: [induced_path] and the
    statement.  [X83Legacy] freezes the cross-module chain of row
    [aravind_rainbow_induced_chromatic_path_statement], which reaches the helper
    through [x83_rainbow_induced_path] and X3's [x3_induced_path].  The copies
    drop the wave prefix and refer to the frozen helper as
    [Legacy.x3_consecutive_in_path]; definitions that do not reach the helper are
    the live ones, in particular [x3_uniquely_covers_path_vertex], migrated by
    family path-vertices (B1).

    B1's snapshot [Chromatic.migration.path_vertices.X3Legacy.statement] froze
    only the path-vertex chain and calls the live [x3_induced_path], which now
    reaches [seq_consecutive]; its body is kept unchanged.  [X3Original] freezes
    the pre-migration statement end to end, over both families' frozen chains,
    and [stable_cover_unique_induced_path_statement_original_compat] relates it
    to the live statement.  Source hashes, the exact substitutions and the
    per-row theorem names are recorded in
    meta/migration_reports/consecutive_in_path.md. *)

From Chromatic.conjectures Require Import U8 X3 X83.
From Chromatic.migration Require path_vertices.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x3_consecutive_in_path (G : sgraph) (p : seq G) (u v : G) : Prop :=
  ((u, v) \in zip p (behead p)) \/ ((v, u) \in zip p (behead p)).

End Legacy.

Module X3Legacy.

Definition induced_path (G : sgraph) (p : seq G) : Prop :=
  [/\ uniq p,
      (if p is u :: q then path (--) u q else true)
    & forall u v : G,
        u \in p -> v \in p -> u != v -> u -- v ->
        Legacy.x3_consecutive_in_path p u v].

Definition statement : Prop :=
  forall s : nat, exists n : nat,
    forall (G : sgraph) (I : finType) (A : I -> {set G}),
      triangle_free G ->
      n <= χ([set: G]) ->
      (forall i : I, x3_stable_set (A i)) ->
      x3_family_covers_vertices A ->
      exists p : seq G,
        size p = s /\
        induced_path p /\
        forall v : G, v \in p -> x3_uniquely_covers_path_vertex A p v.

End X3Legacy.

Module X83Legacy.

Definition rainbow_induced_path
    (G : sgraph) (C : finType) (col : G -> C) (p : seq G) : Prop :=
  X3Legacy.induced_path p /\ uniq (map col p).

Definition statement : Prop :=
  forall (G : sgraph) (C : finType) (col : G -> C),
    0 < #|G| ->
    triangle_free G ->
    x3_proper_colouring col ->
    exists p : seq G,
      size p = χ([set: G]) /\
      rainbow_induced_path col p.

End X83Legacy.

(** The X3 statement before both migrations: the induced path of this family and
    the path-vertex chain of family B1, both frozen. *)
Module X3Original.

Definition statement : Prop :=
  forall s : nat, exists n : nat,
    forall (G : sgraph) (I : finType) (A : I -> {set G}),
      triangle_free G ->
      n <= χ([set: G]) ->
      (forall i : I, x3_stable_set (A i)) ->
      x3_family_covers_vertices A ->
      exists p : seq G,
        size p = s /\
        X3Legacy.induced_path p /\
        forall v : G, v \in p -> path_vertices.X3Legacy.uniquely_covers_path_vertex A p v.

End X3Original.

(** ** Certificates *)

Lemma x3_consecutive_in_path_compat (G : sgraph) (p : seq G) (u v : G) :
  Legacy.x3_consecutive_in_path p u v = x3_consecutive_in_path p u v.
Proof. by []. Qed.

Lemma x3_induced_path_compat (G : sgraph) (p : seq G) :
  X3Legacy.induced_path p <-> x3_induced_path p.
Proof. exact: iff_refl. Qed.

Lemma stable_cover_unique_induced_path_statement_compat :
  X3Legacy.statement <-> stable_cover_unique_induced_path_statement.
Proof. exact: iff_refl. Qed.

Lemma x83_rainbow_induced_path_compat
    (G : sgraph) (C : finType) (col : G -> C) (p : seq G) :
  X83Legacy.rainbow_induced_path col p <-> x83_rainbow_induced_path col p.
Proof. exact: iff_refl. Qed.

Lemma aravind_rainbow_induced_chromatic_path_statement_compat :
  X83Legacy.statement <-> aravind_rainbow_induced_chromatic_path_statement.
Proof. exact: iff_refl. Qed.

Lemma stable_cover_unique_induced_path_statement_original_compat :
  X3Original.statement <-> stable_cover_unique_induced_path_statement.
Proof. exact: iff_refl. Qed.

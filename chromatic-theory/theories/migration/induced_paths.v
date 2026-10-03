(** * Chromatic.migration.induced_paths — B22 certificates: the X3 induced path and the X3 / X83 rows

    Frozen verbatim at the private baseline (the bodies are byte-identical at B21 66279eb and C20
    97605dd): the empty-allowed induced path [x3_induced_path], the X83 chain
    [x83_rainbow_induced_path] over the frozen path, and the two complete rows
    [stable_cover_unique_induced_path_statement] (X3, arxiv:1702.01094#01) and
    [aravind_rainbow_induced_chromatic_path_statement] (X83, studies slug).  Since B22 the live
    [x3_induced_path] is a transparent alias of [GTBase.induced_paths.induced_path], the same body by
    conversion (its consecutive-pair test was already B3's alias of [seq_consecutive]); every
    certificate here is a conversion.  The per-row copies keep the other families' live aliases
    ([x3_consecutive_in_path], [x3_stable_set], [x3_family_covers_vertices],
    [x3_uniquely_covers_path_vertex], [x3_proper_colouring]); the complete pre-B1/B3/B22 and
    pre-B3/C5/B22 rows are B3's [X3Original.statement] and C5's
    [X83Original.aravind_rainbow_induced_chromatic_path_statement], reused with their own certificates. *)

From GTBase Require Import base colourings graph_classes induced_paths.
From Chromatic.conjectures Require Import U8 X3 X83.
From Chromatic.migration Require consecutive_in_path proper_colouring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module B3 := Chromatic.migration.consecutive_in_path.
Module C5 := Chromatic.migration.proper_colouring.

Module Legacy.

Definition x3_induced_path (G : sgraph) (p : seq G) : Prop :=
  [/\ uniq p,
      (if p is u :: q then path (--) u q else true)
    & forall u v : G,
        u \in p -> v \in p -> u != v -> u -- v ->
        x3_consecutive_in_path p u v].

End Legacy.

Module X3Legacy.

Definition stable_cover_unique_induced_path_statement : Prop :=
  forall s : nat, exists n : nat,
    forall (G : sgraph) (I : finType) (A : I -> {set G}),
      triangle_free G ->
      n <= χ([set: G]) ->
      (forall i : I, x3_stable_set (A i)) ->
      x3_family_covers_vertices A ->
      exists p : seq G,
        size p = s /\
        Legacy.x3_induced_path p /\
        forall v : G, v \in p -> x3_uniquely_covers_path_vertex A p v.

End X3Legacy.

Module X83Legacy.

Definition x83_rainbow_induced_path
    (G : sgraph) (C : finType) (col : G -> C) (p : seq G) : Prop :=
  Legacy.x3_induced_path p /\ uniq (map col p).

Definition aravind_rainbow_induced_chromatic_path_statement : Prop :=
  forall (G : sgraph) (C : finType) (col : G -> C),
    0 < #|G| ->
    triangle_free G ->
    x3_proper_colouring col ->
    exists p : seq G,
      size p = χ([set: G]) /\
      X83Legacy.x83_rainbow_induced_path col p.

End X83Legacy.

(** ** Certificates (conversions) *)

Lemma x3_induced_path_compat (G : sgraph) (p : seq G) :
  Legacy.x3_induced_path p <-> x3_induced_path p.
Proof. by []. Qed.

Lemma stable_cover_unique_induced_path_statement_compat :
  X3Legacy.stable_cover_unique_induced_path_statement <->
  stable_cover_unique_induced_path_statement.
Proof. by []. Qed.

Lemma x83_rainbow_induced_path_compat (G : sgraph) (C : finType) (col : G -> C) (p : seq G) :
  X83Legacy.x83_rainbow_induced_path col p <-> x83_rainbow_induced_path col p.
Proof. by []. Qed.

Lemma aravind_rainbow_induced_chromatic_path_statement_compat :
  X83Legacy.aravind_rainbow_induced_chromatic_path_statement <->
  aravind_rainbow_induced_chromatic_path_statement.
Proof. by []. Qed.

(** ** The complete Originals, reused from B3 (X3) and C5 (X83) *)

Lemma stable_cover_unique_induced_path_statement_original_compat :
  Chromatic.migration.consecutive_in_path.X3Original.statement <-> stable_cover_unique_induced_path_statement.
Proof. exact: B3.stable_cover_unique_induced_path_statement_original_compat. Qed.

Lemma aravind_rainbow_induced_chromatic_path_statement_original_compat :
  Chromatic.migration.proper_colouring.X83Original.aravind_rainbow_induced_chromatic_path_statement <->
  aravind_rainbow_induced_chromatic_path_statement.
Proof. exact: C5.aravind_rainbow_induced_chromatic_path_statement_compat. Qed.

Print Assumptions x3_induced_path_compat.
Print Assumptions stable_cover_unique_induced_path_statement_compat.
Print Assumptions x83_rainbow_induced_path_compat.
Print Assumptions aravind_rainbow_induced_chromatic_path_statement_compat.
Print Assumptions stable_cover_unique_induced_path_statement_original_compat.
Print Assumptions aravind_rainbow_induced_chromatic_path_statement_original_compat.

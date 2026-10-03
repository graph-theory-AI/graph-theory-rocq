(** A17 clique counts (extremal): the frozen D2tur nonempty count, X88 exact-size count and X4 triangle count with
    its unchanged triangle-set support, the D2tur and X4 rows, and X4's complete row.  Baseline, hashes and exact
    substitutions are recorded in meta/migration_reports/clique_counts.spec.json.
    - [Legacy]: each count equals its GTBase.clique_counts view by an unconditional cardinality equality (not a
      conversion): D2tur's is [nonempty_clique_count], X88's is [clique_count_size G r], X4's triangle count is
      [clique_count_size G 3].  [x4_triangle_set] is frozen only as the support of the frozen triangle count; its live
      body is unchanged.  X88's count reaches no row.
    - [D2turLegacy], [X4Legacy]: the rows over the frozen counts; D2tur's has no older history, so it is also complete.
    - [X4Original]: the complete supersaturation row, composing A7's frozen edge count with the frozen triangle count
      (text at A7's baseline ae0e605).  A7's module is aliased, not imported; the bridge reuses A7's certificate. *)
From Corelib Require Import Setoid Morphisms.
From GTBase Require Import base clique_counts.
From Extremal.conjectures Require Import D2tur X4 X88.
From Extremal.migration Require edge_count.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A7's certificate module, aliased without Import: its module names coincide with this file's. *)
Module A7 := Extremal.migration.edge_count.

Module Legacy.

Definition clique_count (G : sgraph) : nat :=
  #|[set S : {set G} | cliqueb S && (S != set0)]|.

Definition x88_clique_count (G : sgraph) (r : nat) : nat :=
  #|[set S : {set G} | (#|S| == r) && cliqueb S]|.

Definition x4_triangle_set (G : sgraph) (T : {set G}) : bool :=
  (#|T| == 3) && cliqueb T.

Definition x4_triangle_count (G : sgraph) : nat :=
  #|[set T : {set G} | Legacy.x4_triangle_set T]|.

End Legacy.

Module D2turLegacy.

Definition number_of_cliques_in_minor_closed_classes_statement : Prop :=
  exists c : nat, forall (t : nat) (G : sgraph), (0 < t)%N ->
    Kt_minor_free G t -> (Legacy.clique_count G <= c ^ t * #|G|)%N.

End D2turLegacy.

Module X4Legacy.

Definition triangle_supersaturation_statement : Prop :=
  forall G : sgraph, forall n t : nat,
    #|G| = n -> t < n %/ 2 ->
    x4_edge_count G = n * n %/ 4 + t ->
    t * (n %/ 2) <= Legacy.x4_triangle_count G.

End X4Legacy.

Module X4Original.

Definition triangle_supersaturation_statement : Prop :=
  forall G : sgraph, forall n t : nat,
    #|G| = n -> t < n %/ 2 ->
    A7.Legacy.x4_edge_count G = n * n %/ 4 + t ->
    t * (n %/ 2) <= Legacy.x4_triangle_count G.

End X4Original.

Lemma clique_count_compat (G : sgraph) :
  Legacy.clique_count G = clique_count G.
Proof.
by rewrite /clique_count nonempty_clique_countE.
Qed.

Lemma x88_clique_count_compat (G : sgraph) (r : nat) :
  Legacy.x88_clique_count G r = x88_clique_count G r.
Proof.
by rewrite /x88_clique_count clique_count_sizeE.
Qed.

Lemma x4_triangle_set_compat (G : sgraph) (T : {set G}) :
  Legacy.x4_triangle_set T = x4_triangle_set T.
Proof.
by [].
Qed.

Lemma x4_triangle_count_compat (G : sgraph) :
  Legacy.x4_triangle_count G = x4_triangle_count G.
Proof.
by rewrite /x4_triangle_count clique_count_sizeE.
Qed.

Lemma number_of_cliques_in_minor_closed_classes_statement_compat :
  D2turLegacy.number_of_cliques_in_minor_closed_classes_statement <-> number_of_cliques_in_minor_closed_classes_statement.
Proof.
rewrite /D2turLegacy.number_of_cliques_in_minor_closed_classes_statement /number_of_cliques_in_minor_closed_classes_statement.
by setoid_rewrite clique_count_compat.
Qed.

Lemma triangle_supersaturation_statement_compat :
  X4Legacy.triangle_supersaturation_statement <-> triangle_supersaturation_statement.
Proof.
rewrite /X4Legacy.triangle_supersaturation_statement /triangle_supersaturation_statement.
by setoid_rewrite x4_triangle_count_compat.
Qed.

(** Complete X4: A7's frozen edge count is kept; only the triangle count is rewritten, then A7's certificate. *)
Lemma triangle_supersaturation_statement_original_compat :
  X4Original.triangle_supersaturation_statement <-> triangle_supersaturation_statement.
Proof.
apply: (iff_trans _ A7.triangle_supersaturation_statement_compat).
rewrite /X4Original.triangle_supersaturation_statement /A7.X4Legacy.triangle_supersaturation_statement.
by setoid_rewrite x4_triangle_count_compat.
Qed.

(** A17 clique counts (minor): the frozen X174 all-clique count and X175 nonempty count, both rows and their
    complete rows.  Baseline, hashes and exact substitutions are recorded in
    meta/migration_reports/clique_counts.spec.json.
    - [Legacy]: X174's count equals [all_clique_count] (the empty clique included) and X175's equals
      [nonempty_clique_count], each by an unconditional cardinality equality (not a conversion).
    - [X174Legacy], [X175Legacy]: the rows over the frozen counts.  X174's bound keeps its natural subtraction
      [(n - t + 3)] and both the upper-bound and the attainment halves; X175 keeps its eventual-in-t upper envelope.
    - [X174Original], [X175Original]: the complete rows, composing B8's frozen immersion chain (text at 048c768) and
      B2's frozen subdivision chain (text at 9e03072).  Their modules are aliased, not imported; the bridges reuse
      their certificates. *)
From Corelib Require Import Setoid Morphisms.
From GTBase Require Import base clique_counts.
From Minor.conjectures Require Import U7 X174 X175.
From Minor.migration Require path_edges internal_vertices.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** B8's and B2's certificate modules, aliased without Import: their module names coincide with this file's. *)
Module B8 := Minor.migration.path_edges.
Module B2 := Minor.migration.internal_vertices.

Module Legacy.

Definition x174_clique_count (G : sgraph) : nat :=
  #|[set S : {set G} | cliqueb S]|.

Definition x175_clique_count (G : sgraph) : nat :=
  #|[set S : {set G} | cliqueb S && (S != set0)]|.

End Legacy.

Module X174Legacy.

Definition kt_immersion_clique_count_extremal_statement : Prop :=
  forall t n : nat,
    2 <= t ->
    t - 2 <= n ->
    (forall G : sgraph,
        #|G| = n ->
        x174_no_Kt_immersion G t ->
        Legacy.x174_clique_count G <= x174_extremal_bound t n) /\
    (exists G : sgraph,
        #|G| = n /\
        x174_no_Kt_immersion G t /\
        Legacy.x174_clique_count G = x174_extremal_bound t n).

End X174Legacy.

Module X175Legacy.

Definition kt_subdivision_clique_count_asymptotic_statement : Prop :=
  forall a b : nat,
    0 < a -> 0 < b ->
    eventually (fun t =>
      forall G : sgraph,
        ~ x175_Kt_subdivision G t ->
        x175_subdivision_clique_asymptotic_bound
          a b t #|G| (Legacy.x175_clique_count G)).

End X175Legacy.

Module X174Original.

Definition kt_immersion_clique_count_extremal_statement : Prop :=
  forall t n : nat,
    2 <= t ->
    t - 2 <= n ->
    (forall G : sgraph,
        #|G| = n ->
        B8.X174Legacy.no_Kt_immersion G t ->
        Legacy.x174_clique_count G <= x174_extremal_bound t n) /\
    (exists G : sgraph,
        #|G| = n /\
        B8.X174Legacy.no_Kt_immersion G t /\
        Legacy.x174_clique_count G = x174_extremal_bound t n).

End X174Original.

Module X175Original.

Definition kt_subdivision_clique_count_asymptotic_statement : Prop :=
  forall a b : nat,
    0 < a -> 0 < b ->
    eventually (fun t =>
      forall G : sgraph,
        ~ B2.X175Legacy.Kt_subdivision G t ->
        x175_subdivision_clique_asymptotic_bound
          a b t #|G| (Legacy.x175_clique_count G)).

End X175Original.

Lemma x174_clique_count_compat (G : sgraph) :
  Legacy.x174_clique_count G = x174_clique_count G.
Proof.
by rewrite /x174_clique_count all_clique_countE.
Qed.

Lemma x175_clique_count_compat (G : sgraph) :
  Legacy.x175_clique_count G = x175_clique_count G.
Proof.
by rewrite /x175_clique_count nonempty_clique_countE.
Qed.

Lemma kt_immersion_clique_count_extremal_statement_compat :
  X174Legacy.kt_immersion_clique_count_extremal_statement <-> kt_immersion_clique_count_extremal_statement.
Proof.
rewrite /X174Legacy.kt_immersion_clique_count_extremal_statement /kt_immersion_clique_count_extremal_statement.
by setoid_rewrite x174_clique_count_compat.
Qed.

(** The eventual threshold [N] is kept in both directions; only the count is rewritten. *)
Lemma kt_subdivision_clique_count_asymptotic_statement_compat :
  X175Legacy.kt_subdivision_clique_count_asymptotic_statement <-> kt_subdivision_clique_count_asymptotic_statement.
Proof.
split=> h a b a0 b0; have [N hN] := h a b a0 b0; exists N => t Nt G noKt;
  move: (hN t Nt G noKt); by rewrite x175_clique_count_compat.
Qed.

(** Complete X174: B8's frozen immersion chain is kept; only the count is rewritten, then B8's certificate. *)
Lemma kt_immersion_clique_count_extremal_statement_original_compat :
  X174Original.kt_immersion_clique_count_extremal_statement <-> kt_immersion_clique_count_extremal_statement.
Proof.
apply: (iff_trans _ B8.kt_immersion_clique_count_extremal_statement_compat).
rewrite /X174Original.kt_immersion_clique_count_extremal_statement /B8.X174Legacy.kt_immersion_clique_count_extremal_statement.
by setoid_rewrite x174_clique_count_compat.
Qed.

(** Complete X175: B2's frozen subdivision chain is kept; only the count is rewritten, then B2's certificate. *)
Lemma kt_subdivision_clique_count_asymptotic_statement_original_compat :
  X175Original.kt_subdivision_clique_count_asymptotic_statement <-> kt_subdivision_clique_count_asymptotic_statement.
Proof.
apply: (iff_trans _ B2.kt_subdivision_clique_count_asymptotic_statement_compat).
split=> h a b a0 b0; have [N hN] := h a b a0 b0; exists N => t Nt G noKt;
  move: (hN t Nt G noKt); by rewrite x175_clique_count_compat.
Qed.

(** * GTMisc.migration.consecutive_in_cycle — frozen cyclic-adjacency chain (library migration B4)

    Batch B, family [consecutive-in-cycle]
    (meta/library_primitives/consecutive-in-cycle.json).  [Legacy] freezes the
    Prop helper [x91_consecutive_in_cycle] verbatim as it stood at 49ddc03, before
    the migration; the live helper now unfolds to
    [GTBase.walks_paths.seq_cyclic_consecutive c u v], whose body is the same
    disjunction, so the certificates below are kernel-checked conversions.

    [X91CycleLegacy] freezes the induced cycle (with its own [3 <= size c] guard)
    and [X91Legacy] the rest of this family's chain of row
    [avoidable_path_or_pk_free_statement]: the avoidable path and the statement.
    The cycle has its own module so that its prefix-dropped name never appears
    unqualified next to D2str's unrelated [induced_cycle].  The avoidable path
    also calls [x91_induced_path], and the statement [x91_Pk_free], migrated by
    family consecutive-in-path (B3); those are the live ones here, by design.
    B3's snapshot [GTMisc.migration.consecutive_in_path.X91Legacy.avoidable_path]
    calls the live [x91_induced_cycle], which now reaches this family's canonical;
    it is kept unchanged.  [X91Original] freezes the row end to end over B3's frozen
    induced path and [Pk_free] and this family's frozen induced cycle, and the
    [*_original_compat] certificates relate it to the live definitions.  Source
    hashes, the exact substitutions and the per-row theorem names are recorded in
    meta/migration_reports/consecutive_in_cycle.md. *)

From GTBase Require Import base.
From GTMisc.conjectures Require Import X91.
From GTMisc.migration Require consecutive_in_path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x91_consecutive_in_cycle (G : sgraph) (c : seq G) (u v : G) : Prop :=
  (u, v) \in zip c (rot 1 c) \/ (v, u) \in zip c (rot 1 c).

End Legacy.

Module X91CycleLegacy.

Definition induced_cycle (G : sgraph) (c : seq G) : Prop :=
  ucycle (--) c /\
  3 <= size c /\
  forall u v : G,
    u \in c -> v \in c -> u -- v -> u != v ->
    Legacy.x91_consecutive_in_cycle c u v.

End X91CycleLegacy.

Module X91Legacy.

Definition avoidable_path (G : sgraph) (p : seq G) : Prop :=
  x91_induced_path p /\
  forall u v : G,
    x91_induced_path (u :: rcons p v) ->
    exists c : seq G,
      X91CycleLegacy.induced_cycle c /\ x91_sequence_contained (u :: rcons p v) c.

Definition avoidable_path_or_pk_free_statement : Prop :=
  forall k : nat,
    0 < k ->
    forall G : sgraph,
      x91_Pk_free G k \/
      exists p : seq G, size p = k /\ avoidable_path p.

End X91Legacy.

Module X91Original.

Definition avoidable_path (G : sgraph) (p : seq G) : Prop :=
  consecutive_in_path.X91Legacy.induced_path p /\
  forall u v : G,
    consecutive_in_path.X91Legacy.induced_path (u :: rcons p v) ->
    exists c : seq G,
      X91CycleLegacy.induced_cycle c /\ x91_sequence_contained (u :: rcons p v) c.

Definition avoidable_path_or_pk_free_statement : Prop :=
  forall k : nat,
    0 < k ->
    forall G : sgraph,
      consecutive_in_path.X91Legacy.Pk_free G k \/
      exists p : seq G, size p = k /\ avoidable_path p.

End X91Original.

(** ** Certificates *)

Lemma x91_consecutive_in_cycle_compat (G : sgraph) (c : seq G) (u v : G) :
  Legacy.x91_consecutive_in_cycle c u v = x91_consecutive_in_cycle c u v.
Proof. by []. Qed.

Lemma x91_induced_cycle_compat (G : sgraph) (c : seq G) :
  X91CycleLegacy.induced_cycle c <-> x91_induced_cycle c.
Proof. exact: iff_refl. Qed.

Lemma x91_avoidable_path_compat (G : sgraph) (p : seq G) :
  X91Legacy.avoidable_path p <-> x91_avoidable_path p.
Proof. exact: iff_refl. Qed.

Lemma avoidable_path_or_pk_free_statement_compat :
  X91Legacy.avoidable_path_or_pk_free_statement <-> avoidable_path_or_pk_free_statement.
Proof. exact: iff_refl. Qed.

Lemma x91_avoidable_path_original_compat (G : sgraph) (p : seq G) :
  X91Original.avoidable_path p <-> x91_avoidable_path p.
Proof. exact: iff_refl. Qed.

Lemma avoidable_path_or_pk_free_statement_original_compat :
  X91Original.avoidable_path_or_pk_free_statement <-> avoidable_path_or_pk_free_statement.
Proof. exact: iff_refl. Qed.

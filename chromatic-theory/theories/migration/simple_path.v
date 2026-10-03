(** * Chromatic.migration.simple_path — frozen simple-path chains (library migration B6)

    Batch B, family [simple-path] (meta/library_primitives/simple-path.json).
    [Legacy] freezes the helper [x126_genuine_path] verbatim as it stood at 95cba2c,
    before the migration: a nonempty sequence without repetition whose consecutive
    entries are adjacent.  The live helper now unfolds to
    [GTBase.walks_paths.seq_simple_path p], whose body is the same match, so the
    certificates below are kernel-checked conversions.  [X126Legacy] freezes the
    nonrepetitive colouring (paths on [2 * h] vertices, [0 < h]), its list version,
    Thue choosability, the least Thue choice number (bound and minimality; an
    exported helper with no row of its own) and the statement.
    Source hashes, the exact substitutions and the per-row theorem names are
    recorded in meta/migration_reports/simple_path.md. *)

From GTBase Require Import base.
From Chromatic.conjectures Require Import X126.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x126_genuine_path (G : sgraph) (p : seq G) : Prop :=
  match p with
  | [::] => False
  | x :: q => uniq p /\ path (--) x q
  end.

End Legacy.

Module X126Legacy.

Definition nonrepetitive (G : sgraph) (C : finType) (col : G -> C) : Prop :=
  forall (p : seq G) (h : nat),
    Legacy.x126_genuine_path p ->
    size p = 2 * h ->
    0 < h ->
    map col (take h p) != map col (take h (drop h p)).

Definition nonrepetitive_list_colouring
    (G : sgraph) (C : finType) (L : G -> {set C}) : Prop :=
  exists col : G -> C,
    (forall v : G, col v \in L v) /\ nonrepetitive col.

Definition thue_choosable (G : sgraph) (k : nat) : Prop :=
  forall (C : finType) (L : G -> {set C}),
    (forall v : G, k <= #|L v|) -> nonrepetitive_list_colouring L.

Definition is_thue_choice_number (G : sgraph) (k : nat) : Prop :=
  thue_choosable G k /\
  (forall k' : nat, thue_choosable G k' -> k <= k').

Definition dujmovic_thue_choice_number_pathwidth_statement : Prop :=
  exists f : nat -> nat,
    forall (p : nat) (G : sgraph),
      x126_pathwidth_at_most G p ->
      thue_choosable G (f p).

End X126Legacy.

(** ** Certificates *)

Lemma x126_genuine_path_compat (G : sgraph) (p : seq G) :
  Legacy.x126_genuine_path p = x126_genuine_path p.
Proof. by []. Qed.

Lemma x126_nonrepetitive_compat (G : sgraph) (C : finType) (col : G -> C) :
  X126Legacy.nonrepetitive col <-> x126_nonrepetitive col.
Proof. exact: iff_refl. Qed.

Lemma x126_nonrepetitive_list_colouring_compat (G : sgraph) (C : finType) (L : G -> {set C}) :
  X126Legacy.nonrepetitive_list_colouring L <-> x126_nonrepetitive_list_colouring L.
Proof. exact: iff_refl. Qed.

Lemma x126_thue_choosable_compat (G : sgraph) (k : nat) :
  X126Legacy.thue_choosable G k <-> x126_thue_choosable G k.
Proof. exact: iff_refl. Qed.

Lemma x126_is_thue_choice_number_compat (G : sgraph) (k : nat) :
  X126Legacy.is_thue_choice_number G k <-> x126_is_thue_choice_number G k.
Proof. exact: iff_refl. Qed.

Lemma dujmovic_thue_choice_number_pathwidth_statement_compat :
  X126Legacy.dujmovic_thue_choice_number_pathwidth_statement <->
  dujmovic_thue_choice_number_pathwidth_statement.
Proof. exact: iff_refl. Qed.

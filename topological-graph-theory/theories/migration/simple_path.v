(** * Topological.migration.simple_path — frozen simple-path chains (library migration B6)

    Batch B, family [simple-path] (meta/library_primitives/simple-path.json).
    [Legacy] freezes the helper [x23_genuine_path] verbatim as it stood at 95cba2c;
    the live helper now unfolds to [GTBase.walks_paths.seq_simple_path p], whose
    body is the same match, so the certificates are kernel-checked conversions.
    [X23Legacy] freezes the nonrepetitive colouring (paths on [2 * h] vertices,
    [0 < h]) and the statement.
    Source hashes, the exact substitutions and the per-row theorem names are
    recorded in meta/migration_reports/simple_path.md. *)

From GTBase Require Import base.
From Topological.conjectures Require Import X23.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x23_genuine_path (G : sgraph) (p : seq G) : Prop :=
  match p with
  | [::] => False
  | x :: q => uniq p /\ path (--) x q
  end.

End Legacy.

Module X23Legacy.

Definition nonrepetitive_colouring
    (G : sgraph) (k : nat) (col : G -> 'I_k) : Prop :=
  forall (p : seq G) (h : nat),
    Legacy.x23_genuine_path p ->
    size p = 2 * h ->
    0 < h ->
    map col (take h p) != map col (take h (drop h p)).

Definition planar_bounded_nonrepetitive_chromatic_statement : Prop :=
  exists k : nat,
    0 < k /\
    forall G : sgraph,
      wagner_planar G ->
      exists col : G -> 'I_k, nonrepetitive_colouring col.

End X23Legacy.

(** ** Certificates *)

Lemma x23_genuine_path_compat (G : sgraph) (p : seq G) :
  Legacy.x23_genuine_path p = x23_genuine_path p.
Proof. by []. Qed.

Lemma x23_nonrepetitive_colouring_compat (G : sgraph) (k : nat) (col : G -> 'I_k) :
  X23Legacy.nonrepetitive_colouring col <-> x23_nonrepetitive_colouring col.
Proof. exact: iff_refl. Qed.

Lemma planar_bounded_nonrepetitive_chromatic_statement_compat :
  X23Legacy.planar_bounded_nonrepetitive_chromatic_statement <->
  planar_bounded_nonrepetitive_chromatic_statement.
Proof. exact: iff_refl. Qed.

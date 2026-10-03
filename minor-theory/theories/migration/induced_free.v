(** * Minor.migration.induced_free -- frozen induced-free certificates

    Batch A, family [induced_free].  [Legacy] freezes the conjecture-local
    helper verbatim as it stood at 9e03072, before the migration; [X42Legacy]
    freezes the affected dependency chain, the statement included, with every
    reference to the helper replaced by its frozen copy.  The live helper now
    unfolds to [GTBase.common.induced_free]; the theorems below prove each
    frozen body equivalent to its live counterpart.  The cross-file consumer
    implications_X42.v keeps its statements; only proof steps that opened the
    old [inhabited] wrapper changed.  Source hashes and the per-row theorem
    names are recorded in meta/migration_reports/induced_free.md. *)

From GTBase Require Import base.
From Minor.conjectures Require Import X27 X42.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x42_induced_free (G H : sgraph) : Prop :=
  forall S : {set G}, ~ inhabited (induced S ≃ H).

End Legacy.

Lemma x42_induced_free_compat (G H : sgraph) :
  Legacy.x42_induced_free G H <-> x42_induced_free G H.
Proof. exact: iff_sym (induced_free_inhabited G H). Qed.

Module X42Legacy.

Definition statement : Prop :=
  exists c : nat,
    forall G : sgraph,
      x27_even_hole_free G ->
      Legacy.x42_induced_free G 'K_4 ->
      Legacy.x42_induced_free G x42_diamond ->
      x27_treewidth_at_most G c.

End X42Legacy.

Lemma x42_statement_compat :
  X42Legacy.statement <-> even_hole_k4_diamond_free_bounded_treewidth_statement.
Proof.
split=> -[c bound]; exists c => G eh k4 diamond.
- by apply: bound eh _ _; apply/x42_induced_free_compat.
- by apply: bound eh _ _; apply/x42_induced_free_compat.
Qed.

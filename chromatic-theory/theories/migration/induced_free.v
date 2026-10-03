(** * Chromatic.migration.induced_free -- frozen induced-free certificates

    Batch A, family [induced_free].  [Legacy] freezes the conjecture-local
    helper verbatim as it stood at 9e03072, before the migration; [X43Legacy]
    freezes the affected dependency chain, the statement included, with every
    reference to the helper replaced by its frozen copy.  The live helper now
    unfolds to [GTBase.common.induced_free]; the theorems below prove each
    frozen body equivalent to its live counterpart.  Source hashes and the
    per-row theorem names are recorded in meta/migration_reports/induced_free.md. *)

From GTBase Require Import base.
From Chromatic.conjectures Require Import X43.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x43_induced_free (G H : sgraph) : Prop :=
  forall S : {set G}, ~ inhabited (induced S ≃ H).

End Legacy.

Lemma x43_induced_free_compat (G H : sgraph) :
  Legacy.x43_induced_free G H <-> x43_induced_free G H.
Proof. exact: iff_sym (induced_free_inhabited G H). Qed.

Module X43Legacy.

Definition statement : Prop :=
  forall G : sgraph,
    regular G 3 ->
    Legacy.x43_induced_free G x43_diamond ->
    Legacy.x43_induced_free G x43_claw ->
    x43_strong_edge_colourable G 6.

End X43Legacy.

Lemma x43_statement_compat :
  X43Legacy.statement <->
  diamond_free_claw_free_cubic_strong_six_edge_colourable_statement.
Proof.
split=> statement G reg diamond claw.
- by apply: statement reg _ _; apply/x43_induced_free_compat.
- by apply: statement reg _ _; apply/x43_induced_free_compat.
Qed.

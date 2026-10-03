(** * Hom.migration.longest_cycle — frozen longest cycle of U3 (library migration B13)

    Batch B, family [longest-cycle] (meta/library_primitives/longest-cycle.json).  [Legacy] freezes,
    verbatim as it stood at the B13 baseline c528254, U3's [longest_cycle] ([[/\ ucycle (--) c,
    2 < size c & forall c', ucycle (--) c' -> size c' <= size c]], whose maximality ranges over ALL
    [ucycle] competitors, degenerate ones included).  The live helper now unfolds to
    [GTBase.walks_paths.seq_longest_cycle (--) c].  The certificate is the proved [and3] view
    [seq_longest_cycle_ucycleE]: a competitor with at most two entries is never longer than a genuine
    cycle.  It needs no symmetry or looplessness premise and no propositional extensionality.
    [U3Legacy] freezes the chords-of-longest-cycles row; its [chord] (both directions of a cyclic
    neighbour pair excluded) and the 3-connectivity guard stay live and unchanged.  Hashes and
    substitutions: meta/migration_reports/longest_cycle.md. *)

From GTBase Require Import base.
From Hom.conjectures Require Import U3.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition longest_cycle (G : sgraph) (c : seq G) : Prop :=
  [/\ ucycle (--) c, 2 < size c &
      forall c' : seq G, ucycle (--) c' -> size c' <= size c].

End Legacy.

Module U3Legacy.

Definition chords_of_longest_cycles_statement : Prop :=
  forall G : sgraph, k_connected G 3 ->
    forall c : seq G, Legacy.longest_cycle c -> chord c.

End U3Legacy.

(** ** Certificates *)

(** The [and3] body over all [ucycle] competitors is the canonical's [and3] view. *)
Lemma longest_cycle_compat (G : sgraph) (c : seq G) : Legacy.longest_cycle c <-> longest_cycle c.
Proof. exact: iff_sym (seq_longest_cycle_ucycleE _ c). Qed.

(** opg:chords_of_longest_cycles (unchanged). *)
Lemma chords_of_longest_cycles_statement_compat :
  U3Legacy.chords_of_longest_cycles_statement <-> chords_of_longest_cycles_statement.
Proof. by split=> H G kc c lc; apply: H => //; apply/longest_cycle_compat. Qed.

Print Assumptions longest_cycle_compat.
Print Assumptions chords_of_longest_cycles_statement_compat.

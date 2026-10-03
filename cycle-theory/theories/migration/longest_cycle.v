(** * Cycle.migration.longest_cycle — frozen longest-cycle helpers of X10 and X212 (library migration
    B13)

    Batch B, family [longest-cycle] (meta/library_primitives/longest-cycle.json).  [Legacy] freezes,
    verbatim as they stood at the B13 baseline c528254, X10's [x10_longest_cycle] (nested [ucycle] /
    size / maximality over genuine competitors with curried premises) and X212's [x212_longest_cycle]
    (the Boolean [x212_cycle] and maximality).  Both live helpers now unfold to
    [GTBase.walks_paths.seq_longest_cycle (--) c], whose body is the Boolean genuine-cycle maximum.
    X212's certificates are conversions.  X10's go through [seq_longest_cycle_nestedE], a proved iff,
    not a conversion.  [X10Legacy] and [X212Legacy] freeze the two Smith rows with this family's
    helpers only.

    History.
    - [X10Original] (B12+B13) is the complete X10 Smith row: B12's frozen support
      [Cycle.migration.cycle_vertices.Legacy.x10_cycle_vertices] with this family's frozen pre-B13
      longest body.
    - X212's complete row is B12's [Cycle.migration.cycle_vertices.X212Original] (B10+B12: B10's
      frozen pre-B10 cycle and longest body, B12's frozen support), reused unchanged; its certificate
      is restated below.
    - The B12 per-row Smith snapshots still call the live longest helpers and are documented in both
      specs.
    Hashes and substitutions: meta/migration_reports/longest_cycle.md. *)

From GTBase Require Import base.
From Cycle.conjectures Require Import X10 X212.
From Cycle.migration Require cycle_vertices.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** B12's frozen copies, without Import. *)
Module B12 := Cycle.migration.cycle_vertices.

Module Legacy.

Definition x10_longest_cycle (G : sgraph) (c : seq G) : Prop :=
  ucycle (--) c /\ 2 < size c /\
  forall c' : seq G, ucycle (--) c' -> 2 < size c' -> size c' <= size c.

Definition x212_longest_cycle (G : sgraph) (c : seq G) : Prop :=
  x212_cycle c /\ forall c' : seq G, x212_cycle c' -> size c' <= size c.

End Legacy.

Module X10Legacy.

Definition smith_longest_cycles_r_connected_statement : Prop :=
  forall (r : nat) (G : sgraph) (c d : seq G),
    2 <= r ->
    k_connected G r ->
    @Legacy.x10_longest_cycle G c ->
    @Legacy.x10_longest_cycle G d ->
    r <= #|@x10_cycle_vertices G c :&: @x10_cycle_vertices G d|.

End X10Legacy.

Module X10Original.

Definition smith_longest_cycles_r_connected_statement : Prop :=
  forall (r : nat) (G : sgraph) (c d : seq G),
    2 <= r ->
    k_connected G r ->
    @Legacy.x10_longest_cycle G c ->
    @Legacy.x10_longest_cycle G d ->
    r <= #|@B12.Legacy.x10_cycle_vertices G c :&: @B12.Legacy.x10_cycle_vertices G d|.

End X10Original.

Module X212Legacy.

Definition smith_two_longest_cycles_statement : Prop :=
  forall (k : nat) (G : sgraph) (c d : seq G),
    2 <= k -> k_connected G k ->
    Legacy.x212_longest_cycle c -> Legacy.x212_longest_cycle d ->
    k <= #|x212_cycle_vertices c :&: x212_cycle_vertices d|.

End X212Legacy.

(** ** Certificates *)

(** X10's nested body is the nested view of the canonical (a proved iff, not a conversion). *)
Lemma x10_longest_cycle_compat (G : sgraph) (c : seq G) :
  Legacy.x10_longest_cycle c <-> x10_longest_cycle c.
Proof. exact: iff_sym (seq_longest_cycle_nestedE _ c). Qed.

(** X212's Boolean body is the canonical's, by conversion. *)
Lemma x212_longest_cycle_compat (G : sgraph) (c : seq G) :
  Legacy.x212_longest_cycle c <-> x212_longest_cycle c.
Proof. exact: iff_refl. Qed.

Lemma smith_longest_cycles_r_connected_statement_compat :
  X10Legacy.smith_longest_cycles_r_connected_statement <-> smith_longest_cycles_r_connected_statement.
Proof. by split=> H r G c d r2 kc lc ld; apply: H => //; apply/x10_longest_cycle_compat. Qed.

(** Before B12 and B13: B12's frozen support and this family's frozen longest body. *)
Lemma smith_longest_cycles_r_connected_statement_original_compat :
  X10Original.smith_longest_cycles_r_connected_statement <-> smith_longest_cycles_r_connected_statement.
Proof. by split=> H r G c d r2 kc lc ld; apply: H => //; apply/x10_longest_cycle_compat. Qed.

Lemma smith_two_longest_cycles_statement_compat :
  X212Legacy.smith_two_longest_cycles_statement <-> smith_two_longest_cycles_statement.
Proof. exact: iff_refl. Qed.

(** Before B10 and B12, and so before B13: B12's complete Original, restated. *)
Lemma smith_two_longest_cycles_statement_original_compat :
  Cycle.migration.cycle_vertices.X212Original.smith_two_longest_cycles_statement <->
  smith_two_longest_cycles_statement.
Proof. exact: Cycle.migration.cycle_vertices.smith_two_longest_cycles_statement_original_compat. Qed.

Print Assumptions x10_longest_cycle_compat.
Print Assumptions x212_longest_cycle_compat.
Print Assumptions smith_longest_cycles_r_connected_statement_compat.
Print Assumptions smith_longest_cycles_r_connected_statement_original_compat.
Print Assumptions smith_two_longest_cycles_statement_compat.
Print Assumptions smith_two_longest_cycles_statement_original_compat.

(** * Cycle.migration.cycle_vertices — frozen vertex supports of X10, X212 and X5 (library migration
    B12)

    Batch B, family [cycle-vertices] (meta/library_primitives/cycle-vertices.json).  The family reuses
    B1's canonical [GTBase.walks_paths.seq_vertices] (registry path-vertices) and adds no primitive,
    fidelity owner or validity guard.  [Legacy] freezes, verbatim as they stood at the B12 baseline
    13c00aa, X10's and X212's [[set v | v \in c]] and X5's [[set v : G | v \in c]].  The live helpers
    now unfold to [seq_vertices c], MathComp's [[set:: c]], which is the same comprehension, so every
    certificate is a kernel-checked conversion; the helper certificates go through [seq_verticesE], as
    in B1.  [X10Legacy] and [X212Legacy] freeze the two Smith rows.  [X5Legacy] freezes the
    disjoint-family chain, #577 and #916.  All of them use this family's helpers only.

    History.  [X212Original] (B10+B12) is the complete Smith row of X212.  It uses B10's frozen
    longest-cycle chain [Cycle.migration.genuine_cycle.X212Legacy.longest_cycle], over B10's frozen
    Boolean cycle, and this family's frozen support.  B10's X212Legacy row is unchanged; it still calls
    the live support and is documented in both specs.  #916 keeps the live [x5_edge_count]: A7 (edge
    counts) is not integrated at this baseline, so whichever of A7 and B12 integrates second owes the
    complete A7+B12 #916 Original.  Hashes and substitutions: meta/migration_reports/cycle_vertices.md. *)

From GTBase Require Import base.
From Cycle.conjectures Require Import X10 X212 X5.
From Cycle.migration Require genuine_cycle.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** B10's frozen copies, without Import. *)
Module B10 := Cycle.migration.genuine_cycle.

Module Legacy.

Definition x10_cycle_vertices (G : sgraph) (c : seq G) : {set G} :=
  [set v | v \in c].

Definition x212_cycle_vertices (G : sgraph) (c : seq G) : {set G} := [set v | v \in c].

Definition x5_vertices_of_seq (G : sgraph) (c : seq G) : {set G} :=
  [set v : G | v \in c].

End Legacy.

Module X10Legacy.

Definition smith_longest_cycles_r_connected_statement : Prop :=
  forall (r : nat) (G : sgraph) (c d : seq G),
    2 <= r ->
    k_connected G r ->
    @x10_longest_cycle G c ->
    @x10_longest_cycle G d ->
    r <= #|@Legacy.x10_cycle_vertices G c :&: @Legacy.x10_cycle_vertices G d|.

End X10Legacy.

Module X212Legacy.

Definition smith_two_longest_cycles_statement : Prop :=
  forall (k : nat) (G : sgraph) (c d : seq G),
    2 <= k -> k_connected G k ->
    x212_longest_cycle c -> x212_longest_cycle d ->
    k <= #|Legacy.x212_cycle_vertices c :&: Legacy.x212_cycle_vertices d|.

End X212Legacy.

Module X212Original.

Definition smith_two_longest_cycles_statement : Prop :=
  forall (k : nat) (G : sgraph) (c d : seq G),
    2 <= k -> k_connected G k ->
    B10.X212Legacy.longest_cycle c -> B10.X212Legacy.longest_cycle d ->
    k <= #|Legacy.x212_cycle_vertices c :&: Legacy.x212_cycle_vertices d|.

End X212Original.

Module X5Legacy.

Definition cycle_family_disjoint
    (G : sgraph) (k : nat) (cs : 'I_k -> seq G) : Prop :=
  forall i j : 'I_k, i != j ->
    [disjoint Legacy.x5_vertices_of_seq (cs i) & Legacy.x5_vertices_of_seq (cs j)].

Definition min_degree_half_disjoint_four_cycles_statement : Prop :=
  forall (k : nat) (G : sgraph),
    #|G| = 4 * k ->
    (forall v : G, 2 * k <= #|N(v)|) ->
    exists cs : 'I_k -> seq G,
      (forall i : 'I_k, ucycle (--) (cs i) /\ size (cs i) = 4) /\
      cycle_family_disjoint cs.

Definition cycle_with_external_three_neighbours_statement : Prop :=
  forall (n : nat) (G : sgraph),
    2 <= n ->
    #|G| = n ->
    x5_edge_count G = 2 * n - 2 ->
    exists (c : seq G) (v : G),
      ucycle (--) c /\
      2 < size c /\
      v \notin c /\
      3 <= #|N(v) :&: Legacy.x5_vertices_of_seq c|.

End X5Legacy.

(** ** Certificates *)

Lemma x10_cycle_vertices_compat (G : sgraph) (c : seq G) :
  Legacy.x10_cycle_vertices c = x10_cycle_vertices c.
Proof. by rewrite /x10_cycle_vertices seq_verticesE. Qed.

Lemma x212_cycle_vertices_compat (G : sgraph) (c : seq G) :
  Legacy.x212_cycle_vertices c = x212_cycle_vertices c.
Proof. by rewrite /x212_cycle_vertices seq_verticesE. Qed.

Lemma x5_vertices_of_seq_compat (G : sgraph) (c : seq G) :
  Legacy.x5_vertices_of_seq c = x5_vertices_of_seq c.
Proof. by rewrite /x5_vertices_of_seq seq_verticesE. Qed.

Lemma smith_longest_cycles_r_connected_statement_compat :
  X10Legacy.smith_longest_cycles_r_connected_statement <-> smith_longest_cycles_r_connected_statement.
Proof. exact: iff_refl. Qed.

Lemma smith_two_longest_cycles_statement_compat :
  X212Legacy.smith_two_longest_cycles_statement <-> smith_two_longest_cycles_statement.
Proof. exact: iff_refl. Qed.

(** Before B10 and B12: B10's frozen longest-cycle chain and this family's frozen support. *)
Lemma smith_two_longest_cycles_statement_original_compat :
  X212Original.smith_two_longest_cycles_statement <-> smith_two_longest_cycles_statement.
Proof. exact: iff_refl. Qed.

Lemma x5_cycle_family_disjoint_compat (G : sgraph) (k : nat) (cs : 'I_k -> seq G) :
  X5Legacy.cycle_family_disjoint cs <-> x5_cycle_family_disjoint cs.
Proof. exact: iff_refl. Qed.

Lemma min_degree_half_disjoint_four_cycles_statement_compat :
  X5Legacy.min_degree_half_disjoint_four_cycles_statement <-> min_degree_half_disjoint_four_cycles_statement.
Proof. exact: iff_refl. Qed.

Lemma cycle_with_external_three_neighbours_statement_compat :
  X5Legacy.cycle_with_external_three_neighbours_statement <-> cycle_with_external_three_neighbours_statement.
Proof. exact: iff_refl. Qed.

Print Assumptions x10_cycle_vertices_compat.
Print Assumptions x212_cycle_vertices_compat.
Print Assumptions x5_vertices_of_seq_compat.
Print Assumptions smith_longest_cycles_r_connected_statement_compat.
Print Assumptions smith_two_longest_cycles_statement_compat.
Print Assumptions smith_two_longest_cycles_statement_original_compat.
Print Assumptions min_degree_half_disjoint_four_cycles_statement_compat.
Print Assumptions cycle_with_external_three_neighbours_statement_compat.

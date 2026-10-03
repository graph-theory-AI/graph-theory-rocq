(** * Cycle.migration.consecutive_in_cycle — frozen cyclic-adjacency chain (library migration B4)

    Batch B, family [consecutive-in-cycle]
    (meta/library_primitives/consecutive-in-cycle.json).  [Legacy] freezes the
    conjecture-local boolean helper [x9_consecutive_in_cycle] verbatim as it stood at
    49ddc03, before the migration; the live helper now unfolds to
    [GTBase.walks_paths.seq_cyclic_consecutiveb c u v], whose body is the same
    disjunction.  [X9Legacy] freezes the chord count (unordered pairs ranked by
    [enum_rank]) and the statement; the certificates are kernel-checked
    conversions.  Source hashes, the exact substitutions and the per-row theorem
    names are recorded in meta/migration_reports/consecutive_in_cycle.md. *)

From GTBase Require Import base.
From Cycle.conjectures Require Import X9.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x9_consecutive_in_cycle (G : sgraph) (c : seq G) (u v : G) : bool :=
  ((u, v) \in zip c (rot 1 c)) || ((v, u) \in zip c (rot 1 c)).

End Legacy.

Module X9Legacy.

Definition cycle_chord_count (G : sgraph) (c : seq G) : nat :=
  #|[set p : G * G |
      [&& p.1 \in c, p.2 \in c, (enum_rank p.1 < enum_rank p.2)%N,
          p.1 -- p.2 & ~~ Legacy.x9_consecutive_in_cycle c p.1 p.2]]|.

Definition min_degree_three_linearly_many_chords_cycle_statement : Prop :=
  exists cnum cden : nat,
    0 < cnum /\ 0 < cden /\
    forall G : sgraph,
      0 < #|G| ->
      (forall v : G, 3 <= #|N(v)|) ->
      exists c : seq G,
        @x9_genuine_cycle G c /\
        cden * @cycle_chord_count G c >= cnum * size c.

End X9Legacy.

(** ** Certificates *)

Lemma x9_consecutive_in_cycle_compat (G : sgraph) (c : seq G) (u v : G) :
  Legacy.x9_consecutive_in_cycle c u v = x9_consecutive_in_cycle c u v.
Proof. by []. Qed.

Lemma x9_cycle_chord_count_compat (G : sgraph) (c : seq G) :
  X9Legacy.cycle_chord_count c = x9_cycle_chord_count c.
Proof. by []. Qed.

Lemma min_degree_three_linearly_many_chords_cycle_statement_compat :
  X9Legacy.min_degree_three_linearly_many_chords_cycle_statement <->
  min_degree_three_linearly_many_chords_cycle_statement.
Proof. exact: iff_refl. Qed.

(** * GTMisc.migration.induced_cycles — B23 certificates: X91's induced cycle and its row

    Frozen verbatim at the fixed B22 baseline 7d8cc47: X91's induced cycle [x91_induced_cycle]
    ([ucycle], [3 <= size c], and a chord clause with a redundant [u != v] premise after the edge
    premise and the consecutiveness as a proposition through B4's live [x91_consecutive_in_cycle]),
    its chain [x91_avoidable_path] and the complete row [avoidable_path_or_pk_free_statement]
    ([0 < k]; no induced k-vertex path, or one whose every induced two-ended extension lies in an
    induced cycle).  Since B23 the live [x91_induced_cycle] is a transparent alias of
    [GTBase.induced_cycles.chordless_cycle]; [2 < size c] and [3 <= size c] are the same term, but
    the chord clauses are not convertible, so [x91_induced_cycle_compat] is an explicit iff through
    [cyclic_chordless_prop_edge_neq].  The copies keep the other families' live aliases
    ([x91_induced_path] and [x91_Pk_free] of B22, [x91_sequence_contained]).

    B22's snapshots [GTMisc.migration.induced_paths.X91Legacy.x91_avoidable_path] and
    [X91Legacy.avoidable_path_or_pk_free_statement] deliberately keep the live [x91_induced_cycle]
    and stay unchanged; B3's [GTMisc.migration.consecutive_in_path.X91Legacy] snapshots likewise.
    The complete row with both families frozen is B4's
    [X91Original.avoidable_path_or_pk_free_statement] (B3's frozen paths and B4's frozen cycle),
    reused with B4's certificate; no duplicate Original is added. *)

From GTBase Require Import base induced_paths induced_cycles.
From GTMisc.conjectures Require Import X91.
From GTMisc.migration Require consecutive_in_cycle.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module B4 := GTMisc.migration.consecutive_in_cycle.

Module Legacy.

Definition x91_induced_cycle (G : sgraph) (c : seq G) : Prop :=
  ucycle (--) c /\
  3 <= size c /\
  forall u v : G,
    u \in c -> v \in c -> u -- v -> u != v ->
    x91_consecutive_in_cycle c u v.

End Legacy.

Module X91Legacy.

Definition x91_avoidable_path (G : sgraph) (p : seq G) : Prop :=
  x91_induced_path p /\
  forall u v : G,
    x91_induced_path (u :: rcons p v) ->
    exists c : seq G,
      Legacy.x91_induced_cycle c /\ x91_sequence_contained (u :: rcons p v) c.

Definition avoidable_path_or_pk_free_statement : Prop :=
  forall k : nat,
    0 < k ->
    forall G : sgraph,
      x91_Pk_free G k \/
      exists p : seq G, size p = k /\ X91Legacy.x91_avoidable_path p.

End X91Legacy.

(** ** The induced cycle: an explicit iff with the canonical genuine view *)

Lemma x91_induced_cycle_compat (G : sgraph) (c : seq G) :
  Legacy.x91_induced_cycle c <-> x91_induced_cycle c.
Proof.
rewrite /x91_induced_cycle; split=> -[uc [sz ch]].
- split=> //; split=> //; apply/cyclic_chordless_prop_edge_neq.
  move=> u v uc' vc' uv nuv; exact: (ch u v uc' vc' uv nuv).
- split=> //; split=> // u v uc' vc' uv nuv.
  exact: (proj2 (cyclic_chordless_prop_edge_neq c) ch u v uc' vc' uv nuv).
Qed.

Lemma x91_avoidable_path_compat (G : sgraph) (p : seq G) :
  X91Legacy.x91_avoidable_path p <-> x91_avoidable_path p.
Proof.
split=> -[ip h]; split=> // u v ip'; have [c [hc sc]] := h u v ip'; exists c; split=> //;
  by apply/x91_induced_cycle_compat.
Qed.

Lemma avoidable_path_or_pk_free_statement_compat :
  X91Legacy.avoidable_path_or_pk_free_statement <-> avoidable_path_or_pk_free_statement.
Proof.
split=> h k k0 G; case: (h k k0 G) => [pk | [p [sp ap]]];
  first [by left | by right; exists p; split=> //; apply/x91_avoidable_path_compat].
Qed.

(** ** The complete earlier row, reused from B4 with B4's own certificate *)

Lemma avoidable_path_or_pk_free_statement_original_compat :
  GTMisc.migration.consecutive_in_cycle.X91Original.avoidable_path_or_pk_free_statement <->
  avoidable_path_or_pk_free_statement.
Proof. exact: B4.avoidable_path_or_pk_free_statement_original_compat. Qed.

Print Assumptions x91_induced_cycle_compat.
Print Assumptions x91_avoidable_path_compat.
Print Assumptions avoidable_path_or_pk_free_statement_compat.
Print Assumptions avoidable_path_or_pk_free_statement_original_compat.

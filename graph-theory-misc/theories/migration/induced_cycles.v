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
From GTMisc.conjectures Require Import X91 U13.
From GTMisc.migration Require consecutive_in_cycle monochromatic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module B4 := GTMisc.migration.consecutive_in_cycle.
Module C8 := GTMisc.migration.monochromatic.

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

(** ** B24: U13's ordinal-map induced cycle and the maximum-clique colouring row

    Frozen verbatim at the fixed B23 baseline (byte-identical at B22 7d8cc47): U13's ordinal-map
    induced cycle [induced_cycle] (an injective map ['I_k -> G] whose images are adjacent exactly
    for cyclically consecutive positions, equal positions included: order 0 vacuous, order 1
    impossible, order 2 an edge), its existential wrapper [has_induced_cycle], and the complete
    current row [two_colouring_a_graph_without_a_monochromatic_maximu_statement] (a nonempty
    graph, every odd length at least 5 excluded, a Boolean colouring under which no
    MAXIMUM-cardinality clique is monochromatic).  Since B24 the two sources are transparent
    aliases of [GTBase.induced_cycles.ordinal_induced_cycle] and [has_ordinal_induced_cycle], the
    same bodies by conversion, so their certificates and the current row's are kernel-checked
    conversions.  The row copy keeps C8's live [splits_max_cliques] (with the live
    [is_max_clique], [monochromatic] and the upstream clique number).  [U13Original] freezes the row
    end to end over B24's frozen map and wrapper and C8's frozen [splits_max_cliques] /
    [monochromatic] chain; its certificate composes C8's [splits_max_cliques_compat].  C8's own
    snapshot [GTMisc.migration.monochromatic.U13Legacy] keeps the live [has_induced_cycle] and stays
    unchanged.  The recorded C8 readback concern (the [0 < #|G|] guard admits [K_1]) is not
    repaired here. *)

Module U13CycleLegacy.

Definition induced_cycle (G : sgraph) (k : nat) (f : 'I_k -> G) : Prop :=
  injective f /\
  forall i j : 'I_k,
    (f i -- f j) <-> ((val j == (val i).+1 %% k) || (val i == (val j).+1 %% k)).

Definition has_induced_cycle (G : sgraph) (k : nat) : Prop :=
  exists f : 'I_k -> G, U13CycleLegacy.induced_cycle f.

End U13CycleLegacy.

Module U13RowLegacy.

Definition two_colouring_a_graph_without_a_monochromatic_maximu_statement : Prop :=
  forall G : sgraph,
    0 < #|G| ->
    (forall k : nat, odd k -> 5 <= k -> ~ U13CycleLegacy.has_induced_cycle G k) ->
    exists c : G -> bool, splits_max_cliques c.

End U13RowLegacy.

Module U13Original.

Definition two_colouring_a_graph_without_a_monochromatic_maximu_statement : Prop :=
  forall G : sgraph,
    0 < #|G| ->
    (forall k : nat, odd k -> 5 <= k -> ~ U13CycleLegacy.has_induced_cycle G k) ->
    exists c : G -> bool, C8.U13Legacy.splits_max_cliques c.

End U13Original.

Lemma induced_cycle_compat (G : sgraph) (k : nat) (f : 'I_k -> G) :
  U13CycleLegacy.induced_cycle f <-> induced_cycle f.
Proof. exact: iff_refl. Qed.

Lemma has_induced_cycle_compat (G : sgraph) (k : nat) :
  U13CycleLegacy.has_induced_cycle G k <-> has_induced_cycle G k.
Proof. exact: iff_refl. Qed.

Lemma two_colouring_a_graph_without_a_monochromatic_maximu_statement_compat :
  U13RowLegacy.two_colouring_a_graph_without_a_monochromatic_maximu_statement <->
  two_colouring_a_graph_without_a_monochromatic_maximu_statement.
Proof. exact: iff_refl. Qed.

Lemma two_colouring_a_graph_without_a_monochromatic_maximu_statement_original_compat :
  U13Original.two_colouring_a_graph_without_a_monochromatic_maximu_statement <->
  two_colouring_a_graph_without_a_monochromatic_maximu_statement.
Proof.
split=> h G ne odd_cycles; have [c hc] := h G ne odd_cycles; exists c.
- by apply/C8.splits_max_cliques_compat.
- by apply/C8.splits_max_cliques_compat.
Qed.

Print Assumptions x91_induced_cycle_compat.
Print Assumptions x91_avoidable_path_compat.
Print Assumptions avoidable_path_or_pk_free_statement_compat.
Print Assumptions avoidable_path_or_pk_free_statement_original_compat.
Print Assumptions induced_cycle_compat.
Print Assumptions has_induced_cycle_compat.
Print Assumptions two_colouring_a_graph_without_a_monochromatic_maximu_statement_compat.
Print Assumptions two_colouring_a_graph_without_a_monochromatic_maximu_statement_original_compat.

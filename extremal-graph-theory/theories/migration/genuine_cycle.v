(** * Extremal.migration.genuine_cycle — frozen genuine cycle of XE2 #767 (library migration B10)

    Batch B, family [genuine-cycle] (meta/library_primitives/genuine-cycle.json).
    [Legacy] freezes XE2's [xe2_cycle] verbatim as it stood at the B10 baseline
    00d6bb3 ([ucycle (--) c /\ 2 < size c]); the live helper now unfolds to
    [GTBase.walks_paths.seq_cycle (--) c], so the certificates are kernel-checked
    conversions.  [XE2Legacy] freezes the incident-chord chain and #767 with this
    family's helper only.  [XE2Original] gives the complete row before B4 and B10:
    B4's frozen incident chord count (Extremal.migration.consecutive_in_cycle.XE2Legacy)
    with this family's frozen cycle; B4's XE2Legacy chain is unchanged.  The edge
    count [x4_edge_count] stays live: family A7 (edge counts) is not integrated, and
    whichever of A7 / B10 integrates second composes the shared #767 history.
    Hashes and substitutions: meta/migration_reports/genuine_cycle.md. *)

From GTBase Require Import base.
From Extremal.conjectures Require Import X4 XE2.
From Extremal.migration Require consecutive_in_cycle.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition xe2_cycle (G : sgraph) (c : seq G) : Prop :=
  ucycle (--) c /\ 2 < size c.

End Legacy.

Module XE2Legacy.

Definition no_cycle_with_incident_chords (G : sgraph) (k : nat) : Prop :=
  forall c : seq G, Legacy.xe2_cycle c ->
    forall v : G, v \in c -> xe2_incident_cycle_chord_count c v < k.

Definition incident_chord_extremal (k n m : nat) : Prop :=
  (exists G : sgraph,
      #|G| = n /\ x4_edge_count G = m /\
      no_cycle_with_incident_chords G k) /\
  forall m' : nat,
    (exists G : sgraph,
      #|G| = n /\ x4_edge_count G = m' /\
      no_cycle_with_incident_chords G k) ->
    m' <= m.

Definition erdos_767_statement : Prop :=
  forall k : nat, exists N : nat,
    forall (n m : nat),
      N <= n ->
      incident_chord_extremal k n m ->
      m = (k + 1) * n - (k + 1) ^ 2.

End XE2Legacy.

Module XE2Original.

Definition no_cycle_with_incident_chords (G : sgraph) (k : nat) : Prop :=
  forall c : seq G, Legacy.xe2_cycle c ->
    forall v : G, v \in c -> Extremal.migration.consecutive_in_cycle.XE2Legacy.incident_cycle_chord_count c v < k.

Definition incident_chord_extremal (k n m : nat) : Prop :=
  (exists G : sgraph,
      #|G| = n /\ x4_edge_count G = m /\
      no_cycle_with_incident_chords G k) /\
  forall m' : nat,
    (exists G : sgraph,
      #|G| = n /\ x4_edge_count G = m' /\
      no_cycle_with_incident_chords G k) ->
    m' <= m.

Definition erdos_767_statement : Prop :=
  forall k : nat, exists N : nat,
    forall (n m : nat),
      N <= n ->
      incident_chord_extremal k n m ->
      m = (k + 1) * n - (k + 1) ^ 2.

End XE2Original.

(** ** Certificates *)

Lemma xe2_cycle_compat (G : sgraph) (c : seq G) : Legacy.xe2_cycle c = xe2_cycle c.
Proof. by []. Qed.

Lemma xe2_no_cycle_with_incident_chords_compat (G : sgraph) (k : nat) :
  XE2Legacy.no_cycle_with_incident_chords G k <-> xe2_no_cycle_with_incident_chords G k.
Proof. exact: iff_refl. Qed.

Lemma xe2_incident_chord_extremal_compat (k n m : nat) :
  XE2Legacy.incident_chord_extremal k n m <-> xe2_incident_chord_extremal k n m.
Proof. exact: iff_refl. Qed.

Lemma erdos_767_statement_compat : XE2Legacy.erdos_767_statement <-> erdos_767_statement.
Proof. exact: iff_refl. Qed.

(** Before B4 and B10: B4's frozen incident chord count and this family's frozen cycle. *)
Lemma xe2_no_cycle_with_incident_chords_original_compat (G : sgraph) (k : nat) :
  XE2Original.no_cycle_with_incident_chords G k <-> xe2_no_cycle_with_incident_chords G k.
Proof. exact: iff_refl. Qed.

Lemma xe2_incident_chord_extremal_original_compat (k n m : nat) :
  XE2Original.incident_chord_extremal k n m <-> xe2_incident_chord_extremal k n m.
Proof. exact: iff_refl. Qed.

Lemma erdos_767_statement_original_compat : XE2Original.erdos_767_statement <-> erdos_767_statement.
Proof. exact: iff_refl. Qed.

Print Assumptions xe2_cycle_compat.
Print Assumptions xe2_no_cycle_with_incident_chords_compat.
Print Assumptions xe2_incident_chord_extremal_compat.
Print Assumptions erdos_767_statement_compat.
Print Assumptions xe2_no_cycle_with_incident_chords_original_compat.
Print Assumptions xe2_incident_chord_extremal_original_compat.
Print Assumptions erdos_767_statement_original_compat.

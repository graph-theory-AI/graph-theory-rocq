(** * GTBase.examples.induced_cycles — public-only client of GTBase.induced_cycles (B23)

    Compiles against the public module alone (no conjecture module).  It separates the three views
    on concrete graphs: the empty list and the two-vertex cycle of an edge are chordless ucycles but
    not chordless cycles; a triangle is a chordless cycle but not a hole; the four-cycle of
    [cycle_graph 4] is a hole; the four-cycle of ['K_4] is a [ucycle] of size four with a chord and is
    rejected.  Positive facts are shown both through the API lemmas and by computation with the
    Boolean mirrors; rotation and reversal transport the hole. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph.
From GTBase Require Import base induced_cycles.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The empty list: a raw chordless ucycle, not a genuine cycle *)

Lemma example_nil_raw : chordless_ucycle (G := 'K_2) [::].
Proof. exact: chordless_ucycle_nil. Qed.

Lemma example_nil_not_genuine : ~ chordless_cycle (G := 'K_2) [::].
Proof. exact: chordless_cycle_nil. Qed.

Lemma example_nil_computes : chordless_ucycleb (G := 'K_2) [::] && ~~ chordless_cycleb (G := 'K_2) [::].
Proof. by vm_compute. Qed.

(** ** The edge of ['K_2]: a raw two-vertex cycle, rejected by the genuine view *)

Local Notation k2_0 := (@Ordinal 2 0 isT).
Local Notation k2_1 := (@Ordinal 2 1 isT).

Lemma example_K2_edge : (k2_0 : 'K_2) -- k2_1.
Proof. by []. Qed.

Lemma example_K2_raw : chordless_ucycle (G := 'K_2) [:: k2_0; k2_1].
Proof. exact: chordless_ucycle_pair example_K2_edge. Qed.

Lemma example_K2_raw_computes : chordless_ucycle (G := 'K_2) [:: k2_0; k2_1].
Proof. by apply/chordless_ucycleP; vm_compute. Qed.

Lemma example_K2_not_genuine : ~ chordless_cycle (G := 'K_2) [:: k2_0; k2_1].
Proof. exact: chordless_cycle_pair. Qed.

Lemma example_K2_not_genuine_computes : ~~ chordless_cycleb (G := 'K_2) [:: k2_0; k2_1].
Proof. by vm_compute. Qed.

Lemma example_K2_not_hole : ~ hole (G := 'K_2) [:: k2_0; k2_1].
Proof. exact: hole_small. Qed.

(** ** The triangle of ['K_3]: a genuine chordless cycle, not a hole *)

Local Notation k3_0 := (@Ordinal 3 0 isT).
Local Notation k3_1 := (@Ordinal 3 1 isT).
Local Notation k3_2 := (@Ordinal 3 2 isT).

Lemma example_K3_genuine : chordless_cycle (G := 'K_3) [:: k3_0; k3_1; k3_2].
Proof. by apply: chordless_cycle_triangle. Qed.

Lemma example_K3_genuine_computes : chordless_cycle (G := 'K_3) [:: k3_0; k3_1; k3_2].
Proof. by apply/chordless_cycleP; vm_compute. Qed.

Lemma example_K3_not_hole : ~ hole (G := 'K_3) [:: k3_0; k3_1; k3_2].
Proof. exact: hole_triangle. Qed.

Lemma example_K3_not_hole_computes : ~~ holeb (G := 'K_3) [:: k3_0; k3_1; k3_2].
Proof. by vm_compute. Qed.

(** ** The four-cycle [C_4]: a hole *)

Local Notation c4_0 := (@Ordinal 4 0 isT).
Local Notation c4_1 := (@Ordinal 4 1 isT).
Local Notation c4_2 := (@Ordinal 4 2 isT).
Local Notation c4_3 := (@Ordinal 4 3 isT).

Definition c4 : seq (cycle_graph 4) := [:: c4_0; c4_1; c4_2; c4_3].

Lemma example_C4_hole : hole c4.
Proof. by apply/holeP; vm_compute. Qed.

Lemma example_C4_genuine : chordless_cycle c4.
Proof. exact: hole_chordless_cycle example_C4_hole. Qed.

Lemma example_C4_raw : chordless_ucycle c4.
Proof. exact: hole_chordless_ucycle example_C4_hole. Qed.

(** Rotation and reversal keep the hole. *)
Lemma example_C4_rot : hole (rot 1 c4).
Proof. by apply/hole_rot; exact: example_C4_hole. Qed.

Lemma example_C4_rev : hole (rev c4).
Proof. by apply/hole_rev; exact: example_C4_hole. Qed.

Lemma example_C4_rev_computes : holeb (rev c4).
Proof. by vm_compute. Qed.

(** ** The chorded four-cycle of ['K_4]: a [ucycle] of size four, rejected *)

Local Notation k4_0 := (@Ordinal 4 0 isT).
Local Notation k4_1 := (@Ordinal 4 1 isT).
Local Notation k4_2 := (@Ordinal 4 2 isT).
Local Notation k4_3 := (@Ordinal 4 3 isT).

Definition chorded4 : seq 'K_4 := [:: k4_0; k4_1; k4_2; k4_3].

Lemma example_chorded_ucycle : ucycle (--) chorded4 /\ size chorded4 = 4.
Proof. by split; vm_compute. Qed.

(** The chord [k4_0 -- k4_2] is a host edge between two non-consecutive entries. *)
Lemma example_chord : (k4_0 : 'K_4) -- k4_2 /\ ~ seq_cyclic_consecutive chorded4 k4_0 k4_2.
Proof. by split=> [|[]]; vm_compute. Qed.

Lemma example_chorded_not_chordless : ~ cyclic_chordless chorded4.
Proof. by move/cyclic_chordlessP; vm_compute. Qed.

Lemma example_chorded_not_hole : ~ hole chorded4.
Proof. by move/holeP; vm_compute. Qed.

Lemma example_chorded_not_raw : ~ chordless_ucycle chorded4.
Proof. by move/chordless_ucycleP; vm_compute. Qed.

Print Assumptions example_K2_raw.
Print Assumptions example_K3_genuine.
Print Assumptions example_C4_hole.
Print Assumptions example_C4_rev.
Print Assumptions example_chorded_not_hole.

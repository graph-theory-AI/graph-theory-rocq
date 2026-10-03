(** * Extremal.migration.induced_cycles — B23 certificates: D2str's raw induced cycle

    Frozen verbatim at the fixed B22 baseline 7d8cc47: D2str's induced cycle [induced_cycle] (a
    [ucycle] whose host edges between its vertices are all cycle edges [cyc_edge], B4's live
    Boolean cyclic consecutiveness; NO length guard, so the empty list and the two-vertex cycle of
    an edge qualify), its chain [peripheral_cycle] and the complete OPG row
    [geodesic_cycles_and_tuttes_theorem_statement] (every [R : realFieldType], 3-connectivity,
    the existential edge-length assignment and the universal geodesic-cycle clause).  Since B23
    the live [induced_cycle] is a transparent alias of [GTBase.induced_cycles.chordless_ucycle],
    the same body by conversion ([cyc_edge c x y] is [seq_cyclic_consecutiveb c x y]), so every
    certificate below is a kernel-checked conversion; in particular no size guard is added.  The
    copies keep [cyc_edge], [geodesic_cycle], [edge_length] and [k_connected] live.  The complete
    pre-B4 row is B4's [D2strLegacy.geodesic_cycles_and_tuttes_theorem_statement] (raw pair
    formula), reused with B4's certificate. *)

From GTBase Require Import base induced_cycles.
From mathcomp Require Import all_algebra.
From Extremal.conjectures Require Import D2str.
From Extremal.migration Require consecutive_in_cycle.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module B4 := Extremal.migration.consecutive_in_cycle.

Module Legacy.

Definition induced_cycle (G : sgraph) (c : seq G) : Prop :=
  ucycle (--) c /\
  forall x y : G, x \in c -> y \in c -> x -- y -> cyc_edge c x y.

End Legacy.

Module D2strLegacy.

Definition peripheral_cycle (G : sgraph) (c : seq G) : Prop :=
  Legacy.induced_cycle c /\ connected (~: [set x in c]).

Definition geodesic_cycles_and_tuttes_theorem_statement : Prop :=
  forall (R : realFieldType) (G : sgraph),
    k_connected G 3 ->
    exists ell : G -> G -> R,
      edge_length ell /\
      (forall c : seq G, geodesic_cycle ell c -> D2strLegacy.peripheral_cycle c).

End D2strLegacy.

(** ** Certificates (conversions) *)

Lemma induced_cycle_compat (G : sgraph) (c : seq G) : Legacy.induced_cycle c <-> induced_cycle c.
Proof. exact: iff_refl. Qed.

Lemma peripheral_cycle_compat (G : sgraph) (c : seq G) :
  D2strLegacy.peripheral_cycle c <-> peripheral_cycle c.
Proof. exact: iff_refl. Qed.

Lemma geodesic_cycles_and_tuttes_theorem_statement_compat :
  D2strLegacy.geodesic_cycles_and_tuttes_theorem_statement <->
  geodesic_cycles_and_tuttes_theorem_statement.
Proof. exact: iff_refl. Qed.

(** ** The complete earlier row, reused from B4 with B4's own certificate *)

Lemma geodesic_cycles_and_tuttes_theorem_statement_original_compat :
  Extremal.migration.consecutive_in_cycle.D2strLegacy.geodesic_cycles_and_tuttes_theorem_statement <->
  geodesic_cycles_and_tuttes_theorem_statement.
Proof. exact: B4.geodesic_cycles_and_tuttes_theorem_statement_compat. Qed.

Print Assumptions induced_cycle_compat.
Print Assumptions peripheral_cycle_compat.
Print Assumptions geodesic_cycles_and_tuttes_theorem_statement_compat.
Print Assumptions geodesic_cycles_and_tuttes_theorem_statement_original_compat.

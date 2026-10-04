(** * Packing.migration.chordal — B25 certificates: XE1's cycle chordality and Erdos #81

    Frozen verbatim at the fixed B24 baseline 63be197: XE1's [xe1_chordal] (every induced cycle in
    XE1's sense, B23's alias of the public genuine [chordless_cycle], has at most three vertices) and
    the complete current row [erdos_81_statement] (a uniform constant [C] before [G] and [n], the
    exact cardinality [#|G| = n], a supplied family [K : 'I_m -> {set G}] that is a clique edge
    partition, and [6 * m <= n ^ 2 + C * n]; no minimization and no nonempty guard).  Since B25 the
    live [xe1_chordal] is a transparent alias of [GTBase.chordal.chordal_by_cycles], the same body by
    conversion, so both certificates below are kernel-checked conversions.  The copies keep B23's
    live [xe1_induced_cycle] and the unrelated M1 clique edge-partition vocabulary
    ([xe1_clique_edge_partition] over [xe1_edge_set]); no pre-M1 Original exists.  The complete
    earlier row is B23's [Packing.migration.induced_cycles.XE1Legacy.erdos_81_statement] (over B23's
    raw [Legacy.xe1_induced_cycle] and [XE1Legacy.xe1_chordal]), reused with B23's certificate. *)

From GTBase Require Import base induced_cycles chordal.
From Packing.conjectures Require Import XE1.
From Packing.migration Require induced_cycles.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module B23 := Packing.migration.induced_cycles.

Module Legacy.

Definition xe1_chordal (G : sgraph) : Prop :=
  forall c : seq G, xe1_induced_cycle c -> size c <= 3.

End Legacy.

Module XE1Legacy.

Definition erdos_81_statement : Prop :=
  exists C : nat,
    forall (G : sgraph) (n : nat),
      #|G| = n -> Legacy.xe1_chordal G ->
      exists m : nat, exists K : 'I_m -> {set G},
        xe1_clique_edge_partition K /\
        6 * m <= n ^ 2 + C * n.

End XE1Legacy.

Lemma xe1_chordal_compat (G : sgraph) : Legacy.xe1_chordal G <-> xe1_chordal G.
Proof. exact: iff_refl. Qed.

Lemma erdos_81_statement_compat : XE1Legacy.erdos_81_statement <-> erdos_81_statement.
Proof. exact: iff_refl. Qed.

(** The complete earlier row, reused from B23 with B23's own certificate. *)
Lemma erdos_81_statement_original_compat :
  Packing.migration.induced_cycles.XE1Legacy.erdos_81_statement <-> erdos_81_statement.
Proof. exact: B23.erdos_81_statement_compat. Qed.

Print Assumptions xe1_chordal_compat.
Print Assumptions erdos_81_statement_compat.
Print Assumptions erdos_81_statement_original_compat.

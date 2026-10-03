(** * Chromatic.migration.genuine_cycle — frozen genuine cycles of the chromatic XE1/XE2 rows
    (library migration B10)

    Batch B, family [genuine-cycle] (meta/library_primitives/genuine-cycle.json).
    [Legacy] freezes XE1's [xe1_cycle] verbatim as it stood at the B10 baseline
    00d6bb3: [ucycle (--) c /\ 2 < size c].  The live helper now unfolds to
    [GTBase.walks_paths.seq_cycle (--) c], whose body is that conjunction, so the
    per-row certificates are kernel-checked conversions.  [XE1Legacy] / [XE2Legacy]
    freeze the odd-cycle-with-diagonals chain, the cross-file odd cycle length and
    separated cycle length predicates, and erdos_58, 751 and 1091 with this family's
    helper only.

    History.  [XE1Original] / [XE2Original] give the complete rows before A5, B4 and
    B10: erdos_1091 over A5's frozen [xe1_subgraph_of]
    (Chromatic.migration.subgraph_of.Legacy), B4's frozen diagonal count
    (Chromatic.migration.consecutive_in_cycle.XE1Legacy) and this family's frozen
    cycle; erdos_58 over A5's frozen subgraph helper and this family's frozen odd cycle
    lengths.  They are convertible with A5's own row certificates, which they reuse.
    Earlier partial snapshots (B4's XE1Legacy.odd_cycle_with_diagonals, A5's
    XE2Legacy.erdos_1091 / erdos_58 and A5's XE2Original.erdos_1091) are unchanged.
    Hashes and substitutions: meta/migration_reports/genuine_cycle.md. *)

From GTBase Require Import base.
From Chromatic.conjectures Require Import XE1 XE2.
From Chromatic.migration Require subgraph_of consecutive_in_cycle.

(** A5's certificate module, aliased so that frozen references read [A5.Legacy.xe1_subgraph_of]. *)
Module A5 := Chromatic.migration.subgraph_of.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition xe1_cycle (G : sgraph) (c : seq G) : Prop :=
  ucycle (--) c /\ 2 < size c.

End Legacy.

Module XE1Legacy.

Definition odd_cycle_with_diagonals (G : sgraph) (d : nat) : Prop :=
  exists c : seq G,
    Legacy.xe1_cycle c /\ odd (size c) /\ d <= xe1_cycle_diagonal_count c.

End XE1Legacy.

Module XE2Legacy.

Definition odd_cycle_lengths_bounded (G : sgraph) (k : nat) : Prop :=
  exists L : seq nat,
    uniq L /\ size L <= k /\
    forall c : seq G, Legacy.xe1_cycle c -> odd (size c) -> size c \in L.

Definition cycle_lengths_separated (G : sgraph) (gap : nat) : Prop :=
  forall c d : seq G,
    Legacy.xe1_cycle c -> Legacy.xe1_cycle d -> size c != size d ->
    gap <= (size c - size d) + (size d - size c).

Definition erdos_58_statement : Prop :=
  forall (G : sgraph) (k : nat),
    odd_cycle_lengths_bounded G k ->
    χ([set: G]) <= 2 * k + 2 /\
    (χ([set: G]) = 2 * k + 2 <-> xe1_subgraph_of 'K_(2 * k + 2) G).

Definition erdos_751_statement : Prop :=
  forall gap g : nat,
    exists G : sgraph,
      χ([set: G]) = 4 /\
      girth_geq G g /\
      cycle_lengths_separated G gap.

Definition erdos_1091_statement : Prop :=
  (forall G : sgraph,
    ~ xe1_subgraph_of 'K_4 G ->
    χ([set: G]) = 4 ->
    XE1Legacy.odd_cycle_with_diagonals G 2) /\
  exists f : nat -> nat,
    xe1_unbounded f /\
    forall (r : nat) (G : sgraph),
      ~ xe1_subgraph_of 'K_4 G ->
      χ([set: G]) = 4 ->
      xe1_induced_subgraph_chi_le G r 3 ->
      XE1Legacy.odd_cycle_with_diagonals G (f r).

End XE2Legacy.

Module XE1Original.

Definition odd_cycle_with_diagonals (G : sgraph) (d : nat) : Prop :=
  exists c : seq G,
    Legacy.xe1_cycle c /\ odd (size c) /\ d <= Chromatic.migration.consecutive_in_cycle.XE1Legacy.cycle_diagonal_count c.

End XE1Original.

Module XE2Original.

Definition erdos_1091_statement : Prop :=
  (forall G : sgraph,
    ~ A5.Legacy.xe1_subgraph_of 'K_4 G ->
    χ([set: G]) = 4 ->
    XE1Original.odd_cycle_with_diagonals G 2) /\
  exists f : nat -> nat,
    xe1_unbounded f /\
    forall (r : nat) (G : sgraph),
      ~ A5.Legacy.xe1_subgraph_of 'K_4 G ->
      χ([set: G]) = 4 ->
      xe1_induced_subgraph_chi_le G r 3 ->
      XE1Original.odd_cycle_with_diagonals G (f r).

Definition erdos_58_statement : Prop :=
  forall (G : sgraph) (k : nat),
    XE2Legacy.odd_cycle_lengths_bounded G k ->
    χ([set: G]) <= 2 * k + 2 /\
    (χ([set: G]) = 2 * k + 2 <-> A5.Legacy.xe1_subgraph_of 'K_(2 * k + 2) G).

End XE2Original.

(** ** Certificates *)

Lemma xe1_cycle_compat (G : sgraph) (c : seq G) : Legacy.xe1_cycle c = xe1_cycle c.
Proof. by []. Qed.

Lemma xe1_odd_cycle_with_diagonals_compat (G : sgraph) (d : nat) :
  XE1Legacy.odd_cycle_with_diagonals G d <-> xe1_odd_cycle_with_diagonals G d.
Proof. exact: iff_refl. Qed.

Lemma xe2_odd_cycle_lengths_bounded_compat (G : sgraph) (k : nat) :
  XE2Legacy.odd_cycle_lengths_bounded G k <-> xe2_odd_cycle_lengths_bounded G k.
Proof. exact: iff_refl. Qed.

Lemma xe2_cycle_lengths_separated_compat (G : sgraph) (gap : nat) :
  XE2Legacy.cycle_lengths_separated G gap <-> xe2_cycle_lengths_separated G gap.
Proof. exact: iff_refl. Qed.

Lemma erdos_58_statement_compat : XE2Legacy.erdos_58_statement <-> erdos_58_statement.
Proof. exact: iff_refl. Qed.

Lemma erdos_751_statement_compat : XE2Legacy.erdos_751_statement <-> erdos_751_statement.
Proof. exact: iff_refl. Qed.

Lemma erdos_1091_statement_compat : XE2Legacy.erdos_1091_statement <-> erdos_1091_statement.
Proof. exact: iff_refl. Qed.

(** Before B4 and B10: B4's frozen diagonal count and this family's frozen cycle. *)
Lemma xe1_odd_cycle_with_diagonals_original_compat (G : sgraph) (d : nat) :
  XE1Original.odd_cycle_with_diagonals G d <-> xe1_odd_cycle_with_diagonals G d.
Proof. exact: iff_refl. Qed.

(** Before A5, B4 and B10: convertible with A5's own complete-row certificate. *)
Lemma erdos_1091_statement_original_compat :
  XE2Original.erdos_1091_statement <-> erdos_1091_statement.
Proof. exact: Chromatic.migration.subgraph_of.erdos_1091_statement_original_compat. Qed.

(** Before A5 and B10: convertible with A5's row certificate. *)
Lemma erdos_58_statement_original_compat : XE2Original.erdos_58_statement <-> erdos_58_statement.
Proof. exact: Chromatic.migration.subgraph_of.erdos_58_statement_compat. Qed.

Print Assumptions xe1_cycle_compat.
Print Assumptions xe1_odd_cycle_with_diagonals_compat.
Print Assumptions xe2_odd_cycle_lengths_bounded_compat.
Print Assumptions xe2_cycle_lengths_separated_compat.
Print Assumptions erdos_58_statement_compat.
Print Assumptions erdos_751_statement_compat.
Print Assumptions erdos_1091_statement_compat.
Print Assumptions xe1_odd_cycle_with_diagonals_original_compat.
Print Assumptions erdos_1091_statement_original_compat.
Print Assumptions erdos_58_statement_original_compat.

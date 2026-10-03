(** * Digraph.migration.genuine_cycle — frozen directed cycles of XE2 #1006 (library migration B10)

    Batch B, family [genuine-cycle] (meta/library_primitives/genuine-cycle.json),
    generic supplied-relation class.  [Legacy] freezes XE2's [xe2_directed_cycle]
    verbatim as it stood at the B10 baseline 00d6bb3: [ucycle r c /\ 2 < size c] for an
    arbitrary relation [r] on a finite carrier, here an orientation.  The live helper
    now unfolds to [GTBase.walks_paths.seq_cycle r c], so the certificates are
    kernel-checked conversions; no symmetry is assumed, which is what keeps directed
    cycles directed.  [XE2Legacy] freezes acyclicity of a relation, the one-reversal
    property and #1006.  No earlier migration froze these rows.  Hashes and
    substitutions: meta/migration_reports/genuine_cycle.md. *)

From GTBase Require Import base.
From Digraph.conjectures Require Import XE2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition xe2_directed_cycle (V : finType) (r : rel V) (c : seq V) : Prop :=
  ucycle r c /\ 2 < size c.

End Legacy.

Module XE2Legacy.

Definition acyclic_rel (V : finType) (r : rel V) : Prop :=
  forall c : seq V, ~ Legacy.xe2_directed_cycle r c.

Definition orientation_stays_acyclic_after_one_reversal
    (G : sgraph) (r : rel G) : Prop :=
  acyclic_rel r /\
  forall a b : G, r a b ->
    acyclic_rel (xe2_reverse_one_edge r a b).

Definition erdos_1006_statement : Prop :=
  forall G : sgraph,
    girth_geq G 5 ->
    exists r : rel G,
      xe2_uses_only_edges r /\
      xe2_orients_edge r /\
      orientation_stays_acyclic_after_one_reversal r.

End XE2Legacy.

(** ** Certificates *)

Lemma xe2_directed_cycle_compat (V : finType) (r : rel V) (c : seq V) :
  Legacy.xe2_directed_cycle r c = xe2_directed_cycle r c.
Proof. by []. Qed.

Lemma xe2_acyclic_rel_compat (V : finType) (r : rel V) :
  XE2Legacy.acyclic_rel r <-> xe2_acyclic_rel r.
Proof. exact: iff_refl. Qed.

Lemma xe2_orientation_stays_acyclic_after_one_reversal_compat (G : sgraph) (r : rel G) :
  XE2Legacy.orientation_stays_acyclic_after_one_reversal r <->
  xe2_orientation_stays_acyclic_after_one_reversal r.
Proof. exact: iff_refl. Qed.

Lemma erdos_1006_statement_compat : XE2Legacy.erdos_1006_statement <-> erdos_1006_statement.
Proof. exact: iff_refl. Qed.

Print Assumptions xe2_directed_cycle_compat.
Print Assumptions erdos_1006_statement_compat.

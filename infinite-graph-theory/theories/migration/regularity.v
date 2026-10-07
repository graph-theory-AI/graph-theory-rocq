(** * D9: local neighbourhood regularity of an infinite graph, Infinite certificate

    Bound at the regularity family baseline 7e030f252c859c5334185673b10b69971cab9402, the effective commit;
    frozen at the D8 pin 216204c1dfe3a483cc952446ff1f494397ccc7a8 (descriptive), where the source and its
    whole dependency closure are byte-identical (meta/migration_reports/regularity.spec.json).
    - [Legacy]: D4inf3's [regular], verbatim, on the existing [Infinite.foundations.igraph] carrier.  The
      source now unfolds to the public [Infinite.foundations.regularity.iregular], the same local injective
      ordinal-neighbour enumeration.
    - [D4inf3Legacy]: the complete existential row over the frozen [regular]: both outer existentials and all
      five conjuncts, with the live unmigrated local supports [locally_finite], [one_ended] and
      [uniquely_hamiltonian] (the documented spanning-double-ray proxy). *)
From mathcomp Require Import all_boot.
From Infinite Require Import foundations.igraph.
Require Infinite.foundations.regularity.
Require Infinite.conjectures.D4inf3.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition regular (r : nat) (G : iGraph) : Prop :=
  forall x : iV G, exists e : 'I_r -> iV G,
    injective e /\ (forall w, iadj x w <-> exists i, e i = w).

End Legacy.

Module D4inf3Legacy.
Import Infinite.conjectures.D4inf3.

Definition infinite_uniquely_hamiltonian_graphs_statement : Prop :=
  exists (G : iGraph) (r : nat),
    [/\ 2 < r, locally_finite G, Legacy.regular r G, one_ended G & uniquely_hamiltonian G].

End D4inf3Legacy.

(** Both bridges are conversions: the live [regular] unfolds to the same enumeration predicate. *)

Lemma regular_compat (r : nat) (G : iGraph) :
  Legacy.regular r G <->
  Infinite.conjectures.D4inf3.regular r G.
Proof. exact: iff_refl. Qed.

Lemma infinite_uniquely_hamiltonian_graphs_statement_compat :
  D4inf3Legacy.infinite_uniquely_hamiltonian_graphs_statement <->
  Infinite.conjectures.D4inf3.infinite_uniquely_hamiltonian_graphs_statement.
Proof. exact: iff_refl. Qed.

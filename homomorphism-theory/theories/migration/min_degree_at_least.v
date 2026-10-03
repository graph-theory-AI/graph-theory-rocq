(** A11 minimum-degree lower bounds (Hom): the frozen X135 bound and its row.
    The bound converts to [GTBase.base.min_degree_at_least].
    Baseline, hashes and exact substitutions are recorded in meta/migration_reports/min_degree_at_least.spec.json. *)
From GTBase Require Import base.
From Hom.conjectures Require Import X135.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x135_min_degree_at_least (G : sgraph) (delta : nat) : Prop :=
  forall v : G, delta <= #|N(v)|.

End Legacy.

Module X135Legacy.

Definition engbers_homomorphism_count_maximisation_statement : Prop :=
  forall (delta : nat) (H : sgraph),
    1 <= delta ->
    exists N : nat,
      forall (n : nat) (G : sgraph),
        N <= n ->
        #|G| = n ->
        Legacy.x135_min_degree_at_least G delta ->
        (x135_hom_count G H) ^ x135_power_denominator delta
          <= x135_engbers_bound delta n H.

End X135Legacy.

Lemma x135_min_degree_at_least_compat (G : sgraph) (delta : nat) :
  Legacy.x135_min_degree_at_least G delta <->
  x135_min_degree_at_least G delta.
Proof. exact: iff_refl. Qed.

Lemma engbers_homomorphism_count_maximisation_statement_compat :
  X135Legacy.engbers_homomorphism_count_maximisation_statement <->
  engbers_homomorphism_count_maximisation_statement.
Proof. exact: iff_refl. Qed.

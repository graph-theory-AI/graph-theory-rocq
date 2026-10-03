(** A11 minimum-degree lower bounds (cycle): the frozen XE2 bound and row erdos:752.
    The bound converts to [GTBase.base.min_degree_at_least]; guards and quantifiers are unchanged.
    Baseline, hashes and exact substitutions are recorded in meta/migration_reports/min_degree_at_least.spec.json. *)
From GTBase Require Import base.
From Cycle.conjectures Require Import XE2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition xe2_min_degree_at_least (G : sgraph) (k : nat) : Prop :=
  forall v : G, k <= #|N(v)|.

End Legacy.

Module XE2Legacy.

Definition erdos_752_statement : Prop :=
  forall s : nat, 1 <= s ->
    exists C k0 : nat,
      0 < C /\
      forall (k : nat) (G : sgraph),
        0 < #|G| ->
        k0 <= k ->
        Legacy.xe2_min_degree_at_least G k ->
        girth_geq G (2 * s).+1 ->
        exists L : seq nat, xe2_cycle_lengths G L /\ k ^ s <= C * size L.

End XE2Legacy.

Lemma xe2_min_degree_at_least_compat (G : sgraph) (k : nat) :
  Legacy.xe2_min_degree_at_least G k <->
  xe2_min_degree_at_least G k.
Proof. exact: iff_refl. Qed.

Lemma erdos_752_statement_compat :
  XE2Legacy.erdos_752_statement <->
  erdos_752_statement.
Proof. exact: iff_refl. Qed.

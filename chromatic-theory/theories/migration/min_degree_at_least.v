(** A11 minimum-degree lower bounds (chromatic): the frozen X203 bound and its row.
    The bound converts to [GTBase.base.min_degree_at_least].  The row is frozen verbatim, with its
    documented empty-graph defect: ['K_0] satisfies every bound, so the row stays blocked.
    Baseline, hashes and exact substitutions are recorded in meta/migration_reports/min_degree_at_least.spec.json. *)
From GTBase Require Import base.
From Chromatic.conjectures Require Import X203.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x203_min_degree_at_least (G : sgraph) (d : nat) : Prop :=
  forall v : G, d <= #|N(v)|.

End Legacy.

Module X203Legacy.

Definition separation_choosability_min_degree_unbounded_statement : Prop :=
  exists x : nat -> nat,
    (forall B : nat, exists d : nat, B <= x d) /\
    forall (d : nat) (G : sgraph),
      Legacy.x203_min_degree_at_least G d ->
      x203_separation_choosability_at_least G (x d).

End X203Legacy.

Lemma x203_min_degree_at_least_compat (G : sgraph) (d : nat) :
  Legacy.x203_min_degree_at_least G d <->
  x203_min_degree_at_least G d.
Proof. exact: iff_refl. Qed.

Lemma separation_choosability_min_degree_unbounded_statement_compat :
  X203Legacy.separation_choosability_min_degree_unbounded_statement <->
  separation_choosability_min_degree_unbounded_statement.
Proof. exact: iff_refl. Qed.

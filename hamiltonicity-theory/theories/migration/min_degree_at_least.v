(** A11 minimum-degree lower bounds (Hamilton): the frozen X211 bound and its row.
    The bound converts to [GTBase.base.min_degree_at_least].
    Baseline, hashes and exact substitutions are recorded in meta/migration_reports/min_degree_at_least.spec.json. *)
From GTBase Require Import base.
From Hamilton.conjectures Require Import X211.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x211_min_degree_geq (G : sgraph) (d : nat) : Prop :=
  forall v : G, d <= #|N(v)|.

End Legacy.

Module X211Legacy.

Definition hypohamiltonian_minimum_degree_four_statement : Prop :=
  exists G : sgraph, Legacy.x211_min_degree_geq G 4 /\ x211_hypohamiltonian G.

End X211Legacy.

Lemma x211_min_degree_geq_compat (G : sgraph) (d : nat) :
  Legacy.x211_min_degree_geq G d <->
  x211_min_degree_geq G d.
Proof. exact: iff_refl. Qed.

Lemma hypohamiltonian_minimum_degree_four_statement_compat :
  X211Legacy.hypohamiltonian_minimum_degree_four_statement <->
  hypohamiltonian_minimum_degree_four_statement.
Proof. exact: iff_refl. Qed.

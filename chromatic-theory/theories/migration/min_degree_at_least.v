(** A11 minimum-degree lower bounds (chromatic): the frozen X203 bound and its row.
    The bound converts to [GTBase.base.min_degree_at_least].  The row is frozen verbatim, with its
    documented empty-graph defect: ['K_0] satisfies every bound ([X203Legacy_row_false]).
    - X203 source repair (2026-10-26, coordination/PROGRAMME.md A2; record meta/STATEMENT_IMPROVEMENTS.md): the live
      row asks for graphs with at least one vertex ([0 < #|G|]).  Its certificate is a ONE-WAY source-repair
      certificate [frozen -> live] (direction "weaken"), not a migration equivalence; the bound keeps its exact iff.
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

(** X203 SOURCE REPAIR (2026-10-26, PROGRAMME A2; record meta/STATEMENT_IMPROVEMENTS.md), not a migration
    equivalence.  The frozen row quantifies over every graph, so the empty graph ['K_0], which satisfies every
    minimum-degree bound and is separation j-choosable for every j (the empty colouring), refutes it once some
    x d is positive.  The live row adds the guard [0 < #|G|]; its certificate is ONE-WAY, [frozen -> live]
    (direction "weaken"), with the same x: the guard is one more hypothesis. *)
Lemma x203_K0_separation_choosable (j : nat) : x203_separation_choosable 'K_0 j.
Proof.
move=> C L _.
have f : 'K_0 -> C by case=> m hm; exfalso; move: hm; rewrite ltn0.
by exists f; split=> [[m hm]|[m hm]]; exfalso; move: hm; rewrite ltn0.
Qed.

Lemma x203_K0_min_degree (d : nat) : Legacy.x203_min_degree_at_least 'K_0 d.
Proof. by case=> m hm; exfalso; move: hm; rewrite ltn0. Qed.

Lemma X203Legacy_row_false : ~ X203Legacy.separation_choosability_min_degree_unbounded_statement.
Proof.
move=> [x [hx h]].
have [d hd] := hx 1.
have := h d 'K_0 (x203_K0_min_degree d) 0 hd.
by apply; exact: x203_K0_separation_choosable.
Qed.

Lemma separation_choosability_min_degree_unbounded_statement_compat :
  X203Legacy.separation_choosability_min_degree_unbounded_statement ->
  separation_choosability_min_degree_unbounded_statement.
Proof. by move=> [x [hx h]]; exists x; split=> // d G _ hd; apply: h. Qed.

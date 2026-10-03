(** * Frozen monochromatic subsets and complete reaching statements (C8)
    Original source: 47eed16, before C8. Every frozen body below preserves
    the original binders, guards and witnesses; only the recorded family
    references are redirected to other frozen bodies. Existing source
    discrepancies and partial/blocked statuses are not repaired. *)
From GTBase Require Import base monochromatic.
From GTMisc.conjectures Require Import U13.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module U13Legacy.

Definition monochromatic (G : sgraph) (c : G -> bool) (Q : {set G}) : Prop :=
  {in Q &, forall x y : G, c x = c y}.

Definition splits_max_cliques (G : sgraph) (c : G -> bool) : Prop :=
  forall Q : {set G}, is_max_clique Q -> ~ U13Legacy.monochromatic c Q.

Definition two_colouring_a_graph_without_a_monochromatic_maximu_statement : Prop :=
  forall G : sgraph,
    0 < #|G| ->
    (forall k : nat, odd k -> 5 <= k -> ~ has_induced_cycle G k) ->
    exists c : G -> bool, U13Legacy.splits_max_cliques c.

End U13Legacy.

Lemma monochromatic_compat (G : sgraph) (col : G -> bool) (S : {set G}) :
  U13Legacy.monochromatic col S <-> GTMisc.conjectures.U13.monochromatic col S.
Proof.
rewrite /U13Legacy.monochromatic /U13.monochromatic.
by split=> [h|/monochromatic_onP h]; [apply/monochromatic_onP | ].
Qed.

Lemma splits_max_cliques_compat (G : sgraph) (col : G -> bool) :
  U13Legacy.splits_max_cliques col <-> splits_max_cliques col.
Proof.
split=> h Q maxq mono; apply: (h Q maxq).
- by apply/monochromatic_compat.
- by apply/monochromatic_compat.
Qed.

Lemma two_colouring_a_graph_without_a_monochromatic_maximu_statement_compat :
  U13Legacy.two_colouring_a_graph_without_a_monochromatic_maximu_statement <->
  two_colouring_a_graph_without_a_monochromatic_maximu_statement.
Proof.
by split=> h G nonempty odd_cycles; have [col hc] := h G nonempty odd_cycles;
  exists col; apply/splits_max_cliques_compat.
Qed.

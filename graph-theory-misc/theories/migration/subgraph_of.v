(** * GTMisc.migration.subgraph_of -- frozen ordinary subgraph containment certificates

    Batch A, family A5 (ordinary [subgraph_of] containment), U13 and the misc XE2 row.
    [Legacy] freezes the two helpers verbatim as they stood at 49ddc03: U13's
    [subgraph_of] ([exists f : H -> G, injective f /\ is_hom f]) and [xe2_subgraph_of].
    [U13Legacy] and [XE2Legacy] freeze the two affected statements.

    The live helpers now unfold to [GTBase.common.has_subgraph G H], host first (the
    reverse of the local argument order).  [has_subgraphP] proves the unconditional
    witness characterization, so each helper certificate is that iff, and every chain
    and statement certificate transports it through the unchanged statement structure
    by setoid rewriting under the logical connectives.  The local [and3]/[and4]
    instances only add the [[/\ ...]] forms; no axiom is used.  The regeneration spec
    is meta/migration_reports/subgraph_of.spec.json. *)

From GTBase Require Import base.
From GTMisc.conjectures Require Import U13 XE2.
From Corelib Require Import Setoid Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

#[local] Instance and3_iff_morphism : Proper (iff ==> iff ==> iff ==> iff) and3.
Proof. by move=> a a' ha b b' hb c c' hc; split=> -[x y z]; split; by [apply/ha|apply/hb|apply/hc]. Qed.

#[local] Instance and4_iff_morphism : Proper (iff ==> iff ==> iff ==> iff ==> iff) and4.
Proof.
move=> a a' ha b b' hb c c' hc d d' hd; split=> -[x y z w]; split;
  by [apply/ha|apply/hb|apply/hc|apply/hd].
Qed.

Module Legacy.

Definition subgraph_of (H G : sgraph) : Prop :=
  exists f : H -> G, injective f /\ is_hom f.

Definition xe2_subgraph_of (H G : sgraph) : Prop :=
  exists f : H -> G, injective f /\ forall x y : H, x -- y -> f x -- f y.

End Legacy.

Module U13Legacy.

Definition subgraph_of_large_average_degree_and_large_average_d_statement : Prop :=
  forall g k : nat,
    0 < g -> 0 < k ->
    exists d : nat,
      forall G : sgraph,
        0 < #|G| ->
        avgdeg_geq G d ->
        exists H : sgraph,
          [/\ 0 < #|H|, Legacy.subgraph_of H G, avgdeg_geq H k & girth_geq H g.+1].

End U13Legacy.

Module XE2Legacy.

Definition erdos_715_statement : Prop :=
  (forall G : sgraph, 0 < #|G| -> regular G 4 ->
      exists H : sgraph, 0 < #|H| /\ Legacy.xe2_subgraph_of H G /\ regular H 3) /\
  (exists r : nat, 3 < r /\
      forall G : sgraph, 0 < #|G| -> regular G r ->
        exists H : sgraph, 0 < #|H| /\ Legacy.xe2_subgraph_of H G /\ regular H 3).

End XE2Legacy.

(** ** Certificates *)

Lemma subgraph_of_compat (H G : sgraph) :
  Legacy.subgraph_of H G <-> subgraph_of H G.
Proof. exact: iff_sym (has_subgraphP G H). Qed.

Lemma xe2_subgraph_of_compat (H G : sgraph) :
  Legacy.xe2_subgraph_of H G <-> xe2_subgraph_of H G.
Proof. exact: iff_sym (has_subgraphP G H). Qed.

Lemma subgraph_of_large_average_degree_and_large_average_d_statement_compat :
  U13Legacy.subgraph_of_large_average_degree_and_large_average_d_statement <-> subgraph_of_large_average_degree_and_large_average_d_statement.
Proof. rewrite /U13Legacy.subgraph_of_large_average_degree_and_large_average_d_statement /subgraph_of_large_average_degree_and_large_average_d_statement; try setoid_rewrite subgraph_of_compat; reflexivity. Qed.

Lemma erdos_715_statement_compat :
  XE2Legacy.erdos_715_statement <-> erdos_715_statement.
Proof. rewrite /XE2Legacy.erdos_715_statement /erdos_715_statement; try setoid_rewrite xe2_subgraph_of_compat; reflexivity. Qed.

Print Assumptions subgraph_of_compat.
Print Assumptions xe2_subgraph_of_compat.
Print Assumptions subgraph_of_large_average_degree_and_large_average_d_statement_compat.
Print Assumptions erdos_715_statement_compat.

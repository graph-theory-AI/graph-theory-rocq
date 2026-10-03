(** A13 multigraph regularity (cycle): the frozen U6 loopless cubic contract, U10's reached chain
    [cubic_bridgeless], the seven U6/U10 rows and the two explicit external reductions of implications_U6
    (non-corpus declarations).  Baseline, hashes and exact substitutions are recorded in
    meta/migration_reports/mregular.spec.json.
    - [Legacy.cubic] is the original [loopless G /\ forall v, mdeg v = 3], with arc-end degrees (a loop would
      count twice).  The live [cubic] is [GTBase.base.loopless_cubic], incidence degrees under the same loopless
      guard; [cubic_compat] is an unconditional iff through [mdeg_loopless], applied to the guard it carries.
    - Every row keeps its nonempty-vertex/edge, connectivity, bridgeless, fixed-S/circuit, multiplicity-two,
      size five/six and oddness conditions; the bridges rewrite the cubic contract under the binders. *)
From Corelib Require Import Setoid Morphisms.
From GTBase Require Import base.
From GraphTheory Require Import mgraph.
From Cycle.foundations Require Import connectivity.
(* implications_U6 re-exports GTBase.base, whose common lemma [perfect_matching_cover] would shadow U10's
   definition; importing it first lets U6 and U10 names win. *)
From Cycle.conjectures Require Import implications_U6 U6 U10.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition cubic (G : mgraph) : Prop :=
  loopless G /\ forall v : G, mdeg v = 3.

End Legacy.

Module U6Legacy.

Definition cycle_double_covers_containing_predefined_2_regular_statement : Prop :=
  forall (G : mgraph) (S : {set edge G}),
    (0 < #|G|)%N -> Legacy.cubic G -> two_connected G ->
    subgraph_kregular S 2 -> connected_del_edges S ->
    exists L : seq {set edge G},
      cdc L /\
      exists D : seq {set edge G},
        cycle_decomposition_of S D /\ {subset D <= L}.

Definition three_decomposition_statement : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> Legacy.cubic G -> mconnected G ->
    exists T F M : {set edge G},
      [/\ spanning_tree T, subgraph_kregular F 2, is_matching M
        & edge_partitionT [:: T; F; M]].

Definition odd_cycles_and_low_oddness_statement : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> Legacy.cubic G -> bridgeless G ->
    (forall F : {set edge G}, two_factor F ->
       forall C : {set edge G}, C \subset F -> is_circuit C -> odd #|C|) ->
    oddness_le G 2.

Definition strong_5_cycle_double_cover_statement : Prop :=
  forall (G : mgraph) (C : {set edge G}),
    (0 < #|G|)%N -> Legacy.cubic G -> bridgeless G -> is_circuit C ->
    exists L : seq {set edge G},
      [/\ size L = 5,
          (forall D, D \in L -> even_subgraph D),
          (forall e : edge G, count (fun D : {set edge G} => e \in D) L = 2)
        & (exists D, D \in L /\ C \subset D)].

End U6Legacy.

Module U10Legacy.

Definition cubic_bridgeless (G : mgraph) : Prop := Legacy.cubic G /\ bridgeless G.

Definition intersecting_two_perfect_matchings_statement : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> U10Legacy.cubic_bridgeless G ->
    exists M1 M2 : {set edge G},
      [/\ is_perfect_matching M1, is_perfect_matching M2
        & ~ contains_odd_edge_cut (M1 :&: M2)].

Definition petersen_coloring_statement : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> U10Legacy.cubic_bridgeless G ->
    exists f : edge G -> Pedge,
      forall e1 e2 e3 : edge G,
        mut_adj3 (@line_rel G) e1 e2 e3 ->
        mut_adj3 Padj (f e1) (f e2) (f e3).

Definition the_berge_fulkerson_statement : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> U10Legacy.cubic_bridgeless G ->
    exists L : seq {set edge G}, perfect_matching_cover 6 L.

End U10Legacy.

Module ImplicationsU6Legacy.

Definition external_cdc_cubic_2connected_reduction_statement : Prop :=
  (forall G : mgraph,
     (0 < #|G|)%N -> Legacy.cubic G -> two_connected G ->
     exists L : seq {set edge G}, cdc L) ->
  cycle_double_cover_statement.

Definition external_five_even_cover_cubic_reduction_statement : Prop :=
  (forall G : mgraph,
     (0 < #|G|)%N -> (0 < #|edge G|)%N -> Legacy.cubic G -> bridgeless G ->
     u6_five_even_cover G) ->
  (forall G : mgraph,
     (0 < #|G|)%N -> (0 < #|edge G|)%N -> bridgeless G -> u6_five_even_cover G).

End ImplicationsU6Legacy.

(** Not a conversion: arc-end degrees against incidence degrees, equal under the loopless guard that both
    sides carry ([mdeg_loopless]). *)
Lemma cubic_compat (G : mgraph) :
  Legacy.cubic G <->
  cubic G.
Proof.
rewrite /Legacy.cubic /cubic /loopless_cubic /mcubic /mregular.
split=> -[ll h]; split=> // v; [rewrite -(mdeg_loopless v ll) | rewrite (mdeg_loopless v ll)]; exact: h.
Qed.

Lemma cycle_double_covers_containing_predefined_2_regular_statement_compat :
  U6Legacy.cycle_double_covers_containing_predefined_2_regular_statement <->
  cycle_double_covers_containing_predefined_2_regular_statement.
Proof. rewrite /U6Legacy.cycle_double_covers_containing_predefined_2_regular_statement /cycle_double_covers_containing_predefined_2_regular_statement; setoid_rewrite cubic_compat; reflexivity. Qed.

Lemma three_decomposition_statement_compat :
  U6Legacy.three_decomposition_statement <->
  three_decomposition_statement.
Proof. rewrite /U6Legacy.three_decomposition_statement /three_decomposition_statement; setoid_rewrite cubic_compat; reflexivity. Qed.

Lemma odd_cycles_and_low_oddness_statement_compat :
  U6Legacy.odd_cycles_and_low_oddness_statement <->
  odd_cycles_and_low_oddness_statement.
Proof. rewrite /U6Legacy.odd_cycles_and_low_oddness_statement /odd_cycles_and_low_oddness_statement; setoid_rewrite cubic_compat; reflexivity. Qed.

Lemma strong_5_cycle_double_cover_statement_compat :
  U6Legacy.strong_5_cycle_double_cover_statement <->
  strong_5_cycle_double_cover_statement.
Proof. rewrite /U6Legacy.strong_5_cycle_double_cover_statement /strong_5_cycle_double_cover_statement; setoid_rewrite cubic_compat; reflexivity. Qed.

Lemma cubic_bridgeless_compat (G : mgraph) :
  U10Legacy.cubic_bridgeless G <->
  cubic_bridgeless G.
Proof. rewrite /U10Legacy.cubic_bridgeless /cubic_bridgeless; setoid_rewrite cubic_compat; reflexivity. Qed.

Lemma intersecting_two_perfect_matchings_statement_compat :
  U10Legacy.intersecting_two_perfect_matchings_statement <->
  intersecting_two_perfect_matchings_statement.
Proof. rewrite /U10Legacy.intersecting_two_perfect_matchings_statement /intersecting_two_perfect_matchings_statement; setoid_rewrite cubic_bridgeless_compat; reflexivity. Qed.

Lemma petersen_coloring_statement_compat :
  U10Legacy.petersen_coloring_statement <->
  petersen_coloring_statement.
Proof. rewrite /U10Legacy.petersen_coloring_statement /petersen_coloring_statement; setoid_rewrite cubic_bridgeless_compat; reflexivity. Qed.

Lemma the_berge_fulkerson_statement_compat :
  U10Legacy.the_berge_fulkerson_statement <->
  the_berge_fulkerson_statement.
Proof. rewrite /U10Legacy.the_berge_fulkerson_statement /the_berge_fulkerson_statement; setoid_rewrite cubic_bridgeless_compat; reflexivity. Qed.

Lemma external_cdc_cubic_2connected_reduction_statement_compat :
  ImplicationsU6Legacy.external_cdc_cubic_2connected_reduction_statement <->
  external_cdc_cubic_2connected_reduction_statement.
Proof. rewrite /ImplicationsU6Legacy.external_cdc_cubic_2connected_reduction_statement /external_cdc_cubic_2connected_reduction_statement; setoid_rewrite cubic_compat; reflexivity. Qed.

Lemma external_five_even_cover_cubic_reduction_statement_compat :
  ImplicationsU6Legacy.external_five_even_cover_cubic_reduction_statement <->
  external_five_even_cover_cubic_reduction_statement.
Proof. rewrite /ImplicationsU6Legacy.external_five_even_cover_cubic_reduction_statement /external_five_even_cover_cubic_reduction_statement; setoid_rewrite cubic_compat; reflexivity. Qed.

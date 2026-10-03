(** * Chromatic.migration.subgraph_of -- frozen ordinary subgraph containment certificates

    Batch A, family A5 (ordinary [subgraph_of] containment), X31 and the chromatic XE1/XE2 rows.
    [Legacy] freezes the two helpers verbatim as they stood at 49ddc03:
    [x31_subgraph_of] and the chromatic [xe1_subgraph_of], both
    [exists f : H -> G, injective f /\ forall x y, x -- y -> f x -- f y].  [X31Legacy],
    [XE1Legacy] and [XE2Legacy] freeze the seven affected statements (XE2 reaches
    [xe1_subgraph_of] across modules).

    The live helpers now unfold to [GTBase.common.has_subgraph G H], host first (the
    reverse of the local argument order).  [has_subgraphP] proves the unconditional
    witness characterization, so each helper certificate is that iff, and every chain
    and statement certificate transports it through the unchanged statement structure
    by setoid rewriting under the logical connectives.  The local [and3]/[and4]
    instances only add the [[/\ ...]] forms; no axiom is used.  The regeneration spec
    is meta/migration_reports/subgraph_of.spec.json. *)

From GTBase Require Import base.
From Chromatic.conjectures Require Import X31 XE1 XE2.
From Chromatic.migration Require consecutive_in_cycle.
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

Definition x31_subgraph_of (H G : sgraph) : Prop :=
  exists f : H -> G,
    injective f /\
    forall x y : H, x -- y -> f x -- f y.

Definition xe1_subgraph_of (H G : sgraph) : Prop :=
  exists f : H -> G, injective f /\ forall x y : H, x -- y -> f x -- f y.

End Legacy.

Module X31Legacy.

Definition chromatic_girth_average_degree_subgraph_statement : Prop :=
  forall k g : nat,
    0 < k ->
    3 <= g ->
    exists c : nat,
      0 < c /\
      forall G : sgraph,
        c <= χ([set: G]) ->
        exists H : sgraph,
          Legacy.x31_subgraph_of H G /\
          girth_geq H g /\
          average_degree_geq H k 1.

End X31Legacy.

Module XE1Legacy.

Definition erdos_108_statement : Prop :=
  forall r k : nat, 4 <= r -> 2 <= k ->
    exists f : nat,
      forall G : sgraph,
        f <= χ([set: G]) ->
        exists H : sgraph,
          Legacy.xe1_subgraph_of H G /\ girth_geq H r /\ k <= χ([set: H]).

Definition erdos_628_statement : Prop :=
  forall (G : sgraph) (k a b : nat),
    χ([set: G]) = k ->
    ~ Legacy.xe1_subgraph_of 'K_k G ->
    2 <= a -> 2 <= b -> a + b = k.+1 ->
    exists A B : {set G},
      [disjoint A & B] /\
      a <= χ([set: induced A]) /\
      b <= χ([set: induced B]).

End XE1Legacy.

Module XE2Legacy.

Definition erdos_1091_statement : Prop :=
  (forall G : sgraph,
    ~ Legacy.xe1_subgraph_of 'K_4 G ->
    χ([set: G]) = 4 ->
    xe1_odd_cycle_with_diagonals G 2) /\
  exists f : nat -> nat,
    xe1_unbounded f /\
    forall (r : nat) (G : sgraph),
      ~ Legacy.xe1_subgraph_of 'K_4 G ->
      χ([set: G]) = 4 ->
      xe1_induced_subgraph_chi_le G r 3 ->
      xe1_odd_cycle_with_diagonals G (f r).

Definition erdos_58_statement : Prop :=
  forall (G : sgraph) (k : nat),
    xe2_odd_cycle_lengths_bounded G k ->
    χ([set: G]) <= 2 * k + 2 /\
    (χ([set: G]) = 2 * k + 2 <-> Legacy.xe1_subgraph_of 'K_(2 * k + 2) G).

Definition erdos_762_statement : Prop :=
  forall (G : sgraph) (z : nat),
    ~ Legacy.xe1_subgraph_of 'K_5 G ->
    xe2_cochromatic_number G z ->
    4 <= z ->
    χ([set: G]) <= z + 2.

Definition erdos_923_statement : Prop :=
  forall k : nat, exists f : nat,
    forall G : sgraph,
      f <= χ([set: G]) ->
      exists H : sgraph,
        Legacy.xe1_subgraph_of H G /\ triangle_free H /\ k <= χ([set: H]).

End XE2Legacy.

(** B4 history: erdos_1091 before both A5 and B4, with A5's frozen helper and B4's frozen
    odd-cycle-with-diagonals chain (Chromatic.migration.consecutive_in_cycle, fbf33a0). *)
Module XE2Original.

Definition erdos_1091_statement : Prop :=
  (forall G : sgraph,
    ~ Legacy.xe1_subgraph_of 'K_4 G ->
    χ([set: G]) = 4 ->
    Chromatic.migration.consecutive_in_cycle.XE1Legacy.odd_cycle_with_diagonals G 2) /\
  exists f : nat -> nat,
    xe1_unbounded f /\
    forall (r : nat) (G : sgraph),
      ~ Legacy.xe1_subgraph_of 'K_4 G ->
      χ([set: G]) = 4 ->
      xe1_induced_subgraph_chi_le G r 3 ->
      Chromatic.migration.consecutive_in_cycle.XE1Legacy.odd_cycle_with_diagonals G (f r).

End XE2Original.

(** ** Certificates *)

Lemma x31_subgraph_of_compat (H G : sgraph) :
  Legacy.x31_subgraph_of H G <-> x31_subgraph_of H G.
Proof. exact: iff_sym (has_subgraphP G H). Qed.

Lemma xe1_subgraph_of_compat (H G : sgraph) :
  Legacy.xe1_subgraph_of H G <-> xe1_subgraph_of H G.
Proof. exact: iff_sym (has_subgraphP G H). Qed.

Lemma chromatic_girth_average_degree_subgraph_statement_compat :
  X31Legacy.chromatic_girth_average_degree_subgraph_statement <-> chromatic_girth_average_degree_subgraph_statement.
Proof. rewrite /X31Legacy.chromatic_girth_average_degree_subgraph_statement /chromatic_girth_average_degree_subgraph_statement; try setoid_rewrite x31_subgraph_of_compat; reflexivity. Qed.

Lemma erdos_108_statement_compat :
  XE1Legacy.erdos_108_statement <-> erdos_108_statement.
Proof. rewrite /XE1Legacy.erdos_108_statement /erdos_108_statement; try setoid_rewrite xe1_subgraph_of_compat; reflexivity. Qed.

Lemma erdos_628_statement_compat :
  XE1Legacy.erdos_628_statement <-> erdos_628_statement.
Proof. rewrite /XE1Legacy.erdos_628_statement /erdos_628_statement; try setoid_rewrite xe1_subgraph_of_compat; reflexivity. Qed.

Lemma erdos_1091_statement_compat :
  XE2Legacy.erdos_1091_statement <-> erdos_1091_statement.
Proof. rewrite /XE2Legacy.erdos_1091_statement /erdos_1091_statement; try setoid_rewrite xe1_subgraph_of_compat; reflexivity. Qed.

Lemma erdos_58_statement_compat :
  XE2Legacy.erdos_58_statement <-> erdos_58_statement.
Proof. rewrite /XE2Legacy.erdos_58_statement /erdos_58_statement; try setoid_rewrite xe1_subgraph_of_compat; reflexivity. Qed.

Lemma erdos_762_statement_compat :
  XE2Legacy.erdos_762_statement <-> erdos_762_statement.
Proof. rewrite /XE2Legacy.erdos_762_statement /erdos_762_statement; try setoid_rewrite xe1_subgraph_of_compat; reflexivity. Qed.

Lemma erdos_923_statement_compat :
  XE2Legacy.erdos_923_statement <-> erdos_923_statement.
Proof. rewrite /XE2Legacy.erdos_923_statement /erdos_923_statement; try setoid_rewrite xe1_subgraph_of_compat; reflexivity. Qed.

Lemma erdos_1091_statement_original_compat :
  XE2Original.erdos_1091_statement <-> erdos_1091_statement.
Proof.
rewrite /XE2Original.erdos_1091_statement /erdos_1091_statement; setoid_rewrite xe1_subgraph_of_compat;
  setoid_rewrite Chromatic.migration.consecutive_in_cycle.xe1_odd_cycle_with_diagonals_compat; reflexivity.
Qed.

Print Assumptions x31_subgraph_of_compat.
Print Assumptions xe1_subgraph_of_compat.
Print Assumptions chromatic_girth_average_degree_subgraph_statement_compat.
Print Assumptions erdos_108_statement_compat.
Print Assumptions erdos_628_statement_compat.
Print Assumptions erdos_1091_statement_compat.
Print Assumptions erdos_58_statement_compat.
Print Assumptions erdos_762_statement_compat.
Print Assumptions erdos_923_statement_compat.
Print Assumptions erdos_1091_statement_original_compat.

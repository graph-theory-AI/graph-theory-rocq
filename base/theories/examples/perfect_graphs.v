(** Public-only clients; no conjecture or migration imports. *)
From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph coloring wpgt.
From GTBase Require Import base perfect_graphs.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Example empty_graph_is_perfect : is_perfect_graph 'K_0.
Proof. exact: is_perfect_graph_empty. Qed.

Example singleton_is_perfect : is_perfect_graph 'K_1.
Proof. exact: is_perfect_graph_complete. Qed.

Example complete_two_is_perfect : is_perfect_graph 'K_2.
Proof. exact: is_perfect_graph_complete. Qed.

Example complete_graphs_are_perfect n : is_perfect_graph 'K_n.
Proof. exact: is_perfect_graph_complete. Qed.

Example edgeless_graphs_are_perfect n : is_perfect_graph (compl 'K_n).
Proof. exact: is_perfect_graph_complement_complete. Qed.

Example empty_induced_subset (G : sgraph) : is_perfect_graph (induced (set0 : {set G})).
Proof. by rewrite /is_perfect_graph perfectT perfect_induced; exact: perfect0. Qed.

Example supplied_isomorphism (G H : sgraph) (iso : diso G H) :
  is_perfect_graph G -> is_perfect_graph H.
Proof. move=> perf; exact: (is_perfect_graph_diso iso).1 perf. Qed.

Example supplied_induced_subset (G : sgraph) (A : {set G}) :
  is_perfect_graph G -> is_perfect_graph (induced A).
Proof. exact: is_perfect_graph_induced. Qed.

(** A bounded five-membership proof avoids enumerating set-valued maxima. *)
Local Definition c5v0 : cycle_graph 5 := @Ordinal 5 0 isT.
Local Definition c5v1 : cycle_graph 5 := @Ordinal 5 1 isT.
Local Definition c5v2 : cycle_graph 5 := @Ordinal 5 2 isT.
Local Definition c5v3 : cycle_graph 5 := @Ordinal 5 3 isT.
Local Definition c5v4 : cycle_graph 5 := @Ordinal 5 4 isT.

Local Lemma c5_card (S : {set cycle_graph 5}) :
  #|S| = (c5v0 \in S) + ((c5v1 \in S) + ((c5v2 \in S) + ((c5v3 \in S) + ((c5v4 \in S) + 0)))).
Proof.
have enum5 : enum 'I_5 = [:: c5v0; c5v1; c5v2; c5v3; c5v4].
  apply: (inj_map val_inj); by rewrite val_enum_ord.
by rewrite cardE /enum_mem -enumT enum5 size_filter /=.
Qed.

Local Lemma c5_stable_bound (S : {set cycle_graph 5}) : stable S -> #|S| <= 2.
Proof.
move/stableP=> bound.
have e01 : ~~ ((c5v0 \in S) && (c5v1 \in S)).
  apply/negP=> /andP [memberI memberJ].
  move: (bound c5v0 c5v1 memberI memberJ); by vm_compute.
have e12 : ~~ ((c5v1 \in S) && (c5v2 \in S)).
  apply/negP=> /andP [memberI memberJ].
  move: (bound c5v1 c5v2 memberI memberJ); by vm_compute.
have e23 : ~~ ((c5v2 \in S) && (c5v3 \in S)).
  apply/negP=> /andP [memberI memberJ].
  move: (bound c5v2 c5v3 memberI memberJ); by vm_compute.
have e34 : ~~ ((c5v3 \in S) && (c5v4 \in S)).
  apply/negP=> /andP [memberI memberJ].
  move: (bound c5v3 c5v4 memberI memberJ); by vm_compute.
have e40 : ~~ ((c5v4 \in S) && (c5v0 \in S)).
  apply/negP=> /andP [memberI memberJ].
  move: (bound c5v4 c5v0 memberI memberJ); by vm_compute.
move: e01 e12 e23 e34 e40; rewrite c5_card.
by case: (c5v0 \in S); case: (c5v1 \in S); case: (c5v2 \in S); case: (c5v3 \in S); case: (c5v4 \in S).
Qed.

Local Lemma c5_clique_bound (S : {set cycle_graph 5}) : clique S -> #|S| <= 2.
Proof.
move=> bound.
have e02 : ~~ ((c5v0 \in S) && (c5v2 \in S)).
  apply/negP=> /andP [memberI memberJ].
  have distinct : c5v0 != c5v2 by vm_compute.
  move: (bound c5v0 c5v2 memberI memberJ distinct); by vm_compute.
have e03 : ~~ ((c5v0 \in S) && (c5v3 \in S)).
  apply/negP=> /andP [memberI memberJ].
  have distinct : c5v0 != c5v3 by vm_compute.
  move: (bound c5v0 c5v3 memberI memberJ distinct); by vm_compute.
have e13 : ~~ ((c5v1 \in S) && (c5v3 \in S)).
  apply/negP=> /andP [memberI memberJ].
  have distinct : c5v1 != c5v3 by vm_compute.
  move: (bound c5v1 c5v3 memberI memberJ distinct); by vm_compute.
have e14 : ~~ ((c5v1 \in S) && (c5v4 \in S)).
  apply/negP=> /andP [memberI memberJ].
  have distinct : c5v1 != c5v4 by vm_compute.
  move: (bound c5v1 c5v4 memberI memberJ distinct); by vm_compute.
have e24 : ~~ ((c5v2 \in S) && (c5v4 \in S)).
  apply/negP=> /andP [memberI memberJ].
  have distinct : c5v2 != c5v4 by vm_compute.
  move: (bound c5v2 c5v4 memberI memberJ distinct); by vm_compute.
move: e02 e03 e13 e14 e24; rewrite c5_card.
by case: (c5v0 \in S); case: (c5v1 \in S); case: (c5v2 \in S); case: (c5v3 \in S); case: (c5v4 \in S).
Qed.

Example cycle_five_independence_bound : α([set: cycle_graph 5]) <= 2.
Proof. case: (alphaP [set: cycle_graph 5]) => S /maxstabset_stable st; exact: c5_stable_bound st. Qed.

Example cycle_five_clique_bound : ω([set: cycle_graph 5]) <= 2.
Proof. case: (omegaP [set: cycle_graph 5]) => S /maxclique_clique cl; exact: c5_clique_bound cl. Qed.

Example cycle_five_is_not_perfect : ~ is_perfect_graph (cycle_graph 5).
Proof.
move/is_perfect_graph_hajnal=> /(_ [set: cycle_graph 5]) lower.
have upper : α([set: cycle_graph 5]) * ω([set: cycle_graph 5]) <= 2 * 2 :=
  leq_mul cycle_five_independence_bound cycle_five_clique_bound.
by have := leq_trans lower upper; rewrite cardsT card_ord.
Qed.

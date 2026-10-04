(** Downstream use of triangle vertex sets ([triangle], [triangle_set]) and raw two-element subsets ([raw_pairs])
    without corpus imports: complete graphs, edgeless graphs, small sets, and the clique guard that makes raw pairs
    graph edges. *)
From GTBase Require Import base triangles.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The whole vertex set of [K_n] is a clique. *)
Lemma Kn_clique (n : nat) : clique [set: 'K_n].
Proof. by move=> x y _ _. Qed.

(** [K_3] is a triangle in both presentations; the whole [K_4] is not. *)
Example K3_triangle : triangle [set: 'K_3] /\ triangle_set [set: 'K_3].
Proof.
have t : triangle [set: 'K_3] by split; [exact: Kn_clique | rewrite cardsT card_ord].
by split=> //; apply/triangleP.
Qed.

Example K4_not_triangle : ~ triangle [set: 'K_4].
Proof. by case=> _; rewrite cardsT card_ord. Qed.

(** A triangle's three raw pairs are its three edges: the clique guard turns raw pairs into graph edges. *)
Example K3_raw_pairs_are_edges :
  raw_pairs [set: 'K_3] = [set e in E('K_3) | e \subset [set: 'K_3]] /\ #|raw_pairs [set: 'K_3]| = 3.
Proof.
split; first exact: raw_pairs_cliqueE (@Kn_clique 3).
by apply: triangle_raw_pairs; case: K3_triangle.
Qed.

(** Empty and singleton sets have no raw pair. *)
Example raw_pairs_empty_singleton (G : sgraph) (x : G) :
  raw_pairs (set0 : {set G}) = set0 /\ raw_pairs [set x] = set0.
Proof. by split; apply: raw_pairs_small; rewrite ?cards0 ?cards1. Qed.

(** An edgeless graph: raw pairs ignore adjacency. *)
Definition edgeless (n : nat) : sgraph :=
  @SGraph 'I_n (fun _ _ => false) (fun _ _ => erefl) (fun _ => erefl).

(** A nonadjacent pair still contributes one raw pair. *)
Example nonadjacent_pair (x y : edgeless 2) :
  x != y -> ~~ (x -- y) /\ #|raw_pairs [set x; y]| = 1.
Proof. by move=> xy; split=> //; rewrite card_raw_pairs cards2 xy. Qed.

(** Three edgeless vertices have three raw pairs but form no triangle. *)
Example edgeless_three :
  #|raw_pairs [set: edgeless 3]| = 3 /\ ~ triangle [set: edgeless 3].
Proof.
split; first by rewrite card_raw_pairs cardsT card_ord.
case=> cl _; have := cl ord0 (@Ordinal 3 1 isT); rewrite !inE => /(_ isT isT isT).
by [].
Qed.

Print Assumptions K3_triangle.
Print Assumptions K3_raw_pairs_are_edges.
Print Assumptions nonadjacent_pair.
Print Assumptions edgeless_three.

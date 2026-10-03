(** Downstream use of inclusion-maximal cliques ([maximal_clique], [nontrivial_maximal_clique]) without corpus
    imports: the empty and one-vertex graphs, complete graphs, edgeless graphs, and inclusion-maximal versus
    maximum-cardinality cliques (upstream [maxcliques]) in the disjoint union of [K_2] and [K_3]. *)
From GTBase Require Import base maximal_cliques.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** [K_0]: the empty set is its maximal clique, and it is not nontrivial. *)
Example K0_empty_maximal :
  maximal_clique (set0 : {set 'K_0}) /\ ~~ nontrivial_maximal_clique (set0 : {set 'K_0}).
Proof.
split; last by rewrite /nontrivial_maximal_clique cards0.
apply/maximal_cliqueP; split; first by apply: small_clique; rewrite cards0.
by move=> T /properP[_ [[]]].
Qed.

(** [K_1]: the singleton is maximal but not nontrivial. *)
Example K1_singleton_maximal :
  maximal_clique [set (ord0 : 'K_1)] /\ ~~ nontrivial_maximal_clique [set (ord0 : 'K_1)].
Proof.
split; last by rewrite /nontrivial_maximal_clique cards1.
apply/maximal_cliqueP; split; first exact: clique1.
by move=> T /properP[_ [x _]]; rewrite (ord1 x) inE eqxx.
Qed.

(** Complete graphs: the whole vertex set is maximal, and nontrivial from two vertices on. *)
Example Kn_whole_maximal (n : nat) : maximal_clique [set: 'K_n].
Proof.
apply/maximal_cliqueP; split; first by move=> x y _ _.
by move=> T /properP[_ [x _]]; rewrite inE.
Qed.

Example Kn_whole_nontrivial (n : nat) : 1 < n -> nontrivial_maximal_clique [set: 'K_n].
Proof. by move=> n1; rewrite /nontrivial_maximal_clique cardsT card_ord n1 Kn_whole_maximal. Qed.

(** A nonempty edgeless graph: exactly the singletons are maximal, so none is nontrivial. *)
Definition edgeless (n : nat) : sgraph :=
  @SGraph 'I_n (fun _ _ => false) (fun _ _ => erefl) (fun _ => erefl).

Lemma edgeless_clique (n : nat) (S : {set edgeless n}) : clique S <-> #|S| <= 1.
Proof.
split=> [cl|]; last exact: small_clique.
rewrite leqNgt; apply/negP => /card_gt1P[x [y [xS yS xy]]].
by have := cl x y xS yS xy.
Qed.

Example edgeless_maximal (n : nat) (S : {set edgeless n.+1}) : maximal_clique S = (#|S| == 1).
Proof.
apply/maximal_cliqueP/eqP => [[/edgeless_clique S1 h]|S1].
  apply/eqP; rewrite eqn_leq S1 card_gt0; apply/negP => /eqP S0.
  apply: (h [set ord0]); last by apply/edgeless_clique; rewrite cards1.
  by rewrite S0 proper0; apply/set0Pn; exists ord0; rewrite inE.
split=> [|T /proper_card]; first by apply/edgeless_clique; rewrite S1.
by rewrite S1 => T1 /edgeless_clique; rewrite leqNgt T1.
Qed.

(** Maximal versus maximum: the disjoint union of [K_2] and [K_3]. *)
Definition sum_rel (u v : 'I_2 + 'I_3) : bool :=
  match u, v with
  | inl x, inl y => x != y
  | inr x, inr y => x != y
  | _, _ => false
  end.

Lemma sum_rel_sym : symmetric sum_rel.
Proof. by do 2 case=> ?; rewrite //= eq_sym. Qed.

Lemma sum_rel_irrefl : irreflexive sum_rel.
Proof. by case=> x /=; rewrite eqxx. Qed.

Definition K2K3 : sgraph := SGraph sum_rel_sym sum_rel_irrefl.

Definition small_side : {set K2K3} := [set (inl x : K2K3) | x in [set: 'I_2]].
Definition large_side : {set K2K3} := [set (inr x : K2K3) | x in [set: 'I_3]].

Lemma card_small_side : #|small_side| = 2.
Proof. by rewrite card_imset ?cardsT ?card_ord //; move=> x y []. Qed.

Lemma card_large_side : #|large_side| = 3.
Proof. by rewrite card_imset ?cardsT ?card_ord //; move=> x y []. Qed.

(** A clique lies on one side. *)
Lemma K2K3_clique_side (S : {set K2K3}) : clique S -> S \subset small_side \/ S \subset large_side.
Proof.
move=> cl; case: (boolP [exists x : 'I_2, (inl x : K2K3) \in S]) => [/existsP[x xS]|/existsPn noL].
  left; apply/subsetP => -[y|y] yS; first by apply/imsetP; exists y.
  by have := cl (inl x) (inr y) xS yS isT.
right; apply/subsetP => -[y|y] yS; last by apply/imsetP; exists y.
by have := noL y; rewrite yS.
Qed.

Lemma small_side_clique : clique small_side.
Proof. by move=> u v /imsetP[x _ ->] /imsetP[y _ ->] /=; rewrite (inj_eq (@inl_inj _ _)). Qed.

Lemma large_side_clique : clique large_side.
Proof. by move=> u v /imsetP[x _ ->] /imsetP[y _ ->] /=; rewrite (inj_eq (@inr_inj _ _)). Qed.

Lemma K2K3_omega : ω([set: K2K3]) = 3.
Proof.
apply/eqP; rewrite eqn_leq; apply/andP; split.
  rewrite omega_setT_maxE; apply/bigmax_leqP => S /cliqueP cS.
  case: (K2K3_clique_side cS) => /subset_leq_card; rewrite ?card_small_side ?card_large_side //.
  by move/leq_trans; apply.
rewrite -card_large_side; apply: clique_bound; rewrite !inE subsetT /=; apply/cliqueP.
exact: large_side_clique.
Qed.

(** The [K_2] side is a nontrivial inclusion-maximal clique but not a maximum one; the [K_3] side is maximum. *)
Example small_side_maximal_not_maximum :
  nontrivial_maximal_clique small_side /\ small_side \notin maxcliques [set: K2K3].
Proof.
split; last by rewrite !inE K2K3_omega card_small_side andbF.
rewrite /nontrivial_maximal_clique card_small_side /=; apply/maximal_cliqueP; split.
  exact: small_side_clique.
move=> T /properP[sub [[y|y] yT ny]]; first by move: ny; rewrite imset_f.
move=> cT; have x0 : (inl ord0 : K2K3) \in T by apply: (subsetP sub); rewrite imset_f.
by have := cT _ _ x0 yT isT.
Qed.

Example large_side_maximum : large_side \in maxcliques [set: K2K3].
Proof.
rewrite !inE subsetT /= K2K3_omega card_large_side leqnn andbT.
by apply/cliqueP; exact: large_side_clique.
Qed.

Print Assumptions K0_empty_maximal.
Print Assumptions edgeless_maximal.
Print Assumptions small_side_maximal_not_maximum.
Print Assumptions large_side_maximum.

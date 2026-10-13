(** Downstream use of the GTBase strongly regular API, without corpus imports: [K_2] has the parameters [(1, 0, 0)]
    (and [(1, 0, mu)] for every [mu]) but is not connected-nontrivial; the empty graph has every triple; [K_{2,2}] is
    connected-nontrivial with [(2, 0, 2)]; the guarded wrapper implies the unguarded one and at least three vertices. *)
From GTBase Require Import base strongly_regular.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma K2_neighbours (x : 'K_2) : N(x) = ~: [set x].
Proof. by apply/setP => y; rewrite !inE eq_sym. Qed.

(** [K_2]: one vertex of degree one each, no common neighbour across the edge; [mu] is vacuous. *)
Example K2_parameters (mu : nat) : strongly_regular_parameters 'K_2 1 0 mu.
Proof.
split.
- by move=> x; rewrite K2_neighbours (cardsCs (~: [set x])) setCK cards1 card_ord subn1.
- move=> x y xy.
  have e2 : [set x] :|: [set y] = [set: 'K_2].
    apply/eqP; rewrite eqEcard subsetT cardsU1 inE cards1 cardsT card_ord.
    by rewrite (sg_edgeNeq xy).
  by rewrite /common_nbr !K2_neighbours -setCU e2 setCT cards0.
- move=> x y xney nadj; exfalso; move: nadj.
  by rewrite (_ : (x -- y) = (x != y)) ?xney.
Qed.

Example K2_has_parameters : has_strongly_regular_parameters 'K_2.
Proof. by exists 1, 0, 0; exact: K2_parameters. Qed.

(** The degree guard excludes [K_2]. *)
Example K2_not_connected_nontrivial : ~ connected_nontrivial_strongly_regular 'K_2.
Proof. by move=> /connected_nontrivial_strongly_regular_card; rewrite card_ord. Qed.

(** The empty graph satisfies every triple vacuously, and the degree guard excludes it. *)
Example K0_parameters (k lam mu : nat) : strongly_regular_parameters 'K_0 k lam mu.
Proof. by split=> -[]. Qed.

Example K0_not_connected_nontrivial : ~ connected_nontrivial_strongly_regular 'K_0.
Proof. by move=> /connected_nontrivial_strongly_regular_card; rewrite card_ord. Qed.

(** [K_{2,2}] = [C_4]: connected, [2]-regular with [0 < 2 < 3], no common neighbour across an edge, two common
    neighbours within a side. *)
Example K22_connected_nontrivial : connected_nontrivial_strongly_regular 'K_2,2.
Proof.
exists 2, 0, 2; split.
- exact: (@Knm_connected 1 1).
- by split=> //; rewrite card_sum !card_ord.
split.
- by move=> [x|y]; rewrite ?deg_Knm_l ?deg_Knm_r.
- move=> [x|x] [y|y] uv //.
  + rewrite /common_nbr opn_Knm_l opn_Knm_r.
    apply/eqP; rewrite cards_eq0; apply/eqP/setP => z; rewrite !inE.
    by case: z => z; apply/andP => -[/imsetP[? _ ?] /imsetP[? _ ?]].
  + rewrite /common_nbr opn_Knm_l opn_Knm_r.
    apply/eqP; rewrite cards_eq0; apply/eqP/setP => z; rewrite !inE.
    by case: z => z; apply/andP => -[/imsetP[? _ ?] /imsetP[? _ ?]].
- move=> [x|x] [y|y] _ nadj //.
  + by rewrite /common_nbr !opn_Knm_l setIid card_imset ?cardsT ?card_ord //; exact: inr_inj.
  + by rewrite /common_nbr !opn_Knm_r setIid card_imset ?cardsT ?card_ord //; exact: inl_inj.
Qed.

Example K22_has_parameters : has_strongly_regular_parameters 'K_2,2.
Proof. exact: connected_nontrivial_strongly_regularW K22_connected_nontrivial. Qed.

(** * GTMisc.conjectures.grounding_X314 -- grounding certificates for wave X314 (arxiv:2008.03587#00)

    - helper_sanity [g314_helper_sanity]: K_1 is a pendant extension of itself, K_2 and K_1 plus a leaf are pendant
      extensions of K_1, two isolated vertices plus a leaf extend two isolated vertices, and the added vertex has
      exactly one neighbour.
    - hyp_inhabited [g314_R1_hyp_inhabited]: K_1 meets both guards, K_2 is a pendant extension of K_1, and
      z(K_1) = z(K_2) = 1, so the statement's instance at (K_1, K_2) has inhabited hypotheses and holds.
    - not_trivially_true [g314_R1_not_trivially_true]: without the connectivity hypothesis the statement fails:
      two isolated vertices have zombie number 2, and with a leaf added to one of them 3. *)

From GTBase Require Export base.
From GTMisc.foundations Require Import zombies.
From GTMisc.conjectures Require Import X314.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** General lemmas *)

(** The vertex added by [add_node H [set v]] has exactly one neighbour, v. *)
Lemma g314_leaf_neighbours (H : sgraph) (v : H) : N(None : add_node H [set v]) = [set Some v].
Proof. by apply/setP => -[u|]; rewrite !inE //= /edge_rel /= inE. Qed.

(** Every other vertex is at the truncated distance #|G| from an isolated vertex. *)
Lemma g314_dist_isolated (G : sgraph) (b x : G) :
  (forall z : G, ~~ b -- z) -> x != b -> graph_dist x b = #|G|.
Proof.
move=> hb xb.
have nb : forall k, b \notin rel_ball (--) k x.
  elim=> [|k IH] /=; first by rewrite inE eq_sym.
  rewrite in_setU (negbTE IH) /=; apply/bigcupP => -[z _]; rewrite inE => zb.
  by move: (hb z); rewrite sg_sym zb.
rewrite /graph_dist; case: ex_minnP => m Pm min; move: Pm; rewrite (negbTE (nb m)) /= => /eqP ->.
by [].
Qed.

Lemma g314_isolated_disconnected (G : sgraph) (x y : G) :
  (forall z : G, ~~ x -- z) -> x != y -> ~ connected [set: G].
Proof.
move=> hx xy hc; case/connectP: (hc x y (in_setT _) (in_setT _)) => -[/= _ yx|z p /= /andP [xz _] _].
  by rewrite yx eqxx in xy.
by move: xz; rewrite !inE /= (negbTE (hx z)).
Qed.

(** ** K_1, K_1 plus a leaf, K_2 *)

Lemma g314_K1_guards : connected [set: 'K_1] /\ 0 < #|'K_1|.
Proof.
split; last by rewrite card_ord.
have -> : [set: 'K_1] = [set ord0] by apply/setP => x; rewrite !inE (ord1 x) eqxx.
exact: connected1.
Qed.

Lemma g314_K2_zombie_number : zombie_number 'K_2 1.
Proof.
split; first by apply: (@zombies_win_dominating 'K_2 ord0) => u; rewrite eq_sym.
by move=> j; rewrite ltnS leqn0 => /eqP ->; apply: not_zombies_win_0; rewrite card_ord.
Qed.

Definition g314_K1_leaf : sgraph := add_node 'K_1 [set ord0].

Lemma g314_K1_leaf_pendant : x314_pendant_extension 'K_1 g314_K1_leaf.
Proof.
apply: (@x314_pendant_step _ 'K_1 ord0); first exact/x314_pendant_refl/inhabits/diso_id.
exact/inhabits/diso_id.
Qed.

Definition g314_leaf_to_K2 (x : g314_K1_leaf) : 'K_2 := if x is Some _ then ord0 else ord_max.
Definition g314_K2_to_leaf (y : 'K_2) : g314_K1_leaf := if y == ord0 then Some ord0 else None.

(** K_1 plus a leaf is K_2. *)
Lemma g314_K1_leaf_K2 : diso g314_K1_leaf 'K_2.
Proof.
apply: (@Diso' _ _ g314_leaf_to_K2 g314_K2_to_leaf).
- by case=> [a|] //=; rewrite /g314_K2_to_leaf eqxx (ord1 a).
- move=> y; rewrite /g314_K2_to_leaf; case: eqP => [-> //|ne] /=; apply/val_inj => /=.
  by case: y ne => -[|[|//]] lt //= ne; case: ne; apply/val_inj.
- by case=> [a|] [b|] //=; rewrite /edge_rel /= ?inE ?(ord1 a) ?(ord1 b).
Qed.

Lemma g314_K2_pendant : x314_pendant_extension 'K_1 'K_2.
Proof.
apply: (@x314_pendant_step _ 'K_1 ord0); first exact/x314_pendant_refl/inhabits/diso_id.
exact/inhabits/g314_K1_leaf_K2.
Qed.

(** ** Two isolated vertices, and the same graph with a leaf at one of them *)

Definition g314_e2 : sgraph := add_node 'K_1 set0.
Definition g314_e2_leaf : sgraph := add_node g314_e2 [set Some ord0].

Lemma g314_e2_isolated (z : g314_e2) : ~~ ((None : g314_e2) -- z).
Proof. by case: z => [u|] //=; rewrite /edge_rel /= inE. Qed.

Lemma g314_e2_no_edge (x z : g314_e2) : ~~ (x -- z).
Proof.
case: x => [a|]; last exact: g314_e2_isolated.
case: z => [b|] /=; last by rewrite /edge_rel /= inE.
by rewrite /edge_rel /= (ord1 a) (ord1 b) sg_irrefl.
Qed.

Lemma g314_e2_zombie_number : zombie_number g314_e2 2.
Proof.
split.
  by have := zombies_win_card g314_e2; rewrite card_option card_ord.
move=> j; rewrite ltnS leq_eqVlt ltnS leqn0 => /orP [/eqP ->|/eqP ->]; last first.
  by apply: not_zombies_win_0; rewrite card_option card_ord.
move=> [t /existsP [Z0 /forallP h]].
pose s0 : g314_e2 := if Z0 ord0 is None then Some ord0 else None.
have nc : ~~ zombie_caught Z0 s0.
  apply/existsPn => i; rewrite (ord1 i) /s0; by case: (Z0 ord0).
move: (h s0); rewrite (@zombies_stuck _ 1 t Z0 s0 ord0) ?(negbTE nc) //.
by move=> w; rewrite (negbTE (g314_e2_no_edge _ _)).
Qed.

Local Notation b314 := (Some None : g314_e2_leaf).

Lemma g314_b_isolated (z : g314_e2_leaf) : ~~ (b314 -- z).
Proof.
case: z => [u|] /=; last by rewrite /edge_rel /= inE.
exact: g314_e2_no_edge.
Qed.

(** One or two zombies lose on two isolated vertices plus a leaf: the survivor takes the isolated vertex if it is
    free (no zombie has a geodesic to it), and otherwise any free vertex (the zombie on the isolated vertex has no
    move). *)
Lemma g314_e2_leaf_lose (k : nat) : 0 < k -> k < 3 -> ~ zombies_win g314_e2_leaf k.
Proof.
move=> k0 k3 [t /existsP [Z0 /forallP h]].
case: (boolP [exists i, Z0 i == b314]) => [/existsP [i /eqP Zi]|/existsPn nb].
- have [s0 ns0] : exists s0 : g314_e2_leaf, s0 \notin [set Z0 i | i in 'I_k].
    apply/existsP; rewrite -negb_forall; apply/negP => /forallP hall.
    have : #|[set: g314_e2_leaf]| <= #|[set Z0 i | i in 'I_k]|.
      by apply: subset_leq_card; apply/subsetP => x _; exact: hall.
    rewrite cardsT card_option card_option card_ord => /leq_trans /(_ (leq_imset_card _ _)).
    by rewrite card_ord leqNgt k3.
  have nc : ~~ zombie_caught Z0 s0.
    by apply/existsPn => j; apply: contra ns0 => /eqP <-; exact: imset_f.
  move: (h s0); rewrite (@zombies_stuck _ k t Z0 s0 i) ?(negbTE nc) //.
  by move=> w; rewrite Zi (negbTE (g314_b_isolated _)).
- have nc : ~~ zombie_caught Z0 b314 by apply/existsPn => j; exact: nb.
  pose i0 : 'I_k := Ordinal k0.
  move: (h b314); rewrite (@zombies_stuck _ k t Z0 b314 i0) ?(negbTE nc) //.
  move=> w e; have wb : w != b314.
    by apply: contraTneq e => ->; rewrite sg_sym (negbTE (g314_b_isolated _)).
  have b_iso : forall z : g314_e2_leaf, ~~ b314 -- z := g314_b_isolated.
  by rewrite !(g314_dist_isolated b_iso) // nb.
Qed.

Lemma g314_e2_leaf_zombie_number : zombie_number g314_e2_leaf 3.
Proof.
split.
  by have := zombies_win_card g314_e2_leaf; rewrite card_option card_option card_ord.
move=> j; case: j => [_|j lt]; first by apply: not_zombies_win_0; rewrite card_option.
exact: g314_e2_leaf_lose.
Qed.

Lemma g314_e2_leaf_pendant : x314_pendant_extension g314_e2 g314_e2_leaf.
Proof.
apply: (@x314_pendant_step _ g314_e2 (Some ord0)); first exact/x314_pendant_refl/inhabits/diso_id.
exact/inhabits/diso_id.
Qed.

(** ** helper_sanity *)

Definition g314_helper_claim : Prop :=
  [/\ (x314_pendant_extension 'K_1 'K_1), (x314_pendant_extension 'K_1 'K_2),
      x314_pendant_extension 'K_1 g314_K1_leaf, x314_pendant_extension g314_e2 g314_e2_leaf
    & forall (H : sgraph) (v : H), N(None : add_node H [set v]) = [set Some v]].

Lemma g314_helper_sanity : g314_helper_claim.
Proof.
split; [exact/x314_pendant_refl/inhabits/diso_id | exact: g314_K2_pendant | exact: g314_K1_leaf_pendant |
        exact: g314_e2_leaf_pendant | exact: g314_leaf_neighbours].
Qed.

(** ** hyp_inhabited *)

Definition g314_R1_at (G G' : sgraph) : Prop :=
  forall z z' : nat, zombie_number G z -> zombie_number G' z' -> z' = z.

Definition g314_R1_hyp_claim : Prop :=
  [/\ connected [set: 'K_1] /\ 0 < #|'K_1|, (x314_pendant_extension 'K_1 'K_2),
      zombie_number 'K_1 1, zombie_number 'K_2 1
    & zombie_number_pendant_vertices_statement -> g314_R1_at 'K_1 'K_2].

Lemma g314_R1_hyp_inhabited : g314_R1_hyp_claim.
Proof.
split; [exact: g314_K1_guards | exact: g314_K2_pendant | exact: zombie_number_K1 |
        exact: g314_K2_zombie_number | ].
by move=> S; case: g314_K1_guards => c n; exact: S _ _ c n g314_K2_pendant.
Qed.

(** The instance holds: both zombie numbers are 1. *)
Lemma g314_R1_at_K1_K2 : g314_R1_at 'K_1 'K_2.
Proof.
move=> z z' hz hz'; rewrite (zombie_number_functional hz zombie_number_K1).
exact: (zombie_number_functional hz' g314_K2_zombie_number).
Qed.

(** ** not_trivially_true *)

Definition g314_R1_unguarded : Prop :=
  forall G G' : sgraph, 0 < #|G| -> x314_pendant_extension G G' -> g314_R1_at G G'.

Definition g314_R1_ntt_claim : Prop :=
  [/\ ~ connected [set: g314_e2], ~ g314_R1_unguarded &
      (g314_R1_unguarded -> zombie_number_pendant_vertices_statement)].

Lemma g314_R1_not_trivially_true : g314_R1_ntt_claim.
Proof.
split.
- apply: (@g314_isolated_disconnected g314_e2 None (Some ord0)) => //; exact: g314_e2_isolated.
- move=> V; have := V _ _ _ g314_e2_leaf_pendant _ _ g314_e2_zombie_number g314_e2_leaf_zombie_number.
  by rewrite card_option => /(_ isT).
- by move=> V G G' _ n0 pe; exact: V G G' n0 pe.
Qed.

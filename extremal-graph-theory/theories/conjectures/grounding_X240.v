(** * Extremal.conjectures.grounding_X240 -- grounding certificates of wave X240.

    For each of the six rows: hyp_inhabited (the hypotheses hold on a concrete instance, and the
    statement then yields its conclusion there) and not_trivially_true in the contract form of
    meta/EXPANSION_PLAN.md 4.4 (the row with a load-bearing hypothesis dropped is false, and that
    variant implies the row): the Turan hypothesis for erdos:146 and the Ramsey hypotheses for
    erdos:159, erdos:986, erdos:1030, erdos:544 and the edge-deletion row (without them the bound
    fails at a small or zero value).  The wave has no local helper, so no helper_sanity certificate.
    Small instances: R(H, K_1) = 1 for nonempty H, R(K_m, K_2) = m, r(D) = |D| for edgeless D,
    K_2 and K_2 with its edge deleted, ex(1; K_2) = 0. *)

From Extremal.conjectures Require Import XE1 D2tur X240.
(* GTBase last: its canonical [edge_count] must shadow D2tur's eta-alias of the same name. *)
From GTBase Require Import base common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Small instances *)

(** No copy of a nonempty graph in a graph without vertices. *)
Lemma g240_no_copy_empty (G H : sgraph) : #|G| = 0 -> 0 < #|H| -> ~ has_subgraph G H.
Proof. by move=> G0 H0 /has_subgraph_card; rewrite G0 leqn0 => /eqP H00; rewrite H00 in H0. Qed.

(** A complete graph on m vertices contains K_m. *)
Lemma g240_complete_embeds (G : sgraph) (m : nat) :
  #|G| = m -> (forall x y : G, x != y -> x -- y) -> has_subgraph G 'K_m.
Proof.
move=> Gm comp; apply/has_subgraphP.
pose f (i : 'I_m) : G := enum_val (cast_ord (esym Gm) i).
have finj : injective f by move=> i j /enum_val_inj /cast_ord_inj.
exists f; split=> // i j ij; apply: comp; by rewrite (inj_eq finj).
Qed.

(** R(H, K_1) = 1 for every nonempty H. *)
Lemma g240_ramsey_K1 (H : sgraph) : 0 < #|H| -> xe1_graph_ramsey_number H 'K_1 1.
Proof.
move=> H0; split.
- move=> G G1; right; apply/has_subgraphP.
  have : 0 < #|G| by rewrite G1.
  case/card_gt0P => v _.
  exists (fun _ => v); split; first by move=> a b _; rewrite (ord1 a) (ord1 b).
  by move=> a b; rewrite (ord1 a) (ord1 b) sg_irrefl.
- case=> // h; exfalso; have [] := h 'K_0 (card_ord 0).
  + exact: (@g240_no_copy_empty 'K_0 H (card_ord 0) H0).
  + by apply: (@g240_no_copy_empty (compl 'K_0) 'K_1 (card_ord 0)); rewrite card_ord.
Qed.

(** R(K_m, K_2) = m: an m-vertex graph is complete or has a non-edge. *)
Lemma g240_ramsey_Km_K2 (m : nat) : xe1_graph_ramsey_number 'K_m 'K_2 m.
Proof.
split.
- move=> G Gm.
  case: (boolP [forall x : G, forall y : G, (x != y) ==> (x -- y)]) => [/forallP h | /forallPn [x /forallPn [y]]].
  + left; apply: g240_complete_embeds Gm _ => x y xy.
    by have /forallP/(_ y)/implyP := h x; apply.
  + rewrite negb_imply => /andP [xy nxy]; right; apply/has_subgraphP.
    exists (fun i : 'I_2 => if i == ord0 then x else y); split.
    * move=> i j /=; case: (i =P ord0) => [-> | /eqP i0]; case: (j =P ord0) => [-> | /eqP j0] //.
      - by move=> e; move: xy; rewrite e eqxx.
      - by move=> e; move: xy; rewrite e eqxx.
      - by move=> _; apply/eqP; move: i j i0 j0 => [[|[|i]] Hi] [[|[|j]] Hj].
    * move=> i j /=; case: (i =P ord0) => [-> | /eqP i0]; case: (j =P ord0) => [-> | /eqP j0] //=; rewrite ?sg_irrefl //.
      - by move=> _; rewrite /edge_rel /= xy nxy.
      - by move=> _; rewrite /edge_rel /= eq_sym xy sg_sym nxy.
      - by move=> ij; exfalso; move: i j i0 j0 ij => [[|[|i]] Hi] [[|[|j]] Hj].
- move=> R' h; rewrite leqNgt; apply/negP => R'm.
  have [] := h 'K_R' (card_ord R').
  + by move/has_subgraph_card; rewrite !card_ord leqNgt R'm.
  + move/has_subgraphP => [f [finj fe]].
    have := fe ord0 (Ordinal (isT : 1 < 2)) isT.
    by rewrite /edge_rel /= andbN.
Qed.

(** r(D) = |D| for an edgeless D. *)
Lemma g240_ramsey_edgeless (D : sgraph) :
  (forall x y : D, ~~ x -- y) -> xe1_diagonal_ramsey_number D #|D|.
Proof.
move=> noE; split.
- move=> G GD; left; apply/has_subgraphP.
  pose f (d : D) : G := enum_val (cast_ord (esym GD) (enum_rank d)).
  exists f; split; first by move=> a b /enum_val_inj /cast_ord_inj /enum_rank_inj.
  by move=> a b; rewrite (negbTE (noE a b)).
- move=> R' hR; rewrite leqNgt; apply/negP => lt.
  by have [] := hR 'K_R' (card_ord R'); move/has_subgraph_card; rewrite card_ord leqNgt lt.
Qed.

(** K_2 with its edge deleted is edgeless. *)
Lemma g240_K2_del_edgeless (a b : del_edge_set 'K_2 [set [set (ord0 : 'I_2); ord_max]]) : ~~ a -- b.
Proof.
rewrite del_edge_setE in_set1 negb_and negbK; move: a b => [[|[|a]] Ha] [[|[|b]] Hb] //=; rewrite ?sg_irrefl //.
all: apply/eqP/setP => z; rewrite !inE; move: z => [[|[|z]] Hz] //=.
Qed.

Lemma g240_K2_bipartite : bipartite 'K_2.
Proof.
exists (fun x : 'K_2 => x == ord0) => x y.
by case: x => [[|[|x]] hx] //; case: y => [[|[|y]] hy].
Qed.

Lemma g240_K2_degenerate : k_degenerate 'K_2 1.
Proof.
move=> S _ /set0Pn [x xS]; exists x; split=> //.
apply: leq_trans (subset_leq_card (subsetIl _ _)) _.
apply: leq_trans (subset_leq_card (_ : N(x) \subset [set~ x])) _.
- by apply/subsetP => y; rewrite !inE => xy; rewrite eq_sym (sg_edgeNeq xy).
- by rewrite cardsC1 card_ord.
Qed.

(** ex(1; K_2) = 0. *)
Lemma g240_turan_K2_1 : is_turan_number 1 (fun _ : 'I_1 => 'K_2) 0.
Proof.
split.
- exists 'K_1; split; [by rewrite card_ord | by rewrite /D2tur.edge_count (proj2 edge_count_K0_K1) |].
  by move=> i [h hi _]; have := leq_card h hi; rewrite !card_ord.
- move=> m' [G [hG <- _]].
  pose h (v : G) : 'K_1 := cast_ord hG (enum_rank v).
  have hi : injective h by move=> x y /cast_ord_inj /enum_rank_inj.
  have e : #|E(G)| <= #|E('K_1)|.
    apply: (@sub_card_edge G 'K_1 h hi) => x y xy.
    by rewrite /edge_rel /= (inj_eq hi) (sg_edgeNeq xy).
  apply: leq_trans e _.
  by rewrite -[X in X <= _]/(edge_count 'K_1) (proj2 edge_count_K0_K1).
Qed.

(** ** Row erdos:146 *)

Definition g240_degen_hyp_claim : Prop :=
  [/\ (bipartite 'K_2), k_degenerate 'K_2 1, is_turan_number 1 (fun _ : 'I_1 => 'K_2) 0 &
      (degenerate_bipartite_turan_exponent_statement -> exists C : nat, forall n m : nat,
         is_turan_number n (fun _ : 'I_1 => 'K_2) m -> m ^ 1 * n <= C ^ 1 * n ^ (2 * 1))].

Theorem g240_degen_hyp_inhabited : g240_degen_hyp_claim.
Proof.
split; [exact: g240_K2_bipartite | exact: g240_K2_degenerate | exact: g240_turan_K2_1 |].
by move=> h; exact: h 1 (leqnn 1) 'K_2 g240_K2_bipartite g240_K2_degenerate.
Qed.

(** Contract form: without the Turan hypothesis, m = C + 1 at n = 1 breaks the bound. *)
Definition g240_degen_no_turan : Prop :=
  forall r : nat, 1 <= r -> forall H : sgraph, bipartite H -> k_degenerate H r ->
    exists C : nat, forall n m : nat, m ^ r * n <= C ^ r * n ^ (2 * r).

Definition g240_degen_ntt_claim : Prop :=
  ~ g240_degen_no_turan /\ (g240_degen_no_turan -> degenerate_bipartite_turan_exponent_statement).

Theorem g240_degen_not_trivially_true : g240_degen_ntt_claim.
Proof.
split.
- move=> h; have [C hC] := h 1 (leqnn 1) 'K_2 g240_K2_bipartite g240_K2_degenerate.
  by have := hC 1 C.+1; rewrite !expn1 !exp1n !muln1 ltnn.
- by move=> h r r1 H Hb Hd; have [C hC] := h r r1 H Hb Hd; exists C => n m _; exact: hC.
Qed.

(** ** Row erdos:159 *)

Lemma g240_ramsey_C4_K1 : xe1_graph_ramsey_number (cycle_graph 4) 'K_1 1.
Proof. by apply: g240_ramsey_K1; rewrite card_ord. Qed.

Definition g240_c4_hyp_claim : Prop :=
  [/\ xe1_graph_ramsey_number (cycle_graph 4) 'K_1 1 &
      (c4_clique_ramsey_power_saving_statement -> exists a b C : nat,
         [/\ 0 < a, 0 < b & 1 ^ b * 1 ^ a <= C ^ b * 1 ^ (2 * b)])].

Theorem g240_c4_hyp_inhabited : g240_c4_hyp_claim.
Proof.
split; first exact: g240_ramsey_C4_K1.
by move=> [a [b [C [a0 b0 h]]]]; exists a, b, C; split=> //; exact: h 1 1 g240_ramsey_C4_K1.
Qed.

(** Contract form: without the Ramsey hypothesis, R = C + 1 at n = 1 breaks the bound. *)
Definition g240_c4_no_ramsey : Prop :=
  exists a b C : nat, [/\ 0 < a, 0 < b & forall n R : nat, R ^ b * n ^ a <= C ^ b * n ^ (2 * b)].

Definition g240_c4_ntt_claim : Prop :=
  ~ g240_c4_no_ramsey /\ (g240_c4_no_ramsey -> c4_clique_ramsey_power_saving_statement).

Theorem g240_c4_not_trivially_true : g240_c4_ntt_claim.
Proof.
split.
- move=> [a [b [C [a0 b0 h]]]]; have := h 1 C.+1; rewrite !exp1n !muln1 leqNgt.
  by rewrite ltn_exp2r // ltnSn.
- by move=> [a [b [C [a0 b0 h]]]]; exists a, b, C; split=> // n R _; exact: h.
Qed.

(** ** Row erdos:986 *)

Lemma g240_ramsey_K3_K1 : xe1_graph_ramsey_number 'K_3 'K_1 1.
Proof. by apply: g240_ramsey_K1; rewrite card_ord. Qed.

Definition g240_polylog_hyp_claim : Prop :=
  [/\ xe1_graph_ramsey_number 'K_3 'K_1 1 &
      (clique_ramsey_polylog_lower_statement -> exists c p n0 : nat, 0 < p /\
         forall n R : nat, n0 <= n -> xe1_graph_ramsey_number 'K_3 'K_n R ->
           n ^ 3 <= p * R * n * trunc_log 2 n ^ c)].

Theorem g240_polylog_hyp_inhabited : g240_polylog_hyp_claim.
Proof. by split; [exact: g240_ramsey_K3_K1 | move=> h; exact: h 3 (leqnn 3)]. Qed.

(** Contract form: without the Ramsey hypothesis, R = 0 breaks the bound. *)
Definition g240_polylog_no_ramsey : Prop :=
  forall k : nat, 3 <= k -> exists c p n0 : nat, 0 < p /\
    forall n R : nat, n0 <= n -> n ^ k <= p * R * n * trunc_log 2 n ^ c.

Definition g240_polylog_ntt_claim : Prop :=
  ~ g240_polylog_no_ramsey /\ (g240_polylog_no_ramsey -> clique_ramsey_polylog_lower_statement).

Theorem g240_polylog_not_trivially_true : g240_polylog_ntt_claim.
Proof.
split.
- move=> h; have [c [p [n0 [p0 hp]]]] := h 3 (leqnn 3).
  by have := hp n0.+1 0 (leqnSn n0); rewrite muln0 !mul0n leqn0 expn_eq0.
- by move=> h k k3; have [c [p [n0 [p0 hp]]]] := h k k3; exists c, p, n0; split=> // n R nn _; exact: hp.
Qed.

(** ** Row erdos:1030 *)

Lemma g240_ramsey_K1_K1 : xe1_graph_ramsey_number 'K_1 'K_1 1.
Proof. by apply: g240_ramsey_K1; rewrite card_ord. Qed.

Lemma g240_ramsey_K2_K1 : xe1_graph_ramsey_number 'K_2 'K_1 1.
Proof. by apply: g240_ramsey_K1; rewrite card_ord. Qed.

Definition g240_ratio_hyp_claim : Prop :=
  [/\ xe1_graph_ramsey_number 'K_1 'K_1 1, xe1_graph_ramsey_number 'K_2 'K_1 1 &
      (consecutive_diagonal_ramsey_ratio_statement -> exists q : nat, 1 <= q /\ exists k0 : nat,
         forall k R0 R1 : nat, k0 <= k ->
           xe1_graph_ramsey_number 'K_k 'K_k R0 -> xe1_graph_ramsey_number 'K_k.+1 'K_k R1 ->
           (q + 1) * R0 < q * R1)].

Theorem g240_ratio_hyp_inhabited : g240_ratio_hyp_claim.
Proof. by split; [exact: g240_ramsey_K1_K1 | exact: g240_ramsey_K2_K1 | ]. Qed.

(** Contract form: without the Ramsey hypotheses, R0 = R1 = 0 breaks the strict inequality. *)
Definition g240_ratio_no_ramsey : Prop :=
  exists q : nat, 1 <= q /\ exists k0 : nat, forall k R0 R1 : nat, k0 <= k -> (q + 1) * R0 < q * R1.

Definition g240_ratio_ntt_claim : Prop :=
  ~ g240_ratio_no_ramsey /\ (g240_ratio_no_ramsey -> consecutive_diagonal_ramsey_ratio_statement).

Theorem g240_ratio_not_trivially_true : g240_ratio_ntt_claim.
Proof.
split.
- by move=> [q [q1 [k0 h]]]; have := h k0 0 0 (leqnn k0); rewrite !muln0.
- by move=> [q [q1 [k0 h]]]; exists q; split=> //; exists k0 => k R0 R1 kk _ _; exact: h.
Qed.

(** ** Row erdos:544 *)

Definition g240_incr_hyp_claim : Prop :=
  [/\ xe1_graph_ramsey_number 'K_3 'K_1 1, xe1_graph_ramsey_number 'K_3 'K_2 3 &
      (triangle_ramsey_increment_unbounded_statement -> exists k0 : nat, forall k R0 R1 : nat, k0 <= k ->
         xe1_graph_ramsey_number 'K_3 'K_k R0 -> xe1_graph_ramsey_number 'K_3 'K_k.+1 R1 -> R0 + 1 <= R1)].

Theorem g240_incr_hyp_inhabited : g240_incr_hyp_claim.
Proof.
split; [exact: g240_ramsey_K3_K1 | | by move=> h; exact: h 1].
by move: (g240_ramsey_Km_K2 3).
Qed.

(** Contract form: without the Ramsey hypotheses, R0 = 1 and R1 = 0 break the bound. *)
Definition g240_incr_no_ramsey : Prop :=
  forall M : nat, exists k0 : nat, forall k R0 R1 : nat, k0 <= k -> R0 + M <= R1.

Definition g240_incr_ntt_claim : Prop :=
  ~ g240_incr_no_ramsey /\ (g240_incr_no_ramsey -> triangle_ramsey_increment_unbounded_statement).

Theorem g240_incr_not_trivially_true : g240_incr_ntt_claim.
Proof.
split.
- by move=> h; have [k0 hk] := h 0; have := hk k0 1 0 (leqnn k0).
- by move=> h M; have [k0 hk] := h M; exists k0 => k R0 R1 kk _ _; exact: hk.
Qed.

(** ** Row studies:std_wigderson_s_edge_deletion_ramsey_conjecture *)

Definition g240_wig_hyp_claim : Prop :=
  [/\ (ord0 : 'K_2) -- ord_max, xe1_diagonal_ramsey_number 'K_2 2,
      xe1_diagonal_ramsey_number (del_edge_set 'K_2 [set [set (ord0 : 'I_2); ord_max]]) 2 &
      (edge_deletion_ramsey_constant_factor_statement -> exists C : nat, 2 <= C * 2)].

Theorem g240_wig_hyp_inhabited : g240_wig_hyp_claim.
Proof.
have r1 : xe1_diagonal_ramsey_number 'K_2 2 := g240_ramsey_Km_K2 2.
have r0 : xe1_diagonal_ramsey_number (del_edge_set 'K_2 [set [set (ord0 : 'I_2); ord_max]]) 2.
  by have := g240_ramsey_edgeless (@g240_K2_del_edgeless); rewrite card_ord.
split=> //.
by move=> [C h]; exists C; exact: h 'K_2 ord0 ord_max 2 2 isT r1 r0.
Qed.

(** Contract form: without the Ramsey hypotheses, R1 = 1 and R0 = 0 on K_2 break the bound. *)
Definition g240_wig_no_ramsey : Prop :=
  exists C : nat, forall (G : sgraph) (x y : G) (R1 R0 : nat), x -- y -> R1 <= C * R0.

Definition g240_wig_ntt_claim : Prop :=
  ~ g240_wig_no_ramsey /\ (g240_wig_no_ramsey -> edge_deletion_ramsey_constant_factor_statement).

Theorem g240_wig_not_trivially_true : g240_wig_ntt_claim.
Proof.
split.
- by move=> [C h]; have := h 'K_2 ord0 ord_max 1 0 isT; rewrite muln0.
- by move=> [C h]; exists C => G x y R1 R0 xy _ _; exact: (h G x y R1 R0 xy).
Qed.

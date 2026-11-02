(** * Extremal.conjectures.grounding_X280 -- grounding certificates of wave X280.

    For each of the two rows: hyp_inhabited (the hypotheses hold on a concrete instance, and the statement gives its
    consequence there) and not_trivially_true in the contract form (a variant obtained from the body by deleting one
    hypothesis is false and implies the row); helper_sanity for [x280_congestion_at_most] in row 1.
    - Pure pairs: H0 = add_node K_2 set0 (three vertices, one edge) has congestion at most 1 / q for every q, and K_2
      (|K_2| = 2 > 1) is H0-free and complement-H0-free (fewer vertices); the statement gives, at c = 1, a pure pair of
      K_2 with both sides nonempty.  Without |G| > 1 the row is false at c = 1, H = H0, G = K_1: K_1 is H0-free and
      complement-H0-free, but has no two disjoint nonempty vertex sets.
    - Congestion: a graph with at most one edge has congestion at most 1 / q for every q (one edge inside S forces
      |S| >= 2), and K_3 (congestion 1 / 3) is not at most 1 / 4: J = K_3 gives 4 * 3 > 4 * 2 + 3.
    - Erdos #805: graphs on every order exist (K_n), and for n = 2^j, j >= 10, the whole vertex set has at least
      (log_2 n)^3 = j^3 vertices (j^3 <= 2^j); the statement gives, eventually along n = 2^j, a graph with a clique and
      an independent set of size j.  Without the size hypothesis on S the row is false: in a graph on n >= 3 vertices
      a single vertex holds no clique of size log_2 n. *)

From Extremal.conjectures Require Import X280.
From GTBase Require Import base set_pairs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Row 1 and the helper: congestion, pure pairs *)

(** An edge of a simple graph is a set of two vertices. *)
Lemma g280_card_edge (G : sgraph) (e : {set G}) : e \in E(G) -> #|e| = 2.
Proof. by case/edgesP => x [y [-> xy]]; rewrite cards2 (sg_edgeNeq xy). Qed.

(** A graph with at most one edge has congestion at most 1 / q for every q. *)
Lemma g280_congestion_le1 (H : sgraph) (q : nat) : #|E(H)| <= 1 -> x280_congestion_at_most H q.
Proof.
move=> h1 S F FE FS F0.
have F1 : #|F| = 1 by apply/eqP; rewrite eqn_leq F0 andbT (leq_trans (subset_leq_card FE) h1).
have /card_gt0P [e eF] := F0.
have S2 : 2 <= #|S| by rewrite -(g280_card_edge (subsetP FE e eF)); exact: subset_leq_card (FS e eF).
rewrite F1 muln1; apply: leq_trans (leq_addr _ _).
by rewrite -{1}[q]muln1 leq_mul2l subn_gt0 S2 orbT.
Qed.

(** H0: K_2 with one isolated vertex added; three vertices, one edge. *)
Definition g280_H0 : sgraph := add_node ('K_2) set0.

Lemma g280_H0_card : #|g280_H0| = 3.
Proof. by rewrite card_option card_ord. Qed.

Lemma g280_H0_edges : #|E(g280_H0)| = 1.
Proof. by rewrite /g280_H0 card_edge_add_node cards0 card_edge_Kn. Qed.

Lemma g280_H0_congestion (q : nat) : x280_congestion_at_most g280_H0 q.
Proof. by apply: g280_congestion_le1; rewrite g280_H0_edges. Qed.

(** K_3 does not have congestion at most 1 / 4: J = K_3 itself. *)
Lemma g280_K3_not_quarter : ~ x280_congestion_at_most ('K_3) 4.
Proof.
move=> h; have := h [set: 'K_3] E('K_3) (subxx _) (fun e _ => subsetT e).
by rewrite card_sg_edge_set_K3 cardsT card_ord => /(_ isT).
Qed.

Definition g280_cg_helper_claim : Prop :=
  [/\ forall q : nat, x280_congestion_at_most g280_H0 q,
      forall (H : sgraph) (q : nat), #|E(H)| <= 1 -> x280_congestion_at_most H q &
      ~ x280_congestion_at_most ('K_3) 4].

Theorem g280_cg_helper_sanity : g280_cg_helper_claim.
Proof. by split; [exact: g280_H0_congestion | exact: g280_congestion_le1 | exact: g280_K3_not_quarter]. Qed.

Definition g280_pp_hyp_claim : Prop :=
  [/\ 0 < 1, forall q : nat, x280_congestion_at_most g280_H0 q, 1 < #|('K_2)|,
      induced_free ('K_2) g280_H0 /\ induced_free ('K_2) (compl g280_H0) &
      (pure_pairs_linear_side_small_congestion_statement ->
         exists m : nat, 0 < m /\ exists A B : {set ('K_2)},
           [/\ [disjoint A & B], complete_between A B || anticomplete A B, 2 <= m * #|A| & 1 <= m * #|B|])].

Theorem g280_pp_hyp_inhabited : g280_pp_hyp_claim.
Proof.
have fr : induced_free ('K_2) g280_H0 /\ induced_free ('K_2) (compl g280_H0).
  by split; apply: induced_free_card; rewrite ?card_ord g280_H0_card.
split=> //; [exact: g280_H0_congestion | by rewrite card_ord |].
move=> h; have [q [q0 hq]] := h 1 isT.
have [m [m0 hm]] := hq g280_H0 (g280_H0_congestion q).
case: fr => fr1 fr2; have := hm ('K_2); rewrite card_ord => /(_ isT fr1 fr2) [A [B [dAB pAB sA sB]]].
by exists m; split=> //; exists A, B; split=> //; move: sB; rewrite expn0 expn1.
Qed.

(** The variant without |G| > 1. *)
Definition g280_pp_no_order : Prop :=
  forall k : nat, 0 < k -> exists q : nat, 0 < q /\
    forall H : sgraph, x280_congestion_at_most H q -> exists m : nat, 0 < m /\
      forall G : sgraph, induced_free G H -> induced_free G (compl H) ->
        exists A B : {set G},
          [/\ [disjoint A & B], complete_between A B || anticomplete A B,
              #|G| <= m * #|A| & #|G| ^ (k - 1) <= (m * #|B|) ^ k].

Definition g280_pp_ntt_claim : Prop :=
  ~ g280_pp_no_order /\ (g280_pp_no_order -> pure_pairs_linear_side_small_congestion_statement).

Theorem g280_pp_not_trivially_true : g280_pp_ntt_claim.
Proof.
split; last first.
  move=> h k k0; have [q [q0 hq]] := h k k0; exists q; split=> // H cH.
  by have [m [m0 hm]] := hq H cH; exists m; split=> // G _; exact: hm.
move=> h; have [q [q0 hq]] := h 1 isT.
have [m [m0 hm]] := hq g280_H0 (g280_H0_congestion q).
have fr1 : induced_free ('K_1) g280_H0 by apply: induced_free_card; rewrite card_ord g280_H0_card.
have fr2 : induced_free ('K_1) (compl g280_H0) by apply: induced_free_card; rewrite card_ord g280_H0_card.
have [A [B [dAB _ sA sB]]] := hm ('K_1) fr1 fr2.
move: sA sB; rewrite card_ord expn0 expn1 => sA sB.
move: sA sB; rewrite !muln_gt0 => /andP [_ /card_gt0P [a aA]] /andP [_ /card_gt0P [b bB]].
by move: (disjointFr dAB aA); rewrite (ord1 a) -(ord1 b) bB.
Qed.

(** ** Row 2: Erdos #805 *)

Lemma g280_cube_le_pow2 (j : nat) : 10 <= j -> j ^ 3 <= 2 ^ j.
Proof.
elim: j => // j IH; rewrite leq_eqVlt => /orP [/eqP <- // | j10].
have j10' : 10 <= j by rewrite -ltnS.
have IH' := IH j10'.
rewrite (expnS 2 j).
apply: (@leq_trans (2 * j ^ 3)); last by rewrite leq_mul2l IH'.
have h1 : 4 * j.+1 <= 5 * j by rewrite mulnS (mulSn 4 j) leq_add2r (leq_trans _ j10').
have h2 : (4 * j.+1) ^ 3 <= (5 * j) ^ 3 by rewrite leq_exp2r.
rewrite !expnMn in h2.
rewrite -(@leq_pmul2l (4 ^ 3)) //.
apply: (leq_trans h2).
by rewrite mulnA leq_mul2r orbC.
Qed.

(** For n = 2^j, j >= 10, every vertex set with n vertices passes the size test of (log_2 n)^3 = j^3. *)
Lemma g280_size_full (j : nat) : 10 <= j ->
  forall a b : nat, 0 < b -> 2 ^ a < (2 ^ j) ^ b -> a ^ 3 <= 2 ^ j * b ^ 3.
Proof.
move=> j10 a b b0; rewrite -expnM ltn_exp2l // => ajb.
apply: (@leq_trans ((j * b) ^ 3)); first by rewrite leq_exp2r // ltnW.
by rewrite expnMn leq_mul2r g280_cube_le_pow2 ?orbT.
Qed.

Definition g280_e805_hyp_claim : Prop :=
  [/\ forall n : nat, #|('K_n)| = n,
      forall j : nat, 10 <= j -> forall a b : nat, 0 < b -> 2 ^ a < (2 ^ j) ^ b ->
        a ^ 3 <= #|[set: ('K_(2 ^ j))]| * b ^ 3 &
      (erdos_805_log_cubed_window_statement -> exists n0 : nat, forall j : nat, 10 <= j -> n0 <= 2 ^ j ->
         exists G : sgraph, #|G| = 2 ^ j /\
           exists K I : {set G}, [/\ cliqueb K, stable I, j <= #|K| & j <= #|I|])].

Theorem g280_e805_hyp_inhabited : g280_e805_hyp_claim.
Proof.
split; [by move=> n; rewrite card_ord | by move=> j j10 a b b0; rewrite cardsT card_ord; exact: g280_size_full |].
move=> [n0 hn]; exists n0 => j j10 nj; have [G [cG hG]] := hn _ nj.
have := hG [set: G]; rewrite cardsT cG => /(_ (g280_size_full j10)) [K [I [_ _ cK sI /andP [nK nI]]]].
by exists G; split=> //; exists K, I; split=> //; rewrite -(leq_exp2l _ _ (isT : 1 < 2)).
Qed.

(** The variant without the size hypothesis on S. *)
Definition g280_e805_every_set : Prop :=
  exists n0 : nat, forall n : nat, n0 <= n -> exists G : sgraph, #|G| = n /\
    forall S : {set G},
      exists K I : {set G},
        [/\ K \subset S, I \subset S, cliqueb K, stable I & (n <= 2 ^ #|K|) && (n <= 2 ^ #|I|)].

Definition g280_e805_ntt_claim : Prop :=
  ~ g280_e805_every_set /\ (g280_e805_every_set -> erdos_805_log_cubed_window_statement).

Theorem g280_e805_not_trivially_true : g280_e805_ntt_claim.
Proof.
split; last first.
  by move=> [n0 hn]; exists n0 => n nn; have [G [cG hG]] := hn n nn; exists G; split=> // S _; exact: hG.
move=> [n0 hn]; have [G [cG hG]] := hn (n0 + 3) (leq_addr _ _).
have /card_gt0P [v _] : 0 < #|G| by rewrite cG addn3.
have [K [I [KS _ _ _ /andP [nK _]]]] := hG [set v].
have K1 : #|K| <= 1 by rewrite -(cards1 v); exact: subset_leq_card.
have : n0 + 3 <= 2 by apply: leq_trans nK _; rewrite -[2]expn1 leq_exp2l.
by rewrite addn3.
Qed.

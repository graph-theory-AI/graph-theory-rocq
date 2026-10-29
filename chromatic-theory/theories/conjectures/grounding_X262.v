(** * Chromatic.conjectures.grounding_X262 -- grounding certificates for wave X262 (2026-10-29)

    For each of the four rows: hyp_inhabited (the hypotheses hold at a small graph, and the statement then gives its
    conclusion there) and not_trivially_true (a variant without one hypothesis is false and implies the statement).
    The wave has no local helper, so there is no helper_sanity certificate.  Value lemmas: C_5 has fractional
    chromatic number at most 5/2 (an (5:2)-fold colouring), f_4(4) = 3 (every K_4-free graph on 4 vertices has
    chromatic number at most 3, and K_4 minus an edge reaches 3), K_(d+1) is d-degenerate with chromatic and clique
    number d + 1, and an (a:b)-fold colouring of K_n has n b <= a. *)

From GTBase Require Import base common bfold_colourings.
From Chromatic.conjectures Require Import X130 X262.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Small graphs ************************************************************ *)

(** In K_(d+1) every vertex has at most d neighbours. *)
Lemma g262_K_N_card (d : nat) (x : 'K_d.+1) : #|N(x)| <= d.
Proof.
have : N(x) \subset [set~ x].
  by apply/subsetP => v; rewrite in_opn !inE; apply: contraTneq => ->; rewrite sg_irrefl.
by move/subset_leq_card; rewrite cardsC1 card_ord.
Qed.

Lemma g262_Delta_K (d : nat) : Delta ('K_d.+1) <= d.
Proof. by apply/bigmax_leqP => x _; exact: g262_K_N_card. Qed.

(** K_(d+1) is d-degenerate with chromatic and clique number d + 1. *)
Lemma g262_complete_degenerate (d : nat) :
  [/\ k_degenerate ('K_d.+1) d, χ([set: ('K_d.+1)]) = d.+1 & ω([set: ('K_d.+1)]) = d.+1].
Proof.
have cl : clique [set: ('K_d.+1)] by move=> x y _ _ xy; rewrite /edge_rel /= xy.
have chiK : χ([set: ('K_d.+1)]) = d.+1 by rewrite chi_clique // cardsT card_ord.
split=> //.
- move=> S _ /set0Pn [x xS]; exists x; split=> //.
  exact: leq_trans (subset_leq_card (subsetIl _ _)) (g262_K_N_card x).
- apply/eqP; rewrite eqn_leq -[X in _ <= X]chiK omega_leq_chi /=.
  by rewrite -[X in X <= _](card_ord d.+1) -cardsT; apply: clique_bound; rewrite inE subxx; apply/cliqueP.
Qed.

(** An (a:b)-fold colouring of K_n uses n pairwise disjoint b-sets of 'I_a, so n b <= a. *)
Lemma g262_bfold_K_le (n a b : nat) (f : 'K_n -> {set 'I_a}) : bfold_colouring b f -> n * b <= a.
Proof.
move=> [card disj].
have -> : n * b = \sum_(v : 'K_n) #|f v| by rewrite (eq_bigr (fun _ => b)) // sum_nat_const card_ord.
rewrite (eq_bigr (fun v => \sum_(c : 'I_a) (c \in f v))); first by move=> v _;
  rewrite -sum1_card big_mkcond /=; apply: eq_bigr => c _; case: (c \in f v).
rewrite exchange_big /= -[X in _ <= X]card_ord -sum1_card; apply: leq_sum => c _.
case: (pickP (fun i => c \in f i)) => [i0 ci0|none]; last by rewrite big1 // => i _; rewrite none.
rewrite (bigD1 i0) //= ci0 big1 // => j ji0; have := disj j i0 ji0.
by rewrite -setI_eq0 => /eqP/setP/(_ c); rewrite !inE ci0 andbT => ->.
Qed.

(** chi_f(K_n) >= n: x130_frac_chi_le ('K_n) p q forces n q <= p. *)
Lemma g262_frac_chi_K (n p q : nat) : x130_frac_chi_le ('K_n) p q -> n * q <= p.
Proof.
case=> a [b] [f] [bpos col le].
have nb : n * b <= a := g262_bfold_K_le col.
by rewrite -(leq_pmul2r bpos) mulnAC (leq_trans (leq_mul nb (leqnn q))) // mulnC (mulnC p).
Qed.

(** C_5's (5:2)-fold colouring: vertex i gets the colours 2i and 2i + 1 (mod 5). *)
Definition g262_C5_col (v : cycle_graph 5) : {set 'I_5} :=
  [set inord ((2 * v) %% 5); inord ((2 * v).+1 %% 5)].

Lemma g262_C5_bfold : x130_bfold_colouring 2 g262_C5_col.
Proof.
rewrite /x130_bfold_colouring; apply/bfold_colouringP; apply/andP; split.
  apply/forallP; case=> -[|[|[|[|[|i]]]]] Hi //; apply/eqP; rewrite /g262_C5_col cards2;
  by apply/eqP; rewrite -val_eqE /= !inordK.
apply/forallP => -[[|[|[|[|[|i]]]]] Hi] //; apply/forallP => -[[|[|[|[|[|j]]]]] Hj] //; apply/implyP => //= _;
  rewrite -setI_eq0; apply/eqP/setP => c; rewrite /g262_C5_col !inE -!val_eqE /= !inordK //;
  by case: c => -[|[|[|[|[|k]]]]] Hk //=.
Qed.

(** chi_f(C_5) <= 5/2. *)
Lemma g262_frac_chi_C5 : x130_frac_chi_le (cycle_graph 5) 5 2.
Proof. by exists 5, 2, g262_C5_col; split=> //; exact: g262_C5_bfold. Qed.

(** Two non-adjacent vertices of a 4-vertex graph can share a colour, so its chromatic number is at most 3. *)
Lemma g262_chi_le3_nonedge (G : sgraph) (x y : G) :
  #|G| = 4 -> x != y -> ~~ x -- y -> χ([set: G]) <= 3.
Proof.
move=> cardG xy nxy.
have st : stable [set x; y].
  apply/stableP => u v; rewrite !inE => /orP[] /eqP-> /orP[] /eqP->; rewrite ?sg_irrefl //.
  by rewrite sg_sym.
apply: leq_trans (chiD1 [set: G] st) _.
rewrite ltnS; apply: leq_trans (leq_chi _) _.
by rewrite cardsDS ?subsetT // cardsT cardG cards2 xy.
Qed.

(** f_4(4) <= 3: every K_4-free graph on 4 vertices misses an edge. *)
Lemma g262_f44_upper (G : sgraph) : #|G| = 4 -> ω([set: G]) < 4 -> χ([set: G]) <= 3.
Proof.
move=> cardG om.
have /cliquePn [x [y [_ _ xy nxy]]] : ~~ cliqueb [set: G].
  apply: contraTN om => cl; rewrite -leqNgt -[X in X <= _]cardG -cardsT.
  by apply: clique_bound; rewrite inE subxx cl.
exact: g262_chi_le3_nonedge cardG xy nxy.
Qed.

(** K_4 minus the edge {0, 1}. *)
Definition g262_K4e : sgraph := fg_mk_sgraph (fun i j : 'I_4 => (i != j) && ((2 <= i) || (2 <= j))).

(** f_4(4) >= 3: K_4 minus an edge is K_4-free with chromatic number 3. *)
Lemma g262_f44_witness : [/\ #|g262_K4e| = 4, ω([set: g262_K4e]) < 4 & χ([set: g262_K4e]) = 3].
Proof.
have le3 : χ([set: g262_K4e]) <= 3.
  apply: (@g262_chi_le3_nonedge g262_K4e (inord 0 : 'I_4) (inord 1 : 'I_4)); first exact: card_ord.
    by rewrite -val_eqE /= !inordK.
  by rewrite /edge_rel /= /fg_srel /= -!val_eqE /= !inordK.
have ge3 : 3 <= ω([set: g262_K4e]).
  pose v0 : g262_K4e := (inord 0 : 'I_4); pose v2 : g262_K4e := (inord 2 : 'I_4).
  pose v3 : g262_K4e := (inord 3 : 'I_4).
  have -> : 3 = #|v0 |: (v2 |: [set v3])| by rewrite !cardsU1 cards1 !inE /v0 /v2 /v3 -!val_eqE /= !inordK.
  apply: clique_bound; rewrite inE subsetT /=; apply/cliqueP => u v.
  by rewrite !inE => /or3P[] /eqP-> /or3P[] /eqP->; rewrite /v0 /v2 /v3 /edge_rel /= /fg_srel /= -?val_eqE /= ?inordK.
split; first exact: card_ord.
  by apply: leq_ltn_trans (omega_leq_chi _) _.
by apply/eqP; rewrite eqn_leq le3 (leq_trans ge3 (omega_leq_chi _)).
Qed.

(** m^2 <= 2^m from m = 4 on. *)
Lemma g262_sq_le_exp2 (m : nat) : 4 <= m -> m ^ 2 <= 2 ^ m.
Proof.
elim: m => // m IH; rewrite leq_eqVlt => /orP[/eqP <- //|]; rewrite ltnS => m4.
apply: (@leq_trans (2 * m ^ 2)); last by rewrite [2 ^ m.+1]expnS leq_pmul2l // IH.
rewrite mul2n -addnn -{1}addn1 sqrnD exp1n !muln1 -addnA leq_add2l.
by rewrite add1n expnS expn1 ltn_mul2r; apply/andP; split; apply: ltn_trans m4.
Qed.

(** ** erdos:920 ************************************************************** *)

(** hyp_inhabited: k = 4 is in range; f_4(4) = 3 (the witness K_4 minus an edge and the upper bound); the statement
    at k = 4 is n^2 <= C chi^3 (trunc_log 2 n)^(3c). *)
Definition g262_kf_hyp_claim : Prop :=
  [/\ 4 <= 4, [/\ #|g262_K4e| = 4, ω([set: g262_K4e]) < 4 & χ([set: g262_K4e]) = 3],
      (forall G : sgraph, #|G| = 4 -> ω([set: G]) < 4 -> χ([set: G]) <= 3) &
      (kk_free_chromatic_lower_bound_statement ->
         exists c C N : nat, forall n : nat, N <= n ->
           exists G : sgraph,
             [/\ #|G| = n, ω([set: G]) < 4 & n ^ 2 <= C * χ([set: G]) ^ 3 * trunc_log 2 n ^ (c * 3)])].

Theorem g262_kf_hyp_inhabited : g262_kf_hyp_claim.
Proof. by split; [| exact: g262_f44_witness | exact: g262_f44_upper | move/(_ 4 isT)]. Qed.

(** not_trivially_true: without the guard k >= 4, k = 0 asks for graphs with clique number below 0. *)
Definition g262_kf_no_guard : Prop :=
  forall k : nat,
    exists c C N : nat,
      forall n : nat, N <= n ->
        exists G : sgraph,
          [/\ #|G| = n, ω([set: G]) < k &
              n ^ (k - 2) <= C * χ([set: G]) ^ (k - 1) * trunc_log 2 n ^ (c * (k - 1))].

Definition g262_kf_ntt_claim : Prop :=
  ~ g262_kf_no_guard /\ (g262_kf_no_guard -> kk_free_chromatic_lower_bound_statement).

Theorem g262_kf_not_trivially_true : g262_kf_ntt_claim.
Proof.
split; last by move=> h k _; exact: h.
by move=> /(_ 0) [c [C [N /(_ N (leqnn N)) [G [_ ]]]]]; rewrite ltn0.
Qed.

(** ** studies:std_harris_conjecture ******************************************** *)

(** hyp_inhabited: K_2 is triangle-free and 1-degenerate; chi_f(C_5) <= 5/2; the statement at K_2. *)
Definition g262_hr_hyp_claim : Prop :=
  [/\ ω([set: 'K_2]) < 3, k_degenerate ('K_2) 1, x130_frac_chi_le (cycle_graph 5) 5 2 &
      (harris_triangle_free_degenerate_fractional_statement ->
         exists K d0 : nat, forall d : nat, d0 <= d -> k_degenerate ('K_2) d ->
           x130_frac_chi_le ('K_2) (K * d) (trunc_log 2 d))].

Theorem g262_hr_hyp_inhabited : g262_hr_hyp_claim.
Proof.
have [deg _ om] := g262_complete_degenerate 1.
split=> //; first by rewrite om.
  exact: g262_frac_chi_C5.
by move=> [K [d0 h]]; exists K, d0 => d dd kd; apply: h => //; rewrite om.
Qed.

(** not_trivially_true: without triangle-freeness, K_(d+1) with d = 2^m and m > K is d-degenerate with chi_f = d + 1
    > K d / m. *)
Definition g262_hr_no_triangle_free : Prop :=
  exists K d0 : nat,
    forall (d : nat) (G : sgraph), d0 <= d -> k_degenerate G d -> x130_frac_chi_le G (K * d) (trunc_log 2 d).

Definition g262_hr_ntt_claim : Prop :=
  ~ g262_hr_no_triangle_free /\
  (g262_hr_no_triangle_free -> harris_triangle_free_degenerate_fractional_statement).

Theorem g262_hr_not_trivially_true : g262_hr_ntt_claim.
Proof.
split; last by move=> [K [d0 h]]; exists K, d0 => d G dd _; exact: h.
move=> [K [d0 h]].
pose m := (K + d0).+1; pose d := 2 ^ m.
have [deg _ _] := g262_complete_degenerate d.
have dd : d0 <= d.
  by apply: (@leq_trans m); [rewrite /m ltnW // ltnS leq_addl | exact: ltnW (ltn_expl m (isT : 1 < 2))].
have := g262_frac_chi_K (h d ('K_d.+1) dd deg); rewrite /d trunc_expnK //.
apply/negP; rewrite -ltnNge; apply: (@leq_trans (m * 2 ^ m)).
  by rewrite ltn_mul2r expn_gt0 /= /m ltnS leq_addr.
by rewrite mulnC leq_mul2r leqnSn orbT.
Qed.

(** ** arxiv:2601.15245#02 ********************************************************** *)

(** hyp_inhabited: q = 1 and K_2 (d = 1): triangle-free, 1-degenerate, Delta = 1 so trunc_log 2 Delta = 0 <= 1; the
    statement at K_2. *)
Definition g262_md_hyp_claim : Prop :=
  [/\ 0 < 1, ω([set: 'K_2]) < 3, k_degenerate ('K_2) 1, trunc_log 2 (Delta ('K_2)) ^ 1 <= 1 ^ (1 - 1) &
      (triangle_free_degenerate_small_degree_chi_statement ->
         exists C : nat, χ([set: 'K_2]) * trunc_log 2 1 <= C * 1)].

Theorem g262_md_hyp_inhabited : g262_md_hyp_claim.
Proof.
have [deg _ om] := g262_complete_degenerate 1.
have tD : trunc_log 2 (Delta ('K_2)) = 0 by apply/eqP; rewrite trunc_log_eq0 /= (g262_Delta_K 1).
split; [by [] | by rewrite om | exact: deg | by rewrite tD |].
by move=> /(_ 1 isT) [C h]; exists C; apply: h => //; [rewrite om | rewrite tD].
Qed.

(** not_trivially_true: without triangle-freeness, q = 2 and K_(d+1) with d = 2^m, m >= 4 and m > C: Delta <= d, so
    (trunc_log 2 Delta)^2 <= m^2 <= d, and chi trunc_log 2 d = (d + 1) m > C d. *)
Definition g262_md_no_triangle_free : Prop :=
  forall q : nat, 0 < q ->
    exists C : nat,
      forall (d : nat) (G : sgraph),
        k_degenerate G d -> trunc_log 2 (Delta G) ^ q <= d ^ (q - 1) -> χ([set: G]) * trunc_log 2 d <= C * d.

Definition g262_md_ntt_claim : Prop :=
  ~ g262_md_no_triangle_free /\
  (g262_md_no_triangle_free -> triangle_free_degenerate_small_degree_chi_statement).

Theorem g262_md_not_trivially_true : g262_md_ntt_claim.
Proof.
split; last by move=> h q q0; have [C hC] := h q q0; exists C => d G _; exact: hC.
move=> /(_ 2 isT) [C h].
pose m := C + 4; pose d := 2 ^ m.
have [deg chiK _] := g262_complete_degenerate d.
have tm : trunc_log 2 d = m by rewrite /d trunc_expnK.
have hyp : trunc_log 2 (Delta ('K_d.+1)) ^ 2 <= d ^ (2 - 1).
  rewrite expn1; apply: (@leq_trans (m ^ 2)); last by rewrite /d g262_sq_le_exp2 // /m leq_addl.
  by rewrite leq_exp2r // -tm leq_trunc_log // g262_Delta_K.
have := h d ('K_d.+1) deg hyp; rewrite chiK tm.
apply/negP; rewrite -ltnNge; apply: (@leq_trans (m * d)).
  by rewrite ltn_mul2r expn_gt0 /= /m -addSnnS ltn_addr.
by rewrite mulnC leq_mul2r leqnSn orbT.
Qed.

(** ** arxiv:2601.15245#03 ********************************************************** *)

(** hyp_inhabited: r = 4 and K_3 (d = 2): K_4-free, 2-degenerate, chromatic number 3 = d + 1, on 3 vertices (the
    small complete-graph examples of the Notes); the statement at K_3. *)
Definition g262_cr_hyp_claim : Prop :=
  [/\ 3 <= 4, ω([set: 'K_3]) < 4, k_degenerate ('K_3) 2, χ([set: 'K_3]) = 3 &
      (kr_free_degenerate_critical_order_exponential_statement ->
         exists m d0 : nat, d0 <= 2 -> 2 <= m * trunc_log 2 #|'K_3|)].

Theorem g262_cr_hyp_inhabited : g262_cr_hyp_claim.
Proof.
have [deg chiK om] := g262_complete_degenerate 2.
split=> //; first by rewrite om.
by move=> /(_ 4 isT) [m [d0 h]]; exists m, d0 => dd; apply: h => //; rewrite om.
Qed.

(** not_trivially_true: without the clique bound, K_(d+1) with d + 1 = 2^j and j > m, j > d0, j >= 4 is d-degenerate
    with chi = d + 1 on 2^j vertices, and m j < 2^j - 1 = d. *)
Definition g262_cr_no_clique_bound : Prop :=
  forall r : nat, 3 <= r ->
    exists m d0 : nat,
      forall (d : nat) (G : sgraph),
        d0 <= d -> k_degenerate G d -> χ([set: G]) = d.+1 -> d <= m * trunc_log 2 #|G|.

Definition g262_cr_ntt_claim : Prop :=
  ~ g262_cr_no_clique_bound /\
  (g262_cr_no_clique_bound -> kr_free_degenerate_critical_order_exponential_statement).

Theorem g262_cr_not_trivially_true : g262_cr_ntt_claim.
Proof.
split; last by move=> h r r3; have [m [d0 hm]] := h r r3; exists m, d0 => d G dd _; exact: hm dd.
move=> /(_ 3 isT) [m [d0 h]].
pose j := m + d0 + 4; pose d := (2 ^ j).-1.
have dS : d.+1 = 2 ^ j by rewrite /d prednK // expn_gt0.
have [deg chiK _] := g262_complete_degenerate d.
have jd : j <= d by rewrite -ltnS dS ltn_expl.
have := h d ('K_d.+1) (leq_trans _ jd) deg chiK; rewrite card_ord dS trunc_expnK //.
have j4 : 4 <= j by rewrite /j leq_addl.
have d0j : d0 <= j by rewrite /j -addnA (leq_trans (leq_addr 4 d0)) // leq_addl.
move=> /(_ d0j); apply/negP; rewrite -ltnNge -ltnS dS.
apply: leq_trans (g262_sq_le_exp2 j4); apply: (@leq_trans (m.+1 * j)).
  by rewrite mulSn addnC -addn2 leq_add2l (leq_trans _ j4).
rewrite [j ^ 2]expnS expn1 leq_mul2r.
by apply/orP; right; rewrite /j -addnA -[X in X < _]addn0 ltn_add2l addn4.
Qed.

Print Assumptions kk_free_chromatic_lower_bound_statement.
Print Assumptions harris_triangle_free_degenerate_fractional_statement.
Print Assumptions triangle_free_degenerate_small_degree_chi_statement.
Print Assumptions kr_free_degenerate_critical_order_exponential_statement.
Print Assumptions g262_kf_hyp_inhabited.
Print Assumptions g262_kf_not_trivially_true.
Print Assumptions g262_hr_hyp_inhabited.
Print Assumptions g262_hr_not_trivially_true.
Print Assumptions g262_md_hyp_inhabited.
Print Assumptions g262_md_not_trivially_true.
Print Assumptions g262_cr_hyp_inhabited.
Print Assumptions g262_cr_not_trivially_true.

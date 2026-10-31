(** * Chromatic.conjectures.grounding_X272 -- grounding certificates for wave X272 (2026-10-31)

    For each of the three rows: hyp_inhabited (the hypotheses hold at a small graph, and the statement then gives its
    conclusion there) and not_trivially_true (a variant without one hypothesis is false and implies the statement);
    and, in every row, the helper_sanity groups of the five X272.v helpers.
    - arxiv:2204.12683#00: K_2 is subcubic, triangle-free, too small to contain any obstruction, with a (2:1)-fold
      colouring; without triangle-freeness the row is false at K_4 (subcubic, too small, chi_f = 4 > 19/7).
    - studies:std_kierstead_et_al_question_on_the_2_coloring_numbe: K_4 is planar with col_2 <= 4 <= 8; without
      planarity the row is false at K_9 (the last vertex of any ordering reaches the eight others, col_2 = 9).
    - studies:std_thomassen_s_conjecture_exponentially_many_3_colo: K_1 is planar and triangle-free with 3
      colourings, and the statement's constants satisfy 2^p <= 3^q; without triangle-freeness the row is false at K_4
      (no proper 3-colouring, while 2^(4 p) >= 1).
    - helper_sanity: each obstruction has its order, its degrees (cubic, or subcubic for F11) and no triangle,
      checked by vm_compute on its edge list through g272_adj; col_2(K_9) <= 9 and not <= 8. *)

From GTBase Require Import base common colourings bfold_colourings.
From Chromatic.conjectures Require Import X130 X272.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Graphs given by edge lists ****************************************************************** *)

(** Adjacency of an edge list on the naturals, the relation of [fg_mk_sgraph] read on the ordinals' values. *)
Definition g272_adj (E : seq (nat * nat)) (i j : nat) : bool := (i != j) && (((i, j) \in E) || ((j, i) \in E)).

Lemma g272_edge (n : nat) (E : seq (nat * nat)) (x y : fg_mk_sgraph (fun i j : 'I_n => (val i, val j) \in E)) :
  x -- y = g272_adj E (val x) (val y).
Proof. by []. Qed.

(** Set cardinalities over 'I_n as counts over iota 0 n (MathComp's finset and card are locked under vm_compute). *)
Lemma g272_card_set_nat (n : nat) (P : pred nat) : #|[set p : 'I_n | P (val p)]| = count P (iota 0 n).
Proof. by rewrite cardsE -sum1_card -(big_mkord P (fun _ => 1)) sum1_count /index_iota subn0. Qed.

Lemma g272_deg (n : nat) (E : seq (nat * nat)) (v : fg_mk_sgraph (fun i j : 'I_n => (val i, val j) \in E)) :
  #|N(v)| = count (g272_adj E (val v)) (iota 0 n).
Proof.
rewrite -(g272_card_set_nat n (g272_adj E (val v))).
by apply: eq_card => u; rewrite !inE.
Qed.

Lemma g272_degs (n d : nat) (E : seq (nat * nat)) :
  all (fun i => count (g272_adj E i) (iota 0 n) == d) (iota 0 n) ->
  forall v : fg_mk_sgraph (fun i j : 'I_n => (val i, val j) \in E), #|N(v)| = d.
Proof.
move/allP => h v; rewrite g272_deg; apply/eqP; apply: h.
by rewrite mem_iota /= ltn_ord.
Qed.

Lemma g272_subcubic (n : nat) (E : seq (nat * nat)) :
  all (fun i => count (g272_adj E i) (iota 0 n) <= 3) (iota 0 n) ->
  subcubic (fg_mk_sgraph (fun i j : 'I_n => (val i, val j) \in E)).
Proof.
move/allP => h v; rewrite g272_deg; apply: h.
by rewrite mem_iota /= ltn_ord.
Qed.

Lemma g272_triangle_free (n : nat) (E : seq (nat * nat)) :
  all (fun i => all (fun j => all (fun k => ~~ [&& g272_adj E i j, g272_adj E j k & g272_adj E k i])
    (iota 0 n)) (iota 0 n)) (iota 0 n) ->
  triangle_free (fg_mk_sgraph (fun i j : 'I_n => (val i, val j) \in E)).
Proof.
move/allP => h x y z; rewrite !g272_edge => xy yz zx.
have mem (w : 'I_n) : val w \in iota 0 n by rewrite mem_iota /= ltn_ord.
move: (h _ (mem x)) => /allP /(_ _ (mem y)) /allP /(_ _ (mem z)).
by rewrite xy yz zx.
Qed.

(** ** Small graphs ******************************************************************************* *)

Lemma g272_planar_small (G : sgraph) : #|G| <= 4 -> wagner_planar G.
Proof.
move=> le4; split=> m; move: (leq_trans (minor_card m) le4).
- by rewrite card_ord.
- by rewrite card_sum !card_ord.
Qed.

(** A graph cannot contain a copy of a larger graph. *)
Lemma g272_no_subgraph_small (G F : sgraph) : #|G| < #|F| -> ~ has_subgraph G F.
Proof. by move=> lt /has_subgraphP [f [inj _]]; have := leq_card f inj; rewrite leqNgt lt. Qed.

Lemma g272_triangle_free_K2 : triangle_free ('K_2).
Proof.
move=> x y z; rewrite /edge_rel /=.
by case: x => [[|[|//]] ?]; case: y => [[|[|//]] ?]; case: z => [[|[|//]] ?].
Qed.

(** An (a:b)-fold colouring of K_n uses n pairwise disjoint b-sets of 'I_a, so n b <= a (grounding_X262's
    argument). *)
Lemma g272_bfold_K_le (n a b : nat) (f : 'K_n -> {set 'I_a}) : bfold_colouring b f -> n * b <= a.
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
Lemma g272_frac_chi_K (n p q : nat) : x130_frac_chi_le ('K_n) p q -> n * q <= p.
Proof.
case=> a [b] [f] [bpos col le].
have nb : n * b <= a := g272_bfold_K_le col.
by rewrite -(leq_pmul2r bpos) mulnAC (leq_trans (leq_mul nb (leqnn q))) // mulnC (mulnC p).
Qed.

(** K_2 has a (2:1)-fold colouring: each vertex gets itself; 2 * 7 <= 19 * 1. *)
Lemma g272_frac_K2 : x130_frac_chi_le ('K_2) 19 7.
Proof.
exists 2, 1, (fun v : ('K_2) => [set (v : 'I_2)]); split=> //.
split=> [v | x y]; first by rewrite cards1.
by rewrite /edge_rel /= disjoints1 in_set1.
Qed.

(** Every graph on at most k vertices has col_2 <= k: any ordering, as L(v) misses v. *)
Lemma g272_col2_small (G : sgraph) (k : nat) : #|G| <= k -> x272_col2_le G k.
Proof.
move=> le; exists (fun v => val (enum_rank v)); split.
  by move=> x y /val_inj /enum_rank_inj.
move=> v; apply: leq_trans le.
set L := [set u : G | _].
have sub : L \subset [set~ v].
  by apply/subsetP => u; rewrite !inE => /andP [lt _]; apply: contraTneq lt => ->; rewrite ltnn.
have pos : 0 < #|G| by apply/card_gt0P; exists v.
by rewrite -(prednK pos) ltnS -(cardsC1 v) subset_leq_card.
Qed.

(** col_2(K_(n+1)) > n: the last vertex of any ordering has the n others before it, all adjacent. *)
Lemma g272_col2_K (n : nat) : ~ x272_col2_le ('K_n.+1) n.
Proof.
case=> rk [inj h].
have [v _ vmax] := @arg_maxnP ('K_n.+1) ord0 xpredT rk isT.
have := h v; apply/negP; rewrite -ltnNge ltnS.
apply: (@leq_trans #|[set~ v]|); first by rewrite cardsC1 card_ord.
apply: subset_leq_card; apply/subsetP => u; rewrite !inE => uv.
have le : rk u <= rk v := vmax u isT.
by rewrite ltn_neqAle (inj_eq inj) uv le /= /edge_rel /= uv.
Qed.

(** The proper 3-colourings of K_1 are its three maps. *)
Lemma g272_col_K1 : #|[set f : {ffun ('K_1) -> 'I_3} | proper_colouring f]| = 3.
Proof.
have -> : [set f : {ffun ('K_1) -> 'I_3} | proper_colouring f] = [set: {ffun ('K_1) -> 'I_3}].
  apply/setP => f; rewrite !inE; apply/proper_colouringP => x y.
  by rewrite (ord1 x) (ord1 y) sg_irrefl.
by rewrite cardsT card_ffun !card_ord.
Qed.

(** K_4 has no proper 3-colouring: it would be injective into three colours. *)
Lemma g272_col_K4 : #|[set f : {ffun ('K_4) -> 'I_3} | proper_colouring f]| = 0.
Proof.
apply/eqP; rewrite cards_eq0; apply/eqP/setP => f; rewrite !inE; apply/negP => /proper_colouringP h.
have inj : injective f by move=> x y; apply: contra_eq => xy; apply: h; rewrite /edge_rel /= xy.
by have := leq_card f inj; rewrite !card_ord.
Qed.

(** ** helper_sanity ****************************************************************************** *)

(** [x272_f14a]: 14 vertices, cubic, triangle-free. *)
Definition g272_f14a_helper_claim : Prop :=
  [/\ #|x272_f14a| = 14, forall v : x272_f14a, #|N(v)| = 3 & triangle_free x272_f14a].

Theorem g272_f14a_helper_sanity : g272_f14a_helper_claim.
Proof. by split; [rewrite card_ord | apply: g272_degs; vm_compute | apply: g272_triangle_free; vm_compute]. Qed.

(** [x272_f14b]: 14 vertices, cubic, triangle-free. *)
Definition g272_f14b_helper_claim : Prop :=
  [/\ #|x272_f14b| = 14, forall v : x272_f14b, #|N(v)| = 3 & triangle_free x272_f14b].

Theorem g272_f14b_helper_sanity : g272_f14b_helper_claim.
Proof. by split; [rewrite card_ord | apply: g272_degs; vm_compute | apply: g272_triangle_free; vm_compute]. Qed.

(** [x272_f11]: 11 vertices, subcubic, triangle-free. *)
Definition g272_f11_helper_claim : Prop :=
  [/\ #|x272_f11| = 11, subcubic x272_f11 & triangle_free x272_f11].

Theorem g272_f11_helper_sanity : g272_f11_helper_claim.
Proof. by split; [rewrite card_ord | apply: g272_subcubic; vm_compute | apply: g272_triangle_free; vm_compute]. Qed.

(** [x272_f22]: 22 vertices, cubic, triangle-free. *)
Definition g272_f22_helper_claim : Prop :=
  [/\ #|x272_f22| = 22, forall v : x272_f22, #|N(v)| = 3 & triangle_free x272_f22].

Theorem g272_f22_helper_sanity : g272_f22_helper_claim.
Proof. by split; [rewrite card_ord | apply: g272_degs; vm_compute | apply: g272_triangle_free; vm_compute]. Qed.

(** [x272_col2_le]: col_2(K_9) <= 9, and not <= 8. *)
Definition g272_col2_helper_claim : Prop := x272_col2_le ('K_9) 9 /\ ~ x272_col2_le ('K_9) 8.

Theorem g272_col2_helper_sanity : g272_col2_helper_claim.
Proof. by split; [apply: g272_col2_small; rewrite card_ord | exact: g272_col2_K]. Qed.

(** ** arxiv:2204.12683#00 *********************************************************************** *)

Definition g272_avoids (G : sgraph) : Prop :=
  [/\ ~ has_subgraph G x272_f14a, ~ has_subgraph G x272_f14b, ~ has_subgraph G x272_f11 &
      ~ has_subgraph G x272_f22].

Lemma g272_avoids_small (G : sgraph) : #|G| < 11 -> g272_avoids G.
Proof.
move=> lt; split; apply: g272_no_subgraph_small; rewrite card_ord //;
  by apply: leq_trans lt _.
Qed.

(** hyp_inhabited: K_2 is subcubic, triangle-free, free of the four obstructions, with chi_f <= 2 <= 19/7; the
    statement at K_2. *)
Definition g272_dlp_hyp_claim : Prop :=
  [/\ subcubic ('K_2) /\ triangle_free ('K_2), g272_avoids ('K_2), x130_frac_chi_le ('K_2) 19 7 &
      (dvorak_lidicky_postle_obstructions_fractional_nineteen_sevenths_statement -> x130_frac_chi_le ('K_2) 19 7)].

Theorem g272_dlp_hyp_inhabited : g272_dlp_hyp_claim.
Proof.
have sc : subcubic ('K_2) by exact: subcubic_Kn.
have tf := g272_triangle_free_K2.
have [a1 a2 a3 a4] : g272_avoids ('K_2) by apply: g272_avoids_small; rewrite card_ord.
by split=> //; [exact: g272_frac_K2 | move=> h; exact: h].
Qed.

(** not_trivially_true: without triangle-freeness, K_4 is subcubic and free of the obstructions, with chi_f = 4 >
    19/7. *)
Definition g272_dlp_no_triangle_free : Prop :=
  forall G : sgraph, subcubic G ->
    ~ has_subgraph G x272_f14a -> ~ has_subgraph G x272_f14b -> ~ has_subgraph G x272_f11 ->
    ~ has_subgraph G x272_f22 -> x130_frac_chi_le G 19 7.

Definition g272_dlp_ntt_claim : Prop :=
  ~ g272_dlp_no_triangle_free /\
  (g272_dlp_no_triangle_free -> dvorak_lidicky_postle_obstructions_fractional_nineteen_sevenths_statement).

Theorem g272_dlp_not_trivially_true : g272_dlp_ntt_claim.
Proof.
split; last by move=> h G sc _; exact: h.
move=> h; have [a1 a2 a3 a4] : g272_avoids ('K_4) by apply: g272_avoids_small; rewrite card_ord.
by have := g272_frac_chi_K (h _ (subcubic_Kn (leqnn 3)) a1 a2 a3 a4).
Qed.

(** ** studies:std_kierstead_et_al_question_on_the_2_coloring_numbe ******************************* *)

(** hyp_inhabited: K_4 is planar with col_2 <= 8; the statement at K_4. *)
Definition g272_col_hyp_claim : Prop :=
  [/\ wagner_planar ('K_4), x272_col2_le ('K_4) 8 &
      (planar_two_colouring_number_at_most_eight_statement -> x272_col2_le ('K_4) 8)].

Theorem g272_col_hyp_inhabited : g272_col_hyp_claim.
Proof.
have pl : wagner_planar ('K_4) by apply: g272_planar_small; rewrite card_ord.
by split=> //; [apply: g272_col2_small; rewrite card_ord | move=> h; exact: h].
Qed.

(** not_trivially_true: without planarity, K_9 has col_2 = 9 > 8. *)
Definition g272_col_no_planarity : Prop := forall G : sgraph, x272_col2_le G 8.

Definition g272_col_ntt_claim : Prop :=
  ~ g272_col_no_planarity /\ (g272_col_no_planarity -> planar_two_colouring_number_at_most_eight_statement).

Theorem g272_col_not_trivially_true : g272_col_ntt_claim.
Proof.
split; last by move=> h G _; exact: h.
by move=> h; exact: (g272_col2_K (h ('K_9))).
Qed.

(** ** studies:std_thomassen_s_conjecture_exponentially_many_3_colo ********************************* *)

(** hyp_inhabited: K_1 is planar and triangle-free with 3 proper 3-colourings; the statement's constants satisfy
    2^p <= 3^q there. *)
Definition g272_th_hyp_claim : Prop :=
  [/\ wagner_planar ('K_1), triangle_free ('K_1), #|[set f : {ffun ('K_1) -> 'I_3} | proper_colouring f]| = 3 &
      (thomassen_triangle_free_planar_exponentially_many_three_colourings_statement ->
         exists p q : nat, [/\ 0 < p, 0 < q & 2 ^ p <= 3 ^ q])].

Theorem g272_th_hyp_inhabited : g272_th_hyp_claim.
Proof.
have pl : wagner_planar ('K_1) by apply: g272_planar_small; rewrite card_ord.
have tf : triangle_free ('K_1) by move=> x y z; rewrite (ord1 x) (ord1 y) sg_irrefl.
split=> //; first exact: g272_col_K1.
move=> [p [q [p0 q0 h]]]; exists p, q; split=> //.
by have := h _ pl tf; rewrite g272_col_K1 card_ord muln1.
Qed.

(** not_trivially_true: without triangle-freeness, K_4 is planar with no proper 3-colouring. *)
Definition g272_th_no_triangle_free : Prop :=
  exists p q : nat, [/\ 0 < p, 0 < q &
    forall G : sgraph, wagner_planar G ->
      2 ^ (p * #|G|) <= #|[set f : {ffun G -> 'I_3} | proper_colouring f]| ^ q].

Definition g272_th_ntt_claim : Prop :=
  ~ g272_th_no_triangle_free /\
  (g272_th_no_triangle_free -> thomassen_triangle_free_planar_exponentially_many_three_colourings_statement).

Theorem g272_th_not_trivially_true : g272_th_ntt_claim.
Proof.
split; last by move=> [p [q [p0 q0 h]]]; exists p, q; split=> // G pl _; exact: h.
move=> [p [q [p0 q0 h]]].
have pl : wagner_planar ('K_4) by apply: g272_planar_small; rewrite card_ord.
by have := h _ pl; rewrite g272_col_K4 exp0n // leqn0 expn_eq0.
Qed.

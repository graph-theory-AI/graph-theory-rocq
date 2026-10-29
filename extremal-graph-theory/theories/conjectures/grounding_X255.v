(** * Extremal.conjectures.grounding_X255 -- grounding certificates of wave X255.

    For each of the three rows: hyp_inhabited (the hypotheses hold on a concrete instance, with a concrete value of every
    Ramsey-type or tiling hypothesis, and the statement then yields its conclusion there) and not_trivially_true in the
    contract form of meta/EXPANSION_PLAN.md 4.4 (a variant obtained from the body is false and implies the row): each row
    without its relational hypotheses (erdos:553 without both Ramsey hypotheses, as grounding_X240's erdos:544:
    a = 0, b = 1; erdos:720 without its size Ramsey hypotheses: m = 0 against M n; erdos:1015 without its tiling
    hypothesis: t = 0, f = 1 against C t).  The concrete values are R(3,3,1) = 1 and R(3,1) = 1
    (grounding_X240's g240_ramsey_K3_K1), R^(P_0) = 0 (one vertex), R^(C_2) = 1 (cycle_graph 2 is one edge) and
    f(1) = 0 (singletons).  helper_sanity: R(3,3,1) = 1, 2 is not R(3,3,1) and K_0 does not arrow (K_3, K_3, K_1);
    f(1) = 0, 1 is not f(1) and no t >= 2 has leftover 0.  g255_tiling_pos (f(t) >= 1 for t >= 2) is the fact X255.v's
    erdos:1015 Notes use for the lower half of f(t)^{1/t} -> 1. *)

From Extremal.foundations Require Import edge_colourings.
From Extremal.conjectures Require Import XE1 grounding_X240 X255.
From GTBase Require Import base common path_graphs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local vocabulary: R(3,3,n) ************************************************ *)

(** K_1 has a copy in every colour of a host with a vertex (no edge to colour). *)
Lemma g255_K1_copy (m : nat) (col : {set 'K_m.+1} -> 'I_3) (c : 'I_3) : mono_copy 'K_1 col c.
Proof.
exists (fun _ => ord0); split.
- by move=> x y _; rewrite (ord1 x) (ord1 y).
- by move=> x y; rewrite (ord1 x) (ord1 y) sg_irrefl.
- by move=> x y; rewrite (ord1 x) (ord1 y) sg_irrefl.
Qed.

Lemma g255_arrows_33n_1_1 : x255_arrows_33n 1 1.
Proof. by move=> col; apply: Or33; exact: g255_K1_copy. Qed.

(** K_0 has no copy of a graph with a vertex, in any colour. *)
Lemma g255_not_arrows_33n_1_0 : ~ x255_arrows_33n 1 0.
Proof. by move=> h; case: (h (fun _ => @Ordinal 3 0 isT)) => -[emb _]; case: (emb ord0). Qed.

Lemma g255_ramsey_33n_1 : x255_ramsey_33n 1 1.
Proof.
split; first exact: g255_arrows_33n_1_1.
by case=> // h; exfalso; exact: g255_not_arrows_33n_1_0 h.
Qed.

(** helper_sanity: R(3,3,1) = 1 (K_1 arrows, K_0 does not), and 2 is not R(3,3,1). *)
Definition g255_r33n_helper_claim : Prop :=
  [/\ x255_arrows_33n 1 1, ~ x255_arrows_33n 1 0, x255_ramsey_33n 1 1 & ~ x255_ramsey_33n 1 2].

Theorem g255_r33n_helper_sanity : g255_r33n_helper_claim.
Proof.
split; [exact: g255_arrows_33n_1_1 | exact: g255_not_arrows_33n_1_0 | exact: g255_ramsey_33n_1 |].
by case=> _ /(_ 1 g255_arrows_33n_1_1).
Qed.

(** ** Local vocabulary: the tiling leftover f(t) ******************************** *)

(** f(1) = 0: the singletons tile every K_n, each a monochromatic K_1 (no pair to colour). *)
Lemma g255_tiling_leftover_1 : x255_mono_tiling_leftover 1 0.
Proof.
exists 0 => n col _; exists [set [set x] | x : 'I_n]; split.
- move=> S /imsetP [x _ ->]; split; first exact: cards1.
  by exists true => u v; rewrite !inE => /eqP -> /eqP ->; rewrite eqxx.
- move=> S S' /imsetP [x _ ->] /imsetP [y _ ->] ne; rewrite disjoints1 inE; apply: contra ne => /eqP ->.
  by rewrite eqxx.
- rewrite addn0; apply: (@leq_trans #|[set: 'I_n]|); first by rewrite cardsT card_ord.
  by apply: subset_leq_card; apply/subsetP => x _; apply/bigcupP; exists [set x]; [apply: imset_f | rewrite inE].
Qed.

Lemma g255_tiling_1 : x255_mono_tiling_number 1 0.
Proof. by split; [exact: g255_tiling_leftover_1 | move=> r _]. Qed.

(** For t >= 2 the leftover is at least 1: n = n0 t + 1 is not a multiple of t, while a tiling covering every vertex
    is a partition of 'I_n into t-sets. *)
Lemma g255_tiling_leftover_pos (t : nat) : 2 <= t -> ~ x255_mono_tiling_leftover t 0.
Proof.
move=> t2 [n0 h].
have [P [hS hD]] := h (n0 * t).+1 (fun _ => true) (leq_trans (leq_pmulr n0 (ltnW t2)) (leqnSn _)).
rewrite addn0 => hn.
have cov : cover P = [set: 'I_(n0 * t).+1].
  apply/eqP; rewrite eqEcard subsetT /= cardsT card_ord; exact: hn.
have part : partition P [set: 'I_(n0 * t).+1].
  rewrite /partition cov eqxx /=; apply/andP; split.
  - by apply/trivIsetP => A B hA hB; exact: hD.
  - apply/negP => h0; have [c0 _] := hS _ h0; move: c0; rewrite cards0 => t0.
    by move: t2; rewrite -t0.
have := card_uniform_partition (fun A hA => proj1 (hS A hA)) part.
rewrite cardsT card_ord => e.
have : ((n0 * t).+1 %% t == 0) by rewrite e modnMl.
by rewrite -addn1 modnMDl modn_small.
Qed.

(** f(t) >= 1 for t >= 2, hence f(t)^{1/t} >= 1: the lower half of f(t)^{1/t} -> 1 holds automatically. *)
Lemma g255_tiling_pos (t f : nat) : 2 <= t -> x255_mono_tiling_number t f -> 1 <= f.
Proof.
move=> t2 [hf _]; case: f hf => // h; exfalso; exact: g255_tiling_leftover_pos t2 h.
Qed.

(** helper_sanity: f(1) = 0, 1 is not f(1), and leftover 0 fails for t = 2. *)
Definition g255_tiling_helper_claim : Prop :=
  [/\ x255_mono_tiling_leftover 1 0, ~ x255_mono_tiling_leftover 2 0, x255_mono_tiling_number 1 0 &
      ~ x255_mono_tiling_number 1 1].

Theorem g255_tiling_helper_sanity : g255_tiling_helper_claim.
Proof.
split; [exact: g255_tiling_leftover_1 | exact: g255_tiling_leftover_pos | exact: g255_tiling_1 |].
by case=> _ /(_ 0 g255_tiling_leftover_1).
Qed.

(** ** erdos:553 ************************************************************* *)

(** hyp_inhabited: concrete values R(3,3,1) = 1 and R(3,1) = 1; the statement at C = 1. *)
Definition g255_r33n_hyp_claim : Prop :=
  [/\ x255_ramsey_33n 1 1, xe1_graph_ramsey_number 'K_3 'K_1 1 &
      (multicolour_triangle_clique_ramsey_ratio_statement ->
         exists N : nat, forall n a b : nat, N <= n ->
           x255_ramsey_33n n a -> xe1_graph_ramsey_number 'K_3 'K_n b -> 1 * b <= a)].

Theorem g255_r33n_hyp_inhabited : g255_r33n_hyp_claim.
Proof. by split; [exact: g255_ramsey_33n_1 | exact: g240_ramsey_K3_K1 | move=> h; exact: h 1]. Qed.

(** not_trivially_true: without the two Ramsey hypotheses, a = 0 and b = 1 break the bound at C = 1. *)
Definition g255_r33n_no_ramsey : Prop :=
  forall C : nat, exists N : nat, forall n a b : nat, N <= n -> C * b <= a.

Definition g255_r33n_ntt_claim : Prop :=
  ~ g255_r33n_no_ramsey /\ (g255_r33n_no_ramsey -> multicolour_triangle_clique_ramsey_ratio_statement).

Theorem g255_r33n_not_trivially_true : g255_r33n_ntt_claim.
Proof.
split.
- by move=> h; have [N hN] := h 1; have := hN N 0 1 (leqnn N).
- by move=> h C; have [N hN] := h C; exists N => n a b hn _ _; exact: hN.
Qed.

(** ** erdos:720 ************************************************************* *)

(** R^(P_0) = 0: P_0 = ordinal_path 1 is one vertex; K_1 (no edge) carries a copy in either colour. *)
Lemma g255_size_ramsey_P0 : xe1_size_ramsey_number (ordinal_path 1) (ordinal_path 1) 0.
Proof.
split=> // ; exists 'K_1; split; first by rewrite /X4.x4_edge_count (proj2 edge_count_K0_K1).
move=> col _; left; exists (fun _ => ord0); split; first by move=> x y _; rewrite (ord1 x) (ord1 y).
by move=> x y; rewrite (ord1 x) (ord1 y) sg_irrefl.
Qed.

(** cycle_graph 2 is one edge (0 -- 1), so R^(C_2) = 1 with K_2 its own host. *)
Lemma g255_cycle2_edge (x y : cycle_graph 2) : x -- y = (x != y).
Proof.
by case: x => [[|[|x]] hx] //; case: y => [[|[|y]] hy] //.
Qed.

Lemma g255_size_ramsey_C2 : xe1_size_ramsey_number (cycle_graph 2) (cycle_graph 2) 1.
Proof.
have two (z : 'I_2) : z = ord0 \/ z = ord_max.
  by case: z => [[|[|m]] Hm]; [left | right | by []]; apply: val_inj.
have noedge (G : sgraph) (u v : G) : X4.x4_edge_count G = 0 -> u -- v -> False.
  move=> eG uv; move: eG; rewrite /X4.x4_edge_count /edge_count => /eqP; rewrite cards_eq0 => /eqP E0.
  by move: (in_edges u v); rewrite E0 inE uv.
split.
- exists 'K_2; split; first by rewrite /X4.x4_edge_count edge_count_Kn.
  move=> col csym.
  have colxy (x y : 'K_2) : x -- y -> col x y = col ord0 ord_max.
    by case: (two x) => ->; case: (two y) => ->; rewrite ?sg_irrefl // => _; rewrite csym.
  case c01: (col ord0 ord_max); [left | right]; exists (fun v : cycle_graph 2 => (v : 'K_2)); split=> // x y xy;
    (have e : (x : 'K_2) -- y by move: xy; rewrite g255_cycle2_edge); split=> //; by rewrite (colxy x y e) c01.
- case=> [[G [eG hG]] | //]; exfalso.
  have := hG (fun _ _ => true) (fun _ _ => erefl).
  have e01 : (ord0 : cycle_graph 2) -- ord_max by rewrite g255_cycle2_edge.
  by case=> [[f [_ hf]] | [f [_ hf]]]; have [e _] := hf ord0 ord_max e01; exact: noedge eG e.
Qed.

(** hyp_inhabited: q = 1 meets the guard, R^(P_0) = 0 and R^(C_2) = 1 are concrete size Ramsey values; the statement
    then gives its third clause at q = 1. *)
Definition g255_sr_hyp_claim : Prop :=
  [/\ 1 <= 1, xe1_size_ramsey_number (ordinal_path 1) (ordinal_path 1) 0,
      xe1_size_ramsey_number (cycle_graph 2) (cycle_graph 2) 1 &
      (path_cycle_size_ramsey_growth_statement ->
         exists N : nat, forall n m : nat, N <= n ->
           xe1_size_ramsey_number (cycle_graph n) (cycle_graph n) m -> 1 * m <= n ^ 2)].

Theorem g255_sr_hyp_inhabited : g255_sr_hyp_claim.
Proof.
split=> //; [exact: g255_size_ramsey_P0 | exact: g255_size_ramsey_C2 |].
by case=> _ _ h; exact: h 1 (leqnn 1).
Qed.

(** not_trivially_true: without the size Ramsey hypotheses, m = 0 breaks M n <= m at M = 1, n = N + 1. *)
Definition g255_sr_no_ramsey : Prop :=
  [/\ (forall M : nat, exists N : nat, forall n m : nat, N <= n -> M * n <= m),
      (forall q : nat, 1 <= q -> exists N : nat, forall n m : nat, N <= n -> q * m <= n ^ 2) &
      (forall q : nat, 1 <= q -> exists N : nat, forall n m : nat, N <= n -> q * m <= n ^ 2)].

Definition g255_sr_ntt_claim : Prop :=
  ~ g255_sr_no_ramsey /\ (g255_sr_no_ramsey -> path_cycle_size_ramsey_growth_statement).

Theorem g255_sr_not_trivially_true : g255_sr_ntt_claim.
Proof.
split.
- by case=> h _ _; have [N hN] := h 1; have := hN N.+1 0 (leqnSn N).
- case=> h1 h2 h3; split.
  + by move=> M; have [N hN] := h1 M; exists N => n m hn _; exact: hN.
  + by move=> q hq; have [N hN] := h2 q hq; exists N => n m hn _; exact: hN.
  + by move=> q hq; have [N hN] := h3 q hq; exists N => n m hn _; exact: hN.
Qed.

(** ** erdos:1015 ************************************************************ *)

(** hyp_inhabited: q = 1 meets the guard and f(1) = 0 is a concrete tiling value; the statement then gives its first
    question at q = 1 (eventually f(t) <= 2^t). *)
Definition g255_tl_hyp_claim : Prop :=
  [/\ 1 <= 1, x255_mono_tiling_number 1 0 &
      (monochromatic_clique_tiling_leftover_statement ->
         exists t0 : nat, forall t f : nat, t0 <= t -> x255_mono_tiling_number t f -> 1 ^ t * f <= (1 + 1) ^ t)].

Theorem g255_tl_hyp_inhabited : g255_tl_hyp_claim.
Proof. by split=> //; [exact: g255_tiling_1 | case=> h _; exact: h 1 (leqnn 1)]. Qed.

(** not_trivially_true: without the tiling hypothesis, t = 0 and f = 1 break f <= C t. *)
Definition g255_tl_no_tiling : Prop :=
  (forall q : nat, 1 <= q -> exists t0 : nat, forall t f : nat, t0 <= t -> q ^ t * f <= (q + 1) ^ t) /\
  (exists C : nat, forall t f : nat, f <= C * t).

Definition g255_tl_ntt_claim : Prop :=
  ~ g255_tl_no_tiling /\ (g255_tl_no_tiling -> monochromatic_clique_tiling_leftover_statement).

Theorem g255_tl_not_trivially_true : g255_tl_ntt_claim.
Proof.
split.
- by case=> _ [C hC]; have := hC 0 1; rewrite muln0.
- case=> h1 [C hC]; split; last by exists C => t f _; exact: hC.
  by move=> q hq; have [t0 ht] := h1 q hq; exists t0 => t f ht0 _; exact: ht.
Qed.

Print Assumptions g255_r33n_helper_sanity.
Print Assumptions g255_tiling_helper_sanity.
Print Assumptions g255_tiling_pos.
Print Assumptions g255_r33n_hyp_inhabited.
Print Assumptions g255_r33n_not_trivially_true.
Print Assumptions g255_sr_hyp_inhabited.
Print Assumptions g255_sr_not_trivially_true.
Print Assumptions g255_tl_hyp_inhabited.
Print Assumptions g255_tl_not_trivially_true.

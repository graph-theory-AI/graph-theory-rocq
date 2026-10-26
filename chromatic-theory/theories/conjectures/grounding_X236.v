(** * Chromatic.conjectures.grounding_X236 -- grounding certificates of wave X236.

    For each of the six rows: hyp_inhabited (the hypotheses hold on a concrete instance, and the
    statement then yields its conclusion there), not_trivially_true (meta/EXPANSION_PLAN.md 4.4: a
    variant dropping a load-bearing hypothesis is false and implies the row; for
    arxiv:2310.04265#06 a false strengthened conclusion, chi <= omega refuted by C_5, as its Notes
    explain) and helper_sanity for the row's local helpers, with positive and negative instances.
    The variant of arxiv:2506.10227#00 without sun-freeness is refuted by the iterated Mycielski
    graphs of Chromatic.applications.cochromatic_gap ([gap_graph_parameters]: clique number 4,
    chromatic number n + 7). *)

From GTBase Require Export base.
From GTBase Require Import common induced_cycles chi_bounding bfold_colourings finite_graph.
From Chromatic.conjectures Require Import X142 X236.
From Chromatic.applications.cochromatic_gap Require Import mycielski_gap cochromatic_gap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Instances *)

Lemma g236_chi_K (n : nat) : χ([set: 'K_n]) = n.
Proof.
have cl : clique [set: 'K_n] by move=> x y _ _ xy.
by rewrite (chi_clique cl) cardsT card_ord.
Qed.

Lemma g236_K2_ternary : x236_ternary 'K_2.
Proof.
move=> k k3 _ [f [inj _]].
by have := leq_card f inj; rewrite !card_ord leqNgt (leq_trans _ k3).
Qed.

Lemma g236_K3_not_ternary : ~ x236_ternary 'K_3.
Proof.
move=> h; apply: (h 3 (leqnn 3) (dvdnn 3)).
exists id; split; first exact: inj_id.
move=> i j /=.
by case: i => [[|[|[|i]]] hi] //; case: j => [[|[|[|j]]] hj].
Qed.

(** The edgeless graph on four vertices, and K_8 on 'I_2 * 'I_4 with the two parts of the first
    coordinate. *)
Definition g236_E4 : sgraph := fg_mk_sgraph (fun _ _ : 'I_4 => false).

Lemma g236_E4_cycle_union : x236_cycle_union g236_E4.
Proof.
move=> v; left; apply/eqP; rewrite cards_eq0; apply/eqP/setP => w.
by rewrite !inE /edge_rel /= /fg_srel /= andbF.
Qed.

Lemma g236_E4_parts : x236_k4_parts (fun _ : g236_E4 => (ord0 : 'I_1)).
Proof. by move=> i; rewrite (ord1 i) (_ : [set v | ord0 == ord0] = setT) ?cardsT ?card_ord //; apply/setP => v; rewrite !inE. Qed.

Lemma g236_K4_union_chi : χ([set: x236_union_k4 (fun _ : g236_E4 => (ord0 : 'I_1))]) = 4.
Proof.
have cl : clique [set: x236_union_k4 (fun _ : g236_E4 => (ord0 : 'I_1))].
  by move=> x y _ _ xy; rewrite /edge_rel /= /fg_srel xy /= eqxx orbT.
by rewrite (chi_clique cl) cardsT card_ord.
Qed.

Definition g236_K8 : sgraph := fg_mk_sgraph (fun _ _ : 'I_2 * 'I_4 => true).
Definition g236_p8 (v : g236_K8) : 'I_2 := v.1.

Lemma g236_K8_parts : x236_k4_parts g236_p8.
Proof.
move=> i; pose h (j : 'I_4) : g236_K8 := (i, j).
have e : [set v | g236_p8 v == i] = h @: setT.
  apply/setP => -[a b]; rewrite !inE /g236_p8 /=; apply/eqP/imsetP => [->|[j _ [-> _]]] //; by exists b.
by rewrite e card_imset ?cardsT ?card_ord // => j j' [].
Qed.

Lemma g236_K8_union_clique : clique [set: x236_union_k4 g236_p8].
Proof. by move=> x y _ _ xy; rewrite /edge_rel /= /fg_srel xy /= /edge_rel /= /fg_srel xy. Qed.

Lemma g236_K8_union_chi : χ([set: x236_union_k4 g236_p8]) = 8.
Proof. by rewrite (chi_clique g236_K8_union_clique) cardsT card_prod !card_ord. Qed.

Lemma g236_K3_cycle_union : x236_cycle_union 'K_3.
Proof.
move=> v; right; rewrite (_ : N(v) = [set~ v]) ?cardsC1 ?card_ord //.
by apply/setP => w; rewrite !inE eq_sym.
Qed.

Definition g236_star : sgraph := fg_mk_sgraph (fun x y : 'I_4 => (x == ord0) && (y != ord0)).

Lemma g236_star_not_cycle_union : ~ x236_cycle_union g236_star.
Proof.
move=> h; have e : N(ord0 : g236_star) = [set~ ord0].
  apply/setP => w; rewrite !inE /edge_rel /= /fg_srel /= eq_sym.
  by case: (w == ord0).
by case: (h ord0); rewrite e cardsC1 card_ord.
Qed.

Lemma g236_parts5 : ~ x236_k4_parts (fun _ : fg_mk_sgraph (fun _ _ : 'I_5 => false) => (ord0 : 'I_1)).
Proof. by move/(_ ord0); rewrite (_ : [set v | ord0 == ord0] = setT) ?cardsT ?card_ord. Qed.

(** K_n has fractional chromatic number at least n: n pairwise disjoint b-sets of 'I_a. *)
Lemma g236_Kn_frac (n : nat) : x236_frac_chi_at_least 'K_n n.
Proof.
move=> a b f b0 [hsz hdis].
have L : \sum_(v : 'K_n) #|f v| = n * b.
  rewrite (eq_bigr (fun _ => b)).
    by move=> v _; exact: hsz.
  by rewrite sum_nat_const card_ord mulnC.
rewrite -L.
have E (v : 'K_n) : #|f v| = \sum_(c : 'I_a) (c \in f v).
  by rewrite -sum1_card big_mkcond.
rewrite (eq_bigr _ (fun v _ => E v)) exchange_big /=.
have one (c : 'I_a) : \sum_(v : 'K_n) (c \in f v) <= 1.
  have e1 : \sum_v (c \in f v) = #|[set v | c \in f v]|.
    rewrite -sum1_card big_mkcond.
    rewrite [RHS]big_mkcond; apply: eq_bigr => v _; rewrite inE; by case: (c \in f v).
  rewrite e1; apply/card_le1_eqP => u v.
  rewrite !inE => cu cv; apply/eqP; apply: contraT => vu.
  have uv : u -- v by rewrite /edge_rel /= eq_sym.
  by have := disjointFr (hdis u v uv) cu; rewrite cv.
apply: (@leq_trans (\sum_(j < a) 1)).
  apply: leq_sum => j _; exact: one j.
by rewrite sum_nat_const card_ord muln1.
Qed.

Lemma g236_K2_not_frac3 : ~ x236_frac_chi_at_least 'K_2 3.
Proof.
move=> h; pose f (v : 'K_2) : {set 'I_2} := [set v].
have bf : bfold_colouring 1 f.
  split=> [v|x y xy]; first by rewrite cards1.
  rewrite /f disjoints1 inE; move: xy; by rewrite /edge_rel /= eq_sym.
by have := h 2 1 f isT bf.
Qed.

(** A subgraph of K_1 has at most one vertex, hence a 1:1 colouring. *)
Lemma g236_sub_K1_not_frac2 (H : sgraph) : has_subgraph 'K_1 H -> ~ x236_frac_chi_at_least H 2.
Proof.
move=> /has_subgraphP [g [inj _]] h.
pose f (v : H) : {set 'I_1} := [set ord0].
have bf : bfold_colouring 1 f.
  split=> [v|x y xy]; first by rewrite cards1.
  exfalso; move: (sg_edgeNeq xy); rewrite (inj x y) ?eqxx //.
  by rewrite (ord1 (g x)) (ord1 (g y)).
by have := h 1 1 f isT bf.
Qed.

(** K_2 has no neighbour sum distinguishing colouring: both ends see the same single edge. *)
Lemma g236_K2_no_nsd (k : nat) : ~ x142_neighbour_sum_edge_colourable 'K_2 k.
Proof.
case=> col [_ hd].
pose v0 : 'K_2 := ord0; pose v1 : 'K_2 := Ordinal (isT : 1 < 2).
have e : x142_edges_incident v0 = x142_edges_incident v1.
  apply/setP => e; rewrite !inE; apply/andP/andP => -[eE _]; split => //;
  case/edgesP: eE => x [y] [-> xy]; rewrite !inE;
  by case: x xy => [[|[|x]] hx] //; case: y => [[|[|y]] hy].
have := hd v0 v1 isT; by rewrite /x142_incident_sum e eqxx.
Qed.

(** The ordered path P_3 on 'I_3. *)
Definition g236_P3 : rel 'I_3 := fun i j => j == i.+1 :> nat.
Definition g236_P3s : sgraph := fg_mk_sgraph g236_P3.

Lemma g236_P3_no_isolated_edge : x236_no_isolated_edge g236_P3s.
Proof.
have n1 : #|N(Ordinal (isT : 1 < 3) : g236_P3s)| = 2.
  rewrite (_ : N(Ordinal (isT : 1 < 3) : g236_P3s) = [set ord0; Ordinal (isT : 2 < 3)]) ?cards2 //.
  apply/setP => j; rewrite !inE /edge_rel /= /fg_srel /g236_P3; by case: j => [[|[|[|j]]] hj].
move=> x y; rewrite /edge_rel /= /fg_srel /g236_P3.
case: x => [[|[|[|x]]] hx] //; case: y => [[|[|[|y]]] hy] //= _; [right | left | left | right];
  rewrite (_ : Ordinal _ = Ordinal (isT : 1 < 3)) ?n1 //; exact: val_inj.
Qed.

Lemma g236_K2_isolated_edge : ~ x236_no_isolated_edge 'K_2.
Proof.
move/(_ ord0 (Ordinal (isT : 1 < 2)) isT).
have n1 (v : 'K_2) : #|N(v)| = 1.
  by rewrite (_ : N(v) = [set~ v]) ?cardsC1 ?card_ord //; apply/setP => w; rewrite !inE eq_sym.
by rewrite !n1; case.
Qed.

(** Ordered graphs: six isolated vertices, one edge, the edgeless 'I_3 and C_5. *)
Definition g236_M6 : rel 'I_6 := fun _ _ => false.

Lemma g236_M6_deg : x236_max_degree_one g236_M6.
Proof. by move=> i; rewrite (_ : [set j | fg_srel g236_M6 i j] = set0) ?cards0 //; apply/setP => j; rewrite !inE /fg_srel /g236_M6 andbF. Qed.

Lemma g236_M6_not_in_C5 : ~ x236_ord_contains g236_M6 (ord_cycle_rel 5).
Proof.
case=> phi [inc _].
have inj : injective phi.
  move=> i j e; apply/eqP; case: (ltngtP i j) => [ij|ji|/val_inj ->] //.
  - by move: (inc _ _ ij); rewrite e ltnn.
  - by move: (inc _ _ ji); rewrite e ltnn.
by have := leq_card phi inj; rewrite !card_ord.
Qed.

Definition g236_M2 : rel 'I_2 := fun _ _ => true.

Lemma g236_M2_deg : x236_max_degree_one g236_M2.
Proof.
move=> i; rewrite (_ : [set j | fg_srel g236_M2 i j] = [set~ i]) ?cardsC1 ?card_ord //.
by apply/setP => j; rewrite !inE /fg_srel /g236_M2 eq_sym andbT.
Qed.

Lemma g236_M2_in_K2 : x236_ord_contains g236_M2 g236_M2.
Proof. by exists id. Qed.

Lemma g236_M2_not_in_E3 : ~ x236_ord_contains g236_M2 (fun _ _ : 'I_3 => false).
Proof.
case=> phi [inc e]; have := e ord0 (Ordinal (isT : 1 < 2)).
by rewrite /fg_srel /g236_M2 /= andbF.
Qed.

Lemma g236_P3_not_deg : ~ x236_max_degree_one g236_P3.
Proof.
move/(_ (Ordinal (isT : 1 < 3))).
rewrite (_ : [set j | fg_srel g236_P3 (Ordinal (isT : 1 < 3)) j] = [set ord0; Ordinal (isT : 2 < 3)]).
  apply/setP => j; rewrite !inE /fg_srel /g236_P3; by case: j => [[|[|[|j]]] hj].
by rewrite cards2.
Qed.

Definition g236_C5 : sgraph := fg_mk_sgraph (ord_cycle_rel 5).

Lemma g236_three (C : finType) (a b c : C) : a != b -> b != c -> c != a -> 3 <= #|C|.
Proof. by move=> ab bc ca; apply/card_gt2P; exists a, b, c. Qed.

Lemma g236_C5_chi : 3 <= χ([set: g236_C5]).
Proof.
apply: chi_lower_from_palettes => C f hf.
pose v (i : nat) (h : i < 5) : g236_C5 := Ordinal h.
have e01 := hf (v 0 isT) (v 1 isT) isT; have e12 := hf (v 1 isT) (v 2 isT) isT.
have e23 := hf (v 2 isT) (v 3 isT) isT; have e34 := hf (v 3 isT) (v 4 isT) isT.
have e40 := hf (v 4 isT) (v 0 isT) isT.
case: (eqVneq (f (v 2 isT)) (f (v 0 isT))) => [e20|n20]; last first.
  exact: g236_three e01 e12 n20.
case: (eqVneq (f (v 3 isT)) (f (v 1 isT))) => [e31|n31]; last first.
  apply: (@g236_three _ (f (v 0 isT)) (f (v 1 isT)) (f (v 3 isT))) => //.
    by rewrite eq_sym.
  by rewrite -e20 eq_sym.
apply: (@g236_three _ (f (v 0 isT)) (f (v 1 isT)) (f (v 4 isT))) => //.
by rewrite -e31.
Qed.

Lemma g236_C5_omega : ω([set: g236_C5]) <= 2.
Proof.
apply: omega_from_cliques => K hK; rewrite leqNgt; apply/negP => /card_gt2P [x [y [z [[xK yK zK] [xy yz zx]]]]].
have := hK x y xK yK xy; have := hK y z yK zK yz; have := hK z x zK xK zx.
rewrite /edge_rel /= /fg_srel xy yz zx /=.
by case: x {xK xy zx} => [[|[|[|[|[|x]]]]] hx] //; case: y {yK yz} => [[|[|[|[|[|y]]]]] hy] //;
  case: z {zK} => [[|[|[|[|[|z]]]]] hz].
Qed.

(** Suns: K_3 is sun-free (a t-sun has 2t >= 8 vertices); adjacency in the 4-sun. *)
Lemma g236_K3_sun_free (t : nat) : 4 <= t -> induced_free 'K_3 (x236_sun t).
Proof.
move=> t4 S [i] _ _; have le := leq_card _ (can_inj (bij.bijK' i)).
have h3 : #|induced S| <= 3 by rewrite card_sig (leq_trans (max_card _)) // card_ord.
have := leq_trans le h3; rewrite card_prod card_ord card_bool => h.
have h8 : 8 <= t * 2 by rewrite (@leq_mul2r 2 4 t) t4 orbT.
by have := leq_trans h8 h.
Qed.

Definition g236_s4 (i : nat) (h : i < 4) (b : bool) : x236_sun 4 := (Ordinal h, b).

(** ** Row arxiv:1810.00065#00 *)

Definition g236_ternary_hyp_claim : Prop :=
  x236_ternary 'K_2 /\ (ternary_three_colourable_statement -> χ([set: 'K_2]) <= 3).

Theorem g236_ternary_hyp_inhabited : g236_ternary_hyp_claim.
Proof. by split; [exact: g236_K2_ternary | move=> h; exact: h _ g236_K2_ternary]. Qed.

(** Without [x236_ternary] the conclusion fails at K_4 (chi 4). *)
Definition g236_all_three_colourable : Prop := forall G : sgraph, χ([set: G]) <= 3.

Definition g236_ternary_ntt_claim : Prop :=
  ~ g236_all_three_colourable /\ (g236_all_three_colourable -> ternary_three_colourable_statement).

Theorem g236_ternary_not_trivially_true : g236_ternary_ntt_claim.
Proof.
split; last by move=> h G _; exact: h G.
by move=> h; have := h 'K_4; rewrite g236_chi_K.
Qed.

Definition g236_ternary_helper_claim : Prop := x236_ternary 'K_2 /\ ~ x236_ternary 'K_3.

Theorem g236_ternary_helper_sanity : g236_ternary_helper_claim.
Proof. by split; [exact: g236_K2_ternary | exact: g236_K3_not_ternary]. Qed.

(** ** Row arxiv:2511.02892#02 *)

Definition g236_k4_hyp_claim : Prop :=
  [/\ x236_cycle_union g236_E4, x236_k4_parts (fun _ : g236_E4 => (ord0 : 'I_1)) &
      (cycles_plus_k4s_four_colourable_statement ->
         χ([set: x236_union_k4 (fun _ : g236_E4 => (ord0 : 'I_1))]) <= 4)].

Theorem g236_k4_hyp_inhabited : g236_k4_hyp_claim.
Proof.
split; [exact: g236_E4_cycle_union | exact: g236_E4_parts |].
by move=> h; exact: h _ _ _ g236_E4_cycle_union g236_E4_parts.
Qed.

(** Without [x236_cycle_union] the conclusion fails: G complete on two parts gives K_8. *)
Definition g236_k4_any_graph : Prop :=
  forall (G : sgraph) (n : nat) (p : G -> 'I_n), x236_k4_parts p -> χ([set: x236_union_k4 p]) <= 4.

Definition g236_k4_ntt_claim : Prop :=
  ~ g236_k4_any_graph /\ (g236_k4_any_graph -> cycles_plus_k4s_four_colourable_statement).

Theorem g236_k4_not_trivially_true : g236_k4_ntt_claim.
Proof.
split; last by move=> h G n p _ hp; exact: h G n p hp.
by move=> h; have := h _ _ _ g236_K8_parts; rewrite g236_K8_union_chi.
Qed.

Definition g236_k4_helper_claim : Prop :=
  [/\ (x236_cycle_union g236_E4 /\ x236_cycle_union 'K_3), ~ x236_cycle_union g236_star,
      (x236_k4_parts g236_p8 /\ ~ x236_k4_parts (fun _ : fg_mk_sgraph (fun _ _ : 'I_5 => false) => (ord0 : 'I_1)))
    & (χ([set: x236_union_k4 (fun _ : g236_E4 => (ord0 : 'I_1))]) = 4 /\ χ([set: x236_union_k4 g236_p8]) = 8)].

Theorem g236_k4_helper_sanity : g236_k4_helper_claim.
Proof.
split; [split; [exact: g236_E4_cycle_union | exact: g236_K3_cycle_union] | exact: g236_star_not_cycle_union
       | split; [exact: g236_K8_parts | exact: g236_parts5] | split; [exact: g236_K4_union_chi | exact: g236_K8_union_chi]].
Qed.

(** ** Row arxiv:1808.01605#00 *)

Definition g236_frac_hyp_claim : Prop :=
  [/\ 1 <= 1, 3 <= 3 &
      (fractional_girth_subgraph_statement ->
         exists k : nat, 0 < k /\
           exists H : sgraph, [/\ has_subgraph 'K_k H, girth_geq H 3 & x236_frac_chi_at_least H 1])].

Theorem g236_frac_hyp_inhabited : g236_frac_hyp_claim.
Proof.
split=> // h; have [k [k0 hk]] := h 1 3 isT isT.
by exists k; split=> //; apply: hk; exact: g236_Kn_frac.
Qed.

(** Without the hypothesis chi_f(G) >= k the conclusion fails at x = 2 and G = K_1. *)
Definition g236_frac_any_graph : Prop :=
  forall x g : nat, 1 <= x -> 3 <= g ->
    exists k : nat, 0 < k /\
      forall G : sgraph,
        exists H : sgraph, [/\ has_subgraph G H, girth_geq H g & x236_frac_chi_at_least H x].

Definition g236_frac_ntt_claim : Prop :=
  ~ g236_frac_any_graph /\ (g236_frac_any_graph -> fractional_girth_subgraph_statement).

Theorem g236_frac_not_trivially_true : g236_frac_ntt_claim.
Proof.
split.
- move=> h; have [k [_ hk]] := h 2 3 isT isT.
  have [H [sub _ fr]] := hk 'K_1.
  exact: g236_sub_K1_not_frac2 sub fr.
- move=> h x g x1 g3; have [k [k0 hk]] := h x g x1 g3.
  by exists k; split=> // G _; exact: hk G.
Qed.

Definition g236_frac_helper_claim : Prop :=
  [/\ forall n : nat, x236_frac_chi_at_least 'K_n n, x236_frac_chi_at_least 'K_2 2
    & ~ x236_frac_chi_at_least 'K_2 3].

Theorem g236_frac_helper_sanity : g236_frac_helper_claim.
Proof. by split; [exact: g236_Kn_frac | exact: g236_Kn_frac | exact: g236_K2_not_frac3]. Qed.

(** ** Row arxiv:1804.06104#00 *)

Definition g236_nsd_hyp_claim : Prop :=
  x236_no_isolated_edge g236_P3s /\
  (nsd_delta_plus_constant_statement ->
     exists C : nat, x142_neighbour_sum_edge_colourable g236_P3s (Delta g236_P3s + C)).

Theorem g236_nsd_hyp_inhabited : g236_nsd_hyp_claim.
Proof.
split; first exact: g236_P3_no_isolated_edge.
by case=> C hC; exists C; exact: hC _ g236_P3_no_isolated_edge.
Qed.

(** Without [x236_no_isolated_edge] the conclusion fails at K_2. *)
Definition g236_nsd_any_graph : Prop :=
  exists C : nat, forall G : sgraph, x142_neighbour_sum_edge_colourable G (Delta G + C).

Definition g236_nsd_ntt_claim : Prop :=
  ~ g236_nsd_any_graph /\ (g236_nsd_any_graph -> nsd_delta_plus_constant_statement).

Theorem g236_nsd_not_trivially_true : g236_nsd_ntt_claim.
Proof.
split.
- by case=> C hC; exact: g236_K2_no_nsd (hC 'K_2).
- by case=> C hC; exists C => G _; exact: hC G.
Qed.

Definition g236_nsd_helper_claim : Prop :=
  x236_no_isolated_edge g236_P3s /\ ~ x236_no_isolated_edge 'K_2.

Theorem g236_nsd_helper_sanity : g236_nsd_helper_claim.
Proof. by split; [exact: g236_P3_no_isolated_edge | exact: g236_K2_isolated_edge]. Qed.

(** ** Row arxiv:2310.04265#06 *)

Definition g236_ord_hyp_claim : Prop :=
  x236_max_degree_one g236_M2 /\
  (ordered_matching_free_chi_bounded_statement ->
     chi_bounded_via (fun x : {n : nat & rel 'I_n} => fg_mk_sgraph (projT2 x))
                     (fun x => ~ x236_ord_contains g236_M2 (projT2 x))).

Theorem g236_ord_hyp_inhabited : g236_ord_hyp_claim.
Proof. by split; [exact: g236_M2_deg | move=> h; exact: h _ _ g236_M2_deg]. Qed.

(** The strengthened conclusion chi <= omega is false (M = six isolated vertices, the ordered C_5)
    and implies the row. *)
Definition g236_ord_chi_le_omega : Prop :=
  forall (m : nat) (M : rel 'I_m), x236_max_degree_one M ->
    forall x : {n : nat & rel 'I_n}, ~ x236_ord_contains M (projT2 x) ->
      χ([set: fg_mk_sgraph (projT2 x)]) <= ω([set: fg_mk_sgraph (projT2 x)]).

Definition g236_ord_ntt_claim : Prop :=
  ~ g236_ord_chi_le_omega /\ (g236_ord_chi_le_omega -> ordered_matching_free_chi_bounded_statement).

Theorem g236_ord_not_trivially_true : g236_ord_ntt_claim.
Proof.
split.
- move=> h; have := h 6 g236_M6 g236_M6_deg (existT _ 5 (ord_cycle_rel 5)) g236_M6_not_in_C5.
  have c3 := g236_C5_chi; have o2 := g236_C5_omega.
  move=> le; have := leq_trans c3 (leq_trans le o2); by [].
- by move=> h m M hM; exists id => x hx; exact: h hM x hx.
Qed.

Definition g236_ord_helper_claim : Prop :=
  [/\ x236_max_degree_one g236_M2, ~ x236_max_degree_one g236_P3,
      x236_ord_contains g236_M2 g236_M2 & ~ x236_ord_contains g236_M2 (fun _ _ : 'I_3 => false)].

Theorem g236_ord_helper_sanity : g236_ord_helper_claim.
Proof. by split; [exact: g236_M2_deg | exact: g236_P3_not_deg | exact: g236_M2_in_K2 | exact: g236_M2_not_in_E3]. Qed.

(** ** Row arxiv:2506.10227#00 *)

Definition g236_sun_hyp_claim : Prop :=
  (forall t : nat, 4 <= t -> induced_free 'K_3 (x236_sun t)) /\
  (sun_free_chi_bounded_statement -> exists f : nat -> nat, χ([set: 'K_3]) <= f ω([set: 'K_3])).

Theorem g236_sun_hyp_inhabited : g236_sun_hyp_claim.
Proof.
split; first exact: g236_K3_sun_free.
by case=> f hf; exists f; exact: hf _ g236_K3_sun_free.
Qed.

(** Without sun-freeness the class of all graphs would be chi-bounded, which the iterated Mycielski
    graphs refute (clique number 4, chromatic number n + 7). *)
Lemma g236_all_not_chi_bounded : ~ chi_bounded_class (fun _ : sgraph => True).
Proof.
case=> f hf; have [ho [_ hc]] := gap_graph_parameters (f 4).
have := hf (gap_graph (f 4)) I; rewrite ho hc.
by rewrite -{2}(addn0 (f 4)) leq_add2l.
Qed.

Definition g236_sun_ntt_claim : Prop :=
  ~ chi_bounded_class (fun _ : sgraph => True) /\
  (chi_bounded_class (fun _ : sgraph => True) -> sun_free_chi_bounded_statement).

Theorem g236_sun_not_trivially_true : g236_sun_ntt_claim.
Proof. by split; [exact: g236_all_not_chi_bounded | apply: chi_bounded_class_sub]. Qed.

Definition g236_sun_helper_claim : Prop :=
  [/\ forall t : nat, 4 <= t -> induced_free 'K_3 (x236_sun t),
      g236_s4 (isT : 0 < 4) true -- g236_s4 (isT : 0 < 4) false,
      ~~ (g236_s4 (isT : 0 < 4) true -- g236_s4 (isT : 1 < 4) false),
      g236_s4 (isT : 0 < 4) false -- g236_s4 (isT : 3 < 4) false
    & ~~ (g236_s4 (isT : 0 < 4) false -- g236_s4 (isT : 2 < 4) false)].

Theorem g236_sun_helper_sanity : g236_sun_helper_claim.
Proof. by split; [exact: g236_K3_sun_free | | | |]. Qed.

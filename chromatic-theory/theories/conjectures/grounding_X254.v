(** * Chromatic.conjectures.grounding_X254 -- grounding certificates of wave X254.

    For each of the eight rows: hyp_inhabited (the hypotheses hold on a concrete instance, and the statement then
    yields its conclusion there) and not_trivially_true in the contract form of meta/EXPANSION_PLAN.md 4.4 (a variant
    obtained from the body is false and implies the row); helper_sanity for the two local helpers, listed in every row.
    - Scott: the class predicate weakened to all graphs, not chi-bounded ([g236_all_not_chi_bounded]: the iterated
      Mycielski graphs of Chromatic.applications.cochromatic_gap, clique number 4 and chromatic number n + 7).
    - Gyarfas: without the odd-hole hypothesis, at k = 4, the same graphs.
    - Trotignon and Vuskovic: without the ISK4 hypothesis, the Grotzsch graph (the Mycielski graph of C_5,
      [g236_C5]) is triangle-free with chromatic number 4.
    - Tomescu (the canonical row and its three synonyms): without the guard 4 <= k, at k = 2 and G = K_2 the count
      2 = 2!(2-1)^0 is attained while the 2-core of K_2 is empty.
    - odd multiholes: the class predicate weakened to all graphs, not polynomially chi-bounded (the same graphs at
      n = c * 4^d).
    The hypotheses are met by K_1 (no induced subdivision of K_2 or K_4, no hole, no multihole, triangle-free) and,
    for Tomescu, by K_4 (connected, chromatic number 4).  Helper sanity: the 2-core of K_4 is all of K_4 and that of
    K_2 is empty; C_5 is an odd 1-multihole and K_1 has none. *)

From GTBase Require Export base.
From Chromatic.foundations Require Import chi_bounding.
From GTBase Require Import induced_cycles induced_subdivisions chi_bounding colourings.
From Chromatic.conjectures Require Import grounding_X236 X254.
From Chromatic.applications.cochromatic_gap Require Import mycielski_gap cochromatic_gap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Shared lemmas ************************************************************ *)

Lemma g254_isd_card (H G : sgraph) : induced_subdivision H G -> #|H| <= #|G|.
Proof. case=> m; apply: (@leq_card H G (isd_branch m)); exact: isd_branch_injective. Qed.

Lemma g254_K1_no_isd (H : sgraph) : 1 < #|H| -> ~ induced_subdivision H 'K_1.
Proof. by move=> hH /g254_isd_card; rewrite card_ord => h; have := leq_trans hH h. Qed.

Lemma g254_no_hole_small (G : sgraph) (c : seq G) : #|G| <= 3 -> ~ hole c.
Proof.
move=> hG [/ucycle_uniq u [sz _]].
have := max_card (mem c); rewrite (card_uniqP u) => hc.
by have := leq_ltn_trans (leq_trans hc hG) sz; rewrite ltnn.
Qed.

Lemma g254_no_multihole_small (G : sgraph) (k : nat) : 1 <= k -> #|G| <= 3 -> ~ x254_odd_multihole G k.
Proof.
case: k => // k _ hG [c [hc _]].
by have [h _] := hc ord0; exact: g254_no_hole_small hG h.
Qed.

Lemma g254_K1_omega : ω([set: 'K_1]) <= 1.
Proof. by apply: omega_from_cliques => K _; have := max_card (mem K); rewrite card_ord. Qed.

Lemma g254_K1_triangle_free : triangle_free 'K_1.
Proof. by move=> x y z; rewrite (ord1 x) (ord1 y) sg_irrefl. Qed.

Lemma g254_connected_K4 : connected [set: 'K_4].
Proof.
move=> x y _ _; case: (eqVneq x y) => [->|xy]; first exact: connect0.
by apply: connect1; rewrite /= !inE /=.
Qed.

Lemma g254_K2_colourings : #|[set f : {ffun 'K_2 -> 'I_2} | proper_colouring f]| = 2.
Proof.
have -> : [set f : {ffun 'K_2 -> 'I_2} | proper_colouring f] = [set f : {ffun 'K_2 -> 'I_2} | injectiveb f].
  apply/setP => f; rewrite !inE; apply/proper_colouringP/injectiveP.
    move=> h x y e; apply/eqP; apply/negPn/negP => xy; have := h x y xy; by rewrite e eqxx.
  move=> h x y xy; apply/eqP => /h e; move: xy; by rewrite e sg_irrefl.
by rewrite card_inj_ffuns !card_ord.
Qed.

(** gap graphs: clique number 4, chromatic number n + 7 *)
Lemma g254_gap_unbounded (c : nat) : ~ (forall G : sgraph, ω([set: G]) <= 4 -> χ([set: G]) <= c).
Proof.
move=> h; have [ho [_ hc]] := gap_graph_parameters c.
have := h (gap_graph c); rewrite ho hc => /(_ (leqnn 4)).
by rewrite -{2}[c]addn0 leq_add2l.
Qed.

(** the Grotzsch graph: the Mycielski graph of C_5, triangle-free with chromatic number 4 *)
Lemma g254_C5_cert : chromatic_certificate g236_C5 3.
Proof.
exists 'I_3, (fun v : g236_C5 => inord (if val v == 4 then 2 else val v %% 2) : 'I_3); split; first by rewrite card_ord.
split.
  move=> [[|[|[|[|[|x]]]]] hx] // [[|[|[|[|[|y]]]]] hy] // _; by apply/eqP => /(congr1 val); rewrite /= !inordK.
move=> D g hg; exact: leq_trans g236_C5_chi (proper_chi_bound hg).
Qed.

Definition g254_grotzsch : sgraph := mycielski g236_C5.

Lemma g254_grotzsch_chi : χ([set: g254_grotzsch]) = 4.
Proof. apply: chromatic_certificate_exact; apply: mycielski_chromatic_certificate g254_C5_cert _; by rewrite card_ord. Qed.

Lemma g254_C5_cliques (K : {set g236_C5}) : clique K -> #|K| <= 2.
Proof. move=> hK; apply: leq_trans g236_C5_omega; apply: clique_bound; rewrite inE subsetT /=; exact/cliqueP. Qed.

Lemma g254_grotzsch_triangle_free : triangle_free g254_grotzsch.
Proof.
move=> x y z xy yz zx.
have hK : clique [set x; y; z].
  move=> a b; rewrite !inE.
  by move=> /orP[/orP[|]|] /eqP-> /orP[/orP[|]|] /eqP->; rewrite ?eqxx // => _; rewrite // sgP.
have := mycielski_cliques_bounded (isT : 1 < 2) _ g254_C5_cliques hK.
rewrite card_ord => /(_ isT); apply/negP; rewrite -ltnNge; apply/card_gt2P; exists x, y, z.
rewrite !inE !eqxx ?orbT; split=> //.
by rewrite (sg_edgeNeq xy) (sg_edgeNeq yz) (sg_edgeNeq zx).
Qed.

(** ** helper_sanity *)

Definition g254_two_core_helper_claim : Prop :=
  x254_two_core 'K_4 = [set: 'K_4] /\ x254_two_core 'K_2 = set0.

Theorem g254_two_core_helper_sanity : g254_two_core_helper_claim.
Proof.
split.
- apply/eqP; rewrite eqEsubset subsetT /=; apply: (bigcup_max [set: 'K_4]) => //.
  apply/forall_inP => v _; rewrite setIT.
  have -> : N(v) = [set~ v] by apply/setP => w; rewrite !inE eq_sym.
  by rewrite cardsC1 card_ord.
- apply/eqP; rewrite -subset0; apply/bigcupsP => S /forall_inP hS; apply/subsetP => v vS.
  have := hS v vS; have -> : N(v) = [set~ v] by apply/setP => w; rewrite !inE eq_sym.
  have := subsetIl [set~ v] S; move/subset_leq_card; rewrite cardsC1 card_ord => h1 h2.
  by have := leq_trans h2 h1.
Qed.

Definition g254_C5_hole : seq g236_C5 :=
  [:: Ordinal (isT : 0 < 5); Ordinal (isT : 1 < 5); Ordinal (isT : 2 < 5); Ordinal (isT : 3 < 5);
      Ordinal (isT : 4 < 5)].

Definition g254_multihole_helper_claim : Prop :=
  x254_odd_multihole g236_C5 1 /\ ~ x254_odd_multihole 'K_1 1.

Theorem g254_multihole_helper_sanity : g254_multihole_helper_claim.
Proof.
split; last by apply: g254_no_multihole_small => //; rewrite card_ord.
exists (fun _ => g254_C5_hole); split.
- by move=> _; split; [apply/holeP; vm_compute | ].
- by move=> i j x y; rewrite (ord1 i) (ord1 j) eqxx.
Qed.

(** ** studies:std_scott_s_conjecture_induced_subdivisions_and_chi *)

Definition g254_scott_hyp_claim : Prop :=
  ~ induced_subdivision 'K_2 'K_1 /\
  (scott_induced_subdivision_chi_bounded_statement ->
     chi_bounded_class (fun G : sgraph => ~ induced_subdivision 'K_2 G)).

Theorem g254_scott_hyp_inhabited : g254_scott_hyp_claim.
Proof. by split; [apply: g254_K1_no_isd; rewrite card_ord | move=> h; exact: h]. Qed.

Definition g254_scott_all_graphs : Prop :=
  forall H : sgraph, chi_bounded_class (fun G : sgraph => True).

Definition g254_scott_ntt_claim : Prop :=
  ~ g254_scott_all_graphs /\ (g254_scott_all_graphs -> scott_induced_subdivision_chi_bounded_statement).

Theorem g254_scott_not_trivially_true : g254_scott_ntt_claim.
Proof.
split; first by move=> h; exact: g236_all_not_chi_bounded (h 'K_1).
by move=> h H; apply: chi_bounded_class_sub (h H).
Qed.

(** ** studies:std_gy_rf_s_odd_hole_boundedness_conjecture *)

Definition g254_gy_hyp_claim : Prop :=
  [/\ 0 < 1, ω([set: 'K_1]) <= 1, (forall c : seq ('K_1), hole c -> odd (size c) -> size c <= 1) &
      (gyarfas_long_odd_hole_chi_bounded_statement -> exists N : nat, χ([set: 'K_1]) <= N)].

Theorem g254_gy_hyp_inhabited : g254_gy_hyp_claim.
Proof.
split=> //; first exact: g254_K1_omega.
  by move=> c /(g254_no_hole_small (G := 'K_1)); rewrite card_ord => /(_ isT).
move=> h; have [N hN] := h 1 1 isT isT; exists N; apply: hN; first exact: g254_K1_omega.
by move=> c /(g254_no_hole_small (G := 'K_1)); rewrite card_ord => /(_ isT).
Qed.

Definition g254_gy_no_hole_clause : Prop :=
  forall k l : nat, 0 < k -> 0 < l -> exists N : nat,
    forall G : sgraph, ω([set: G]) <= k -> χ([set: G]) <= N.

Definition g254_gy_ntt_claim : Prop :=
  ~ g254_gy_no_hole_clause /\ (g254_gy_no_hole_clause -> gyarfas_long_odd_hole_chi_bounded_statement).

Theorem g254_gy_not_trivially_true : g254_gy_ntt_claim.
Proof.
split; first by move=> h; have [N hN] := h 4 1 isT isT; exact: g254_gap_unbounded hN.
by move=> h k l k0 l0; have [N hN] := h k l k0 l0; exists N => G hk _; exact: hN.
Qed.

(** ** studies:std_trotignon_vu_kovi_conjecture_isk4_triangle_free *)

Definition g254_tv_hyp_claim : Prop :=
  [/\ ~ induced_subdivision 'K_4 ('K_1), triangle_free ('K_1) &
      (isk4_triangle_free_three_colourable_statement -> χ([set: 'K_1]) <= 3)].

Theorem g254_tv_hyp_inhabited : g254_tv_hyp_claim.
Proof.
have h1 : ~ induced_subdivision 'K_4 'K_1 by apply: g254_K1_no_isd; rewrite card_ord.
split=> //; first exact: g254_K1_triangle_free.
move=> h; exact: h _ h1 g254_K1_triangle_free.
Qed.

Definition g254_tv_no_isk4_clause : Prop :=
  forall G : sgraph, triangle_free G -> χ([set: G]) <= 3.

Definition g254_tv_ntt_claim : Prop :=
  ~ g254_tv_no_isk4_clause /\ (g254_tv_no_isk4_clause -> isk4_triangle_free_three_colourable_statement).

Theorem g254_tv_not_trivially_true : g254_tv_ntt_claim.
Proof.
split; first by move=> h; have := h _ g254_grotzsch_triangle_free; rewrite g254_grotzsch_chi.
by move=> h G _; exact: h.
Qed.

(** ** studies:std_tomescu_s_conjecture_maximum_number_of_proper_k_529 and its three synonyms *)

Definition g254_tom_hyp_claim : Prop :=
  [/\ 4 <= 4, connected [set: 'K_4], χ([set: 'K_4]) = 4 &
      (tomescu_connected_colouring_count_statement ->
         #|[set f : {ffun 'K_4 -> 'I_4} | proper_colouring f]| <= 4`! * (4 - 1) ^ (#|'K_4| - 4) /\
         (#|[set f : {ffun 'K_4 -> 'I_4} | proper_colouring f]| = 4`! * (4 - 1) ^ (#|'K_4| - 4) <->
            clique (x254_two_core 'K_4) /\ #|x254_two_core 'K_4| = 4))].

Theorem g254_tom_hyp_inhabited : g254_tom_hyp_claim.
Proof.
have hc := g236_chi_K 4.
by split=> //; [exact: g254_connected_K4 | move=> h; exact: h _ _ (leqnn 4) g254_connected_K4 hc].
Qed.

Definition g254_tom_no_k_guard : Prop :=
  forall (G : sgraph) (k : nat), connected [set: G] -> χ([set: G]) = k ->
    #|[set f : {ffun G -> 'I_k} | proper_colouring f]| <= k`! * (k - 1) ^ (#|G| - k) /\
    (#|[set f : {ffun G -> 'I_k} | proper_colouring f]| = k`! * (k - 1) ^ (#|G| - k) <->
       clique (x254_two_core G) /\ #|x254_two_core G| = k).

Definition g254_tom_ntt_claim : Prop :=
  ~ g254_tom_no_k_guard /\ (g254_tom_no_k_guard -> tomescu_connected_colouring_count_statement).

Theorem g254_tom_not_trivially_true : g254_tom_ntt_claim.
Proof.
split; last by move=> h G k _; exact: h.
move=> h; have [_ e] := h 'K_2 2 connected_K2 (g236_chi_K 2).
have [_ hK2] := g254_two_core_helper_sanity.
move: e; rewrite hK2 g254_K2_colourings card_ord cards0.
by case=> /(_ erefl) [].
Qed.

Definition g254_tomkc_hyp_claim : Prop :=
  [/\ 4 <= 4, connected [set: 'K_4], χ([set: 'K_4]) = 4 &
      (tomescu_colouring_count_rooted_trees_statement ->
         #|[set f : {ffun 'K_4 -> 'I_4} | proper_colouring f]| <= 4`! * (4 - 1) ^ (#|'K_4| - 4) /\
         (#|[set f : {ffun 'K_4 -> 'I_4} | proper_colouring f]| = 4`! * (4 - 1) ^ (#|'K_4| - 4) <->
            clique (x254_two_core 'K_4) /\ #|x254_two_core 'K_4| = 4))].

Theorem g254_tomkc_hyp_inhabited : g254_tomkc_hyp_claim.
Proof. exact: g254_tom_hyp_inhabited. Qed.

Definition g254_tomkc_ntt_claim : Prop :=
  ~ g254_tom_no_k_guard /\ (g254_tom_no_k_guard -> tomescu_colouring_count_rooted_trees_statement).

Theorem g254_tomkc_not_trivially_true : g254_tomkc_ntt_claim.
Proof. exact: g254_tom_not_trivially_true. Qed.

Definition g254_tompk_hyp_claim : Prop :=
  [/\ 4 <= 4, connected [set: 'K_4], χ([set: 'K_4]) = 4 &
      (tomescu_colouring_count_rooted_trees_duplicate_statement ->
         #|[set f : {ffun 'K_4 -> 'I_4} | proper_colouring f]| <= 4`! * (4 - 1) ^ (#|'K_4| - 4) /\
         (#|[set f : {ffun 'K_4 -> 'I_4} | proper_colouring f]| = 4`! * (4 - 1) ^ (#|'K_4| - 4) <->
            clique (x254_two_core 'K_4) /\ #|x254_two_core 'K_4| = 4))].

Theorem g254_tompk_hyp_inhabited : g254_tompk_hyp_claim.
Proof. exact: g254_tom_hyp_inhabited. Qed.

Definition g254_tompk_ntt_claim : Prop :=
  ~ g254_tom_no_k_guard /\ (g254_tom_no_k_guard -> tomescu_colouring_count_rooted_trees_duplicate_statement).

Theorem g254_tompk_not_trivially_true : g254_tompk_ntt_claim.
Proof. exact: g254_tom_not_trivially_true. Qed.

Definition g254_tom530_hyp_claim : Prop :=
  [/\ 4 <= 4, connected [set: 'K_4], χ([set: 'K_4]) = 4 &
      (tomescu_colouring_count_two_core_duplicate_statement ->
         #|[set f : {ffun 'K_4 -> 'I_4} | proper_colouring f]| <= 4`! * (4 - 1) ^ (#|'K_4| - 4) /\
         (#|[set f : {ffun 'K_4 -> 'I_4} | proper_colouring f]| = 4`! * (4 - 1) ^ (#|'K_4| - 4) <->
            clique (x254_two_core 'K_4) /\ #|x254_two_core 'K_4| = 4))].

Theorem g254_tom530_hyp_inhabited : g254_tom530_hyp_claim.
Proof. exact: g254_tom_hyp_inhabited. Qed.

Definition g254_tom530_ntt_claim : Prop :=
  ~ g254_tom_no_k_guard /\ (g254_tom_no_k_guard -> tomescu_colouring_count_two_core_duplicate_statement).

Theorem g254_tom530_not_trivially_true : g254_tom530_ntt_claim.
Proof. exact: g254_tom_not_trivially_true. Qed.

(** ** arxiv:2202.09118#01 *)

Definition g254_mh_hyp_claim : Prop :=
  [/\ 1 <= 1, ~ x254_odd_multihole 'K_1 1 &
      (odd_multihole_free_poly_chi_bounded_statement ->
         poly_chi_bounded (fun G : sgraph => ~ x254_odd_multihole G 1))].

Theorem g254_mh_hyp_inhabited : g254_mh_hyp_claim.
Proof. by split=> //; [have [] := g254_multihole_helper_sanity | move=> h; exact: h]. Qed.

Definition g254_mh_all_graphs : Prop :=
  forall k : nat, 1 <= k -> poly_chi_bounded (fun G : sgraph => True).

Definition g254_mh_ntt_claim : Prop :=
  ~ g254_mh_all_graphs /\ (g254_mh_all_graphs -> odd_multihole_free_poly_chi_bounded_statement).

Theorem g254_mh_not_trivially_true : g254_mh_ntt_claim.
Proof.
split; last by move=> h k k1; have [c [d hb]] := h k k1; exists c, d => G _; exact: hb.
move=> h; have [c [d hb]] := h 1 isT.
have [ho [_ hc]] := gap_graph_parameters (c * 4 ^ d).
have := hb (gap_graph (c * 4 ^ d)) I; rewrite ho hc.
by rewrite -{2}[c * 4 ^ d]addn0 leq_add2l.
Qed.

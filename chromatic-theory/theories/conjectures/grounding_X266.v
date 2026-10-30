(** * Chromatic.conjectures.grounding_X266 -- grounding certificates for wave X266 (2026-10-30)

    For each of the three rows: hyp_inhabited (the body's conditions hold together at a small instance, and the
    statement gives its consequence: unbounded clustering, or bounded Hall ratio with unbounded fractional chromatic
    number) and not_trivially_true (a variant without the guard coupling the clustering to the order, or without
    "H a subgraph of G", is false and implies the statement); helper_sanity for the two helper groups (treewidth,
    Hall ratio), listed in every row.  Value lemmas: every graph has treewidth at most #|G| - 1, and a graph with
    an edge has no decomposition of width 0; K_2 boxtimes P_2 and K_2 boxtimes K_2 (both K_4) have no 2-colouring,
    resp. 3-colouring, of clustering 1; every graph has a colouring of clustering #|G|; the order bound
    (x + 1)^e <= N gives x^e < N^c; alpha(A) <= #|A|; rho(K_n) = n; chi_f(K_2) > 1; every subgraph of K_2 has an
    independent set of degree weight at least |E(H)| / 2; an independent set of K_n has degree sum at most n - 1, so
    K_(2p+1) has none of degree weight (q / p) |E|. *)

From GTBase Require Import base common bag_decompositions path_graphs.
From Chromatic.conjectures Require Import X130 X264 X266.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Treewidth *************************************************************** *)

(** Every graph has treewidth at most #|G| - 1: one bag holding every vertex, over the one-vertex path. *)
Lemma g266_treewidth_all (G : sgraph) : x266_treewidth_at_most G #|G|.-1.
Proof.
exists (ordinal_path 1), (fun _ => [set: G]); split.
  apply/tree_bag_decompositionP; split; first exact: ordinal_path_is_tree.
  have i0 : ordinal_path 1 := ord0.
  split; [by move=> v; exists i0; rewrite inE | split; [by move=> x y _; exists i0; rewrite !inE | ]].
  move=> v; have -> : [set _ | v \in [set: G]] = [set: ordinal_path 1] by apply/setP => t; rewrite !inE.
  by case: (ordinal_path_is_tree 1).
by move=> _; rewrite cardsT; case: #|G|.
Qed.

(** A graph with an edge has no decomposition of width 0: the edge needs a bag holding both ends. *)
Lemma g266_treewidth0_edge (G : sgraph) (x y : G) : x -- y -> ~ x266_treewidth_at_most G 0.
Proof.
move=> xy [T [bag [[_ hd] hb]]]; have [i [xi yi]] := bag_decomposition_edge hd xy.
have : #|[set x; y]| <= #|bag i| by apply/subset_leq_card/subsetP => z; rewrite !inE => /orP[] /eqP ->.
by rewrite cards2 (sg_edgeNeq xy) => /leq_trans/(_ (hb i)).
Qed.

(** ** Clustering ************************************************************** *)

(** Every graph has a colouring by a nonempty palette of clustering #|G|. *)
Lemma g266_clustered_all (G : sgraph) (k : nat) : 0 < k -> clustered_colouring G k #|G|.
Proof. by case: k => // k _; exists (fun _ => ord0) => S _ _; exact: max_card. Qed.

(** K_2 boxtimes P_2 (= K_4) has no 2-colouring of clustering 1: two of its four vertices share a colour, and every
    two distinct vertices are adjacent. *)
Lemma g266_K2P2_no_clustering1 : ~ clustered_colouring (x264_strong_product ('K_2) (ordinal_path 2)) 2 1.
Proof.
move=> [col hcol].
have /injectivePn [u [v uv e]] : ~~ injectiveb col.
  by apply/negP => /injectiveP/leq_card; rewrite card_ord /= card_prod !card_ord.
have uvE : u -- v.
  move: u v uv {e}; case=> -[[|[|?]] ?] -[[|[|?]] ?] //; case=> -[[|[|?]] ?] -[[|[|?]] ?] //.
suff : monochromatic_on col [set u; v] by move/(hcol _ (connected2 uvE)); rewrite cards2 uv.
by rewrite monochromatic_on_pair e.
Qed.

(** K_2 boxtimes K_2 (= K_4) has no 3-colouring of clustering 1. *)
Lemma g266_K2K2_no_clustering1 : ~ clustered_colouring (x264_strong_product ('K_2) ('K_2)) 3 1.
Proof.
move=> [col hcol].
have /injectivePn [u [v uv e]] : ~~ injectiveb col.
  by apply/negP => /injectiveP/leq_card; rewrite card_ord /= card_prod !card_ord.
have uvE : u -- v.
  move: u v uv {e}; case=> -[[|[|?]] ?] -[[|[|?]] ?] //; case=> -[[|[|?]] ?] -[[|[|?]] ?] //.
suff : monochromatic_on col [set u; v] by move/(hcol _ (connected2 uvE)); rewrite cards2 uv.
by rewrite monochromatic_on_pair e.
Qed.

(** The order bound behind "infinitely many": if (x + 1)^e <= N then x^e < N^c (e, c > 0). *)
Lemma g266_guard (x e c N : nat) : 0 < e -> 0 < c -> x.+1 ^ e <= N -> x ^ e < N ^ c.
Proof.
move=> e0 c0 hN; have N0 : 0 < N by apply: leq_trans hN; rewrite expn_gt0.
apply: leq_trans (_ : x.+1 ^ e <= N ^ c); first by rewrite ltn_exp2r.
by apply: leq_trans hN _; rewrite -{1}(expn1 N) leq_pexp2l.
Qed.

(** ** Hall ratio and fractional chromatic number ******************************* *)

Lemma g266_alpha_le_card (G : sgraph) (A : {set G}) : α(A) <= #|A|.
Proof. by case: alphaP => S /maxstabsetW /stabsetsP [sub _]; exact: subset_leq_card. Qed.

(** rho(K_n) <= n: a subgraph of K_n has at most n vertices and, if nonempty, an independent vertex. *)
Lemma g266_hall_K (n : nat) : x266_hall_ratio_le ('K_n) n 1.
Proof.
move=> H hs; rewrite mul1n; case: (posnP #|H|) => [-> // | H0].
have a0 : 0 < α([set: H]).
  by rewrite lt0n alpha_eq0; have [v _] := card_gt0P H0; apply/set0Pn; exists v; rewrite inE.
by apply: leq_trans (has_subgraph_card hs) _; rewrite card_ord leq_pmulr.
Qed.

(** rho(K_n) > n - 1 for n > 0: K_n itself has n vertices and independence number at most 1. *)
Lemma g266_hall_K_lt (n : nat) : 0 < n -> ~ x266_hall_ratio_le ('K_n) n.-1 1.
Proof.
move=> n0 /(_ ('K_n) (has_subgraph_refl _)); rewrite mul1n card_ord.
have cl : clique [set: 'K_n] by move=> x y _ _ xy; rewrite /edge_rel /= xy.
have a1 : α([set: 'K_n]) <= 1.
  by case: alphaP => S /maxstabset_stable st; have := cliqueIstable cl st; rewrite setTI.
move=> /leq_trans/(_ (leq_mul (leqnn n.-1) a1)); rewrite muln1.
by rewrite leqNgt ltn_predL n0.
Qed.

(** chi_f(K_2) > 1: an (a:b)-fold colouring of an edge needs a >= 2 b. *)
Lemma g266_frac_K2 : ~ x130_frac_chi_le ('K_2) 1 1.
Proof.
move=> [a [b [f [b0 hf]]]]; rewrite muln1 mul1n.
have := @bfold_colourings.bfold_colouring_edge ('K_2) a b f ord0 ord_max hf isT.
by move=> h2 hab; have := leq_trans h2 hab; rewrite -[X in _ <= X]mul1n leq_pmul2r.
Qed.

(** Every subgraph H of K_2 has an independent set of degree weight at least |E(H)| / 2: H has at most one edge,
    and one end of it has degree at least 1. *)
Lemma g266_degree_weight_K2 (H : sgraph) : has_subgraph ('K_2) H ->
  exists I : {set H}, stable I /\ 1 * #|E(H)| <= 2 * \sum_(v in I) #|N(v)|.
Proof.
move=> /has_subgraphP [f [finj fhom]]; rewrite mul1n.
have hE : #|E(H)| <= 1 by have := sub_card_edge f finj fhom; rewrite card_edge_Kn.
case: (posnP #|E(H)|) => [-> | E0]; first by exists set0; split; [exact: stable0 |].
have [e] := card_gt0P E0; case/imset2P => x y _; rewrite inE => xy _.
exists [set x]; split; first exact: stable1.
rewrite big_set1; apply: leq_trans hE _; apply: leq_trans (leq_pmull _ (isT : 0 < 2)).
by apply/card_gt0P; exists y; rewrite in_opn.
Qed.

(** In K_n an independent set has at most one vertex, of degree n - 1, so its degree sum is at most n - 1. *)
Lemma g266_K_stable_degree_sum (n : nat) (I : {set 'K_n}) : stable I -> \sum_(v in I) #|N(v)| <= n.-1.
Proof.
move=> st; have cl : clique [set: 'K_n] by move=> x y _ _ xy; rewrite /edge_rel /= xy.
have I1 : #|I| <= 1 by have := cliqueIstable cl st; rewrite setTI.
rewrite (eq_bigr (fun _ => n.-1)).
  move=> v _; have -> : N(v) = [set~ v] by apply/setP => u; rewrite in_opn !inE /edge_rel /= eq_sym.
  by rewrite cardsC1 card_ord.
by rewrite sum_nat_const; apply: leq_trans (leq_mul I1 (leqnn _)) _; rewrite mul1n.
Qed.

(** K_(2p+1) has no independent set of degree weight at least (q / p) |E| for p, q > 0:
    q C(2p+1, 2) = q p (2p+1) > p 2p. *)
Lemma g266_degree_weight_K_odd (p q : nat) : 0 < p -> 0 < q ->
  ~ exists I : {set 'K_(p.*2.+1)}, stable I /\ q * #|E('K_(p.*2.+1))| <= p * \sum_(v in I) #|N(v)|.
Proof.
move=> p0 q0 [I [st h]]; have := leq_trans h (leq_mul (leqnn p) (g266_K_stable_degree_sum st)).
rewrite card_edge_Kn bin2 /= -doubleMr doubleK.
apply/negP; rewrite -ltnNge; apply: (leq_trans _ (leq_pmull _ q0)).
by rewrite mulSn [p.*2 * p]mulnC -[X in X < _]add0n ltn_add2r.
Qed.

(** ** Certificates *)

(** arxiv:2407.21360#00 *)
Definition g266_pc_hyp_claim : Prop :=
  [/\ x266_treewidth_at_most ('K_2) 1, (1 * 1) ^ (2 ^ 2 - 2 + 1) < (#|'K_2| * 2) ^ 2,
      ~ clustered_colouring (x264_strong_product ('K_2) (ordinal_path 2)) 2 1 &
      (bounded_treewidth_path_product_clustering_statement ->
         exists t : nat, forall s : nat, exists (H : sgraph) (n : nat),
           x266_treewidth_at_most H t /\ ~ clustered_colouring (x264_strong_product H (ordinal_path n)) 2 s)].

Theorem g266_pc_hyp_inhabited : g266_pc_hyp_claim.
Proof.
split; [by have := g266_treewidth_all ('K_2); rewrite card_ord | by rewrite card_ord |
  exact: g266_K2P2_no_clustering1 |].
move=> /(_ 2 (leqnn 2)) [t [q [_ h]]]; exists t => s.
have [H [n [hM htw hs]]] := h ((q * s).+1 ^ 3).
by exists H, n; split=> //; apply: hs; exact: g266_guard hM.
Qed.

Definition g266_pc_unguarded : Prop :=
  forall c : nat, 2 <= c ->
    exists t q : nat, 0 < q /\
      forall M : nat, exists (H : sgraph) (n : nat),
        [/\ M <= #|H| * n, x266_treewidth_at_most H t &
            forall s : nat, ~ clustered_colouring (x264_strong_product H (ordinal_path n)) c s].

Definition g266_pc_ntt_claim : Prop :=
  ~ g266_pc_unguarded /\ (g266_pc_unguarded -> bounded_treewidth_path_product_clustering_statement).

Theorem g266_pc_not_trivially_true : g266_pc_ntt_claim.
Proof.
split; last first.
  move=> h c c2; have [t [q [q0 hq]]] := h c c2; exists t, q; split=> // M.
  by have [H [n [hM htw hs]]] := hq M; exists H, n; split=> // s _; exact: hs.
move=> /(_ 2 (leqnn 2)) [t [q [_ /(_ 0) [H [n [_ _ hs]]]]]].
by apply: (hs #|x264_strong_product H (ordinal_path n)|); exact: g266_clustered_all.
Qed.

(** arxiv:2407.21360#01 *)
Definition g266_tc_hyp_claim : Prop :=
  [/\ x266_treewidth_at_most ('K_2) 1, (1 * 1) ^ 7 < (#|'K_2| * #|'K_2|) ^ 4,
      ~ clustered_colouring (x264_strong_product ('K_2) ('K_2)) 3 1 &
      (bounded_treewidth_products_three_colour_clustering_statement ->
         exists t : nat, forall s : nat, exists H1 H2 : sgraph,
           [/\ x266_treewidth_at_most H1 t, x266_treewidth_at_most H2 t &
               ~ clustered_colouring (x264_strong_product H1 H2) 3 s])].

Theorem g266_tc_hyp_inhabited : g266_tc_hyp_claim.
Proof.
split; [by have := g266_treewidth_all ('K_2); rewrite card_ord | by rewrite card_ord |
  exact: g266_K2K2_no_clustering1 |].
move=> [t [q [_ _ h]]]; exists t => s.
have [H1 [H2 [hM tw1 tw2 hs]]] := h ((q * s).+1 ^ 7).
by exists H1, H2; split=> //; apply: hs; exact: g266_guard hM.
Qed.

Definition g266_tc_unguarded : Prop :=
  exists t q : nat,
    [/\ 0 < t, 0 < q &
        forall M : nat, exists H1 H2 : sgraph,
          [/\ M <= #|H1| * #|H2|, x266_treewidth_at_most H1 t, x266_treewidth_at_most H2 t &
              forall s : nat, ~ clustered_colouring (x264_strong_product H1 H2) 3 s]].

Definition g266_tc_ntt_claim : Prop :=
  ~ g266_tc_unguarded /\ (g266_tc_unguarded -> bounded_treewidth_products_three_colour_clustering_statement).

Theorem g266_tc_not_trivially_true : g266_tc_ntt_claim.
Proof.
split; last first.
  move=> [t [q [t0 q0 hq]]]; exists t, q; split=> // M.
  by have [H1 [H2 [hM tw1 tw2 hs]]] := hq M; exists H1, H2; split=> // s _; exact: hs.
move=> [t [q [_ _ /(_ 0) [H1 [H2 [_ _ _ hs]]]]]].
by apply: (hs #|x264_strong_product H1 H2|); exact: g266_clustered_all.
Qed.

(** arxiv:1812.07327#01 *)
Definition g266_dw_hyp_claim : Prop :=
  [/\ ~ x130_frac_chi_le ('K_2) 1 1, x266_hall_ratio_le ('K_2) 2 1,
      (forall H : sgraph, has_subgraph ('K_2) H ->
         exists I : {set H}, stable I /\ 1 * #|E(H)| <= 2 * \sum_(v in I) #|N(v)|) &
      (hall_ratio_degree_weighted_fractional_chromatic_statement ->
         exists p q : nat, 0 < q /\
           forall F : nat, exists G : sgraph, ~ x130_frac_chi_le G F 1 /\ x266_hall_ratio_le G p q)].

Theorem g266_dw_hyp_inhabited : g266_dw_hyp_claim.
Proof.
split; [exact: g266_frac_K2 | exact: g266_hall_K | exact: g266_degree_weight_K2 |].
move=> [p [q [_ q0 h]]]; exists p, q; split=> // F.
by have [G [hchi hr _]] := h F; exists G.
Qed.

(** The statement without its inner hypothesis has_subgraph G H: every graph H, not only the subgraphs of G. *)
Definition g266_dw_every_graph : Prop :=
  exists p q : nat,
    [/\ 0 < p, 0 < q &
        forall F : nat, exists G : sgraph,
          [/\ ~ x130_frac_chi_le G F 1, x266_hall_ratio_le G p q &
              forall H : sgraph,
                exists I : {set H}, stable I /\ q * #|E(H)| <= p * \sum_(v in I) #|N(v)|]].

Definition g266_dw_ntt_claim : Prop :=
  ~ g266_dw_every_graph /\ (g266_dw_every_graph -> hall_ratio_degree_weighted_fractional_chromatic_statement).

Theorem g266_dw_not_trivially_true : g266_dw_ntt_claim.
Proof.
split; last first.
  move=> [p [q [p0 q0 h]]]; exists p, q; split=> // F.
  by have [G [hchi hr hH]] := h F; exists G; split=> // H _; exact: hH.
move=> [p [q [p0 q0 /(_ 0) [G [_ _ /(_ ('K_(p.*2.+1)))]]]]].
exact: (g266_degree_weight_K_odd p0 q0).
Qed.

(** ** Helper sanity (the same two groups in every row) *)

(** Treewidth: every graph has treewidth at most #|G| - 1; K_2 has no decomposition of width 0. *)
Definition g266_tw_helper_claim : Prop :=
  (forall G : sgraph, x266_treewidth_at_most G #|G|.-1) /\ ~ x266_treewidth_at_most ('K_2) 0.

Theorem g266_tw_helper_sanity : g266_tw_helper_claim.
Proof.
split; first exact: g266_treewidth_all.
exact: (@g266_treewidth0_edge ('K_2) ord0 ord_max isT).
Qed.

(** Hall ratio: rho(K_n) = n. *)
Definition g266_hr_helper_claim : Prop :=
  (forall n : nat, x266_hall_ratio_le ('K_n) n 1) /\
  (forall n : nat, 0 < n -> ~ x266_hall_ratio_le ('K_n) n.-1 1).

Theorem g266_hr_helper_sanity : g266_hr_helper_claim.
Proof. by split; [exact: g266_hall_K | exact: g266_hall_K_lt]. Qed.

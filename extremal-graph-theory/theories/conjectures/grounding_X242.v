(** * Extremal.conjectures.grounding_X242 -- grounding certificates of wave X242.

    For each of the five rows: hyp_inhabited (the hypotheses hold on a concrete instance, and the statement then
    yields its conclusion there) and not_trivially_true in the contract form of meta/EXPANSION_PLAN.md 4.4 (the row
    with a load-bearing hypothesis dropped is false, and that variant implies the row): the density hypothesis for
    erdos:182 (an edgeless graph has no nonempty 3-regular subgraph), the Turan hypotheses for erdos:574 and erdos:147
    (m = 0), "no K_5" for erdos:533 (the dense K_(2t+1): a triangle-free induced set of K_n has at most 2 vertices) and
    "edge_count G = m" for erdos:1008 (a large m on K_1).  The wave has no local helper, so no helper_sanity
    certificate.  Small instances: K_4 3-regular inside K_6, the edgeless complete_multipartite_graph 1 n,
    K_{2,2} = complete_multipartite_graph 2 2 (bipartite, minimum degree 2, ex(1; K_{2,2}) = 0), grounding_X239's
    ex(1; {C_3, C_4}) = 0 and grounding_X241's edge count of K_(2t+1). *)

From Extremal.conjectures Require Import D2tur grounding_X239 grounding_X241 X242.
(* GTBase last: its canonical [edge_count] must shadow D2tur's eta-alias of the same name. *)
From GTBase Require Import base common complete_multipartite_graphs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Small instances *)

(** An edgeless graph has no nonempty k-regular subgraph for k >= 1. *)
Lemma g242_edgeless_no_regular (G H : sgraph) (k : nat) :
  (forall x y : G, ~~ x -- y) -> 0 < k -> 0 < #|H| -> regular H k -> ~ has_subgraph G H.
Proof.
move=> noE k0 H0 rH /has_subgraphP [f [_ hf]].
have /card_gt0P [v _] := H0.
have : 0 < #|N(v)| by rewrite rH.
case/card_gt0P => w; rewrite inE => vw.
by have := hf _ _ vw; rewrite (negbTE (noE _ _)).
Qed.

Lemma g242_K4_regular : regular 'K_4 3.
Proof.
move=> v; have -> : N(v) = ~: [set v] by apply/setP => w; rewrite !inE eq_sym.
by rewrite cardsC1 card_ord.
Qed.

Lemma g242_K4_in_K6 : has_subgraph 'K_6 'K_4.
Proof.
apply/has_subgraphP; exists (widen_ord (isT : 4 <= 6)); split; first by move=> i j /(congr1 val) /= /val_inj.
by move=> i j ij; rewrite /edge_rel /= -(inj_eq val_inj) /= (inj_eq val_inj).
Qed.

Lemma g242_edgeless_multipartite (n : nat) (x y : complete_multipartite_graph 1 n) : ~~ x -- y.
Proof. by rewrite complete_multipartite_edgeE (ord1 x.1) (ord1 y.1) eqxx. Qed.

(** ** Row erdos:182 *)

Definition g242_reg_hyp_claim : Prop :=
  [/\ #|'K_6| ^ 3 <= edge_count 'K_6 ^ 2, regular 'K_4 3, has_subgraph 'K_6 'K_4 &
      (regular_subgraph_superlinear_edges_statement -> exists n0 : nat,
         forall G : sgraph, n0 <= #|G| -> #|G| ^ 3 <= edge_count G ^ 2 ->
           exists H : sgraph, [/\ 0 < #|H|, regular H 3 & has_subgraph G H])].

Theorem g242_reg_hyp_inhabited : g242_reg_hyp_claim.
Proof.
split; [by rewrite card_ord edge_count_Kn | exact: g242_K4_regular | exact: g242_K4_in_K6 |].
by move=> h; exact: h 3 (leqnn 3) 2 isT.
Qed.

(** Contract form: without the density hypothesis, an edgeless graph on n0 vertices has no nonempty 3-regular
    subgraph. *)
Definition g242_reg_no_density : Prop :=
  forall k : nat, 3 <= k -> forall q : nat, 1 <= q -> exists n0 : nat,
    forall G : sgraph, n0 <= #|G| -> exists H : sgraph, [/\ 0 < #|H|, regular H k & has_subgraph G H].

Definition g242_reg_ntt_claim : Prop :=
  ~ g242_reg_no_density /\ (g242_reg_no_density -> regular_subgraph_superlinear_edges_statement).

Theorem g242_reg_not_trivially_true : g242_reg_ntt_claim.
Proof.
split.
- move=> h; have [n0 hn] := h 3 (leqnn 3) 1 isT.
  have [|H [H0 rH sH]] := hn (complete_multipartite_graph 1 n0).
    by rewrite card_complete_multipartite_graph mul1n.
  exact: (@g242_edgeless_no_regular (complete_multipartite_graph 1 n0) H 3 (@g242_edgeless_multipartite n0) isT H0 rH sH).
- by move=> h k k3 q q1; have [n0 hn] := h k k3 q q1; exists n0 => G nG _; exact: hn.
Qed.

(** ** Row erdos:574 *)

Definition g242_cyc_hyp_claim : Prop :=
  [/\ is_turan_number 1 (fun i : 'I_2 => cycle_graph (i + (2 * 0 + 3))) 0 &
      (odd_even_cycle_free_turan_asymptotic_statement -> exists n0 : nat,
         forall n m : nat, n0 <= n -> is_turan_number n (fun i : 'I_2 => cycle_graph (i + (2 * 0 + 3))) m ->
           1 ^ (0 + 2) * n ^ (0 + 3) <= 2 ^ (0 + 3) * (1 + 1) ^ (0 + 2) * m ^ (0 + 2) /\
           2 ^ (0 + 3) * 1 ^ (0 + 2) * m ^ (0 + 2) <= (1 + 1) ^ (0 + 2) * n ^ (0 + 3))].

Theorem g242_cyc_hyp_inhabited : g242_cyc_hyp_claim.
Proof. by split; [exact: g239_turan_C3C4_1 | move=> h; exact: h 0 1 isT]. Qed.

(** Contract form: without the Turan hypothesis, m = 0 breaks the lower bound. *)
Definition g242_cyc_no_turan : Prop :=
  forall j q : nat, 1 <= q -> exists n0 : nat,
    forall n m : nat, n0 <= n ->
      q ^ (j + 2) * n ^ (j + 3) <= 2 ^ (j + 3) * (q + 1) ^ (j + 2) * m ^ (j + 2) /\
      2 ^ (j + 3) * q ^ (j + 2) * m ^ (j + 2) <= (q + 1) ^ (j + 2) * n ^ (j + 3).

Definition g242_cyc_ntt_claim : Prop :=
  ~ g242_cyc_no_turan /\ (g242_cyc_no_turan -> odd_even_cycle_free_turan_asymptotic_statement).

Theorem g242_cyc_not_trivially_true : g242_cyc_ntt_claim.
Proof.
split.
- move=> h; have [n0 hn] := h 0 1 isT; have [h1 _] := hn n0.+1 0 (leqnSn n0).
  by move: h1; rewrite exp0n // muln0 exp1n mul1n leqn0 expn_eq0.
- by move=> h j q q1; have [n0 hn] := h j q q1; exists n0 => n m nn _; exact: hn.
Qed.

(** ** Row erdos:147 *)

Lemma g242_K22_bipartite : bipartite (complete_multipartite_graph 2 2).
Proof.
exists (fun x : complete_multipartite_graph 2 2 => x.1 == ord0) => x y.
rewrite complete_multipartite_edgeE.
by case: x => [[[|[|a]] Ha] u]; case: y => [[[|[|b]] Hb] w].
Qed.

Lemma g242_K22_min_degree : min_degree_at_least (complete_multipartite_graph 2 2) 2.
Proof.
move=> [a u]; apply/card_gt1P.
have [o ov] : {o : 'I_2 | o != a} by case: a => [[|[|a]] Ha]; [exists ord_max | exists ord0 | by []].
exists (o, ord0), (o, ord_max); split; rewrite ?inE ?complete_multipartite_edgeE /= 1?eq_sym //.
by rewrite xpair_eqE eqxx.
Qed.

Lemma g242_turan_K22_1 : is_turan_number 1 (fun _ : 'I_1 => complete_multipartite_graph 2 2) 0.
Proof.
split.
- exists 'K_1; split; [by rewrite card_ord | by rewrite /D2tur.edge_count (proj2 edge_count_K0_K1) |].
  by move=> i [h hi _]; have := leq_card h hi; rewrite card_complete_multipartite_graph card_ord.
- move=> m' [G [hG <- _]].
  pose h (v : G) : 'K_1 := cast_ord hG (enum_rank v).
  have hi : injective h by move=> x y /cast_ord_inj /enum_rank_inj.
  have e : #|E(G)| <= #|E('K_1)|.
    apply: (@sub_card_edge G 'K_1 h hi) => x y xy.
    by rewrite /edge_rel /= (inj_eq hi) (sg_edgeNeq xy).
  apply: leq_trans e _.
  by rewrite -[X in X <= _]/(edge_count 'K_1) (proj2 edge_count_K0_K1).
Qed.

Definition g242_mindeg_hyp_claim : Prop :=
  [/\ bipartite (complete_multipartite_graph 2 2), min_degree_at_least (complete_multipartite_graph 2 2) (0 + 2),
      is_turan_number 1 (fun _ : 'I_1 => complete_multipartite_graph 2 2) 0 &
      (bipartite_min_degree_turan_exponent_statement -> exists s c n0 : nat, 1 <= s /\
         forall n m : nat, n0 <= n -> is_turan_number n (fun _ : 'I_1 => complete_multipartite_graph 2 2) m ->
           n ^ ((2 * 0 + 1) * s + 0 + 1) <= (c * m) ^ ((0 + 1) * s))].

Theorem g242_mindeg_hyp_inhabited : g242_mindeg_hyp_claim.
Proof.
split; [exact: g242_K22_bipartite | exact: g242_K22_min_degree | exact: g242_turan_K22_1 |].
by move=> h; exact: h 0 _ g242_K22_bipartite g242_K22_min_degree.
Qed.

(** Contract form: without the Turan hypothesis, m = 0 breaks the bound (K_{2,2}). *)
Definition g242_mindeg_no_turan : Prop :=
  forall (t : nat) (H : sgraph), bipartite H -> min_degree_at_least H (t + 2) ->
    exists s c n0 : nat, 1 <= s /\
      forall n m : nat, n0 <= n -> n ^ ((2 * t + 1) * s + t + 1) <= (c * m) ^ ((t + 1) * s).

Definition g242_mindeg_ntt_claim : Prop :=
  ~ g242_mindeg_no_turan /\ (g242_mindeg_no_turan -> bipartite_min_degree_turan_exponent_statement).

Theorem g242_mindeg_not_trivially_true : g242_mindeg_ntt_claim.
Proof.
split.
- move=> h; have [s [c [n0 [s1 hs]]]] := h 0 _ g242_K22_bipartite g242_K22_min_degree.
  have := hs n0.+1 0 (leqnSn n0); rewrite muln0.
  by rewrite muln0 exp0n ?mul1n // leqn0 expn_eq0.
- by move=> h t H Hb Hd; have [s [c [n0 [s1 hs]]]] := h t H Hb Hd; exists s, c, n0; split=> // n m nn _; exact: hs.
Qed.

(** ** Row erdos:533 *)

(** In K_n, a vertex set whose induced subgraph has no triangle has at most 2 vertices. *)
Lemma g242_Kn_induced_triangle (n : nat) (S : {set 'K_n}) : ~ has_subgraph (induced S) 'K_3 -> #|S| <= 2.
Proof.
move=> noK3; rewrite leqNgt; apply/negP => S3; apply: noK3; apply/has_subgraphP.
have le : 3 <= #|induced S| by rewrite card_sig.
pose f (i : 'I_3) : induced S := enum_val (widen_ord le i).
have finj : injective f by move=> i j /enum_val_inj /(congr1 val) /= /val_inj.
exists f; split=> // i j ij.
by rewrite /edge_rel /= /edge_rel /= (inj_eq val_inj) (inj_eq finj).
Qed.

Definition g242_k5_hyp_claim : Prop :=
  [/\ (~ has_subgraph 'K_4 'K_5), #|'K_4| ^ 2 <= 3 * edge_count 'K_4 &
      (k5_free_dense_linear_triangle_free_set_statement -> exists c n0 : nat,
         forall G : sgraph, n0 <= #|G| -> ~ has_subgraph G 'K_5 -> #|G| ^ 2 <= 3 * edge_count G ->
           exists S : {set G}, ~ has_subgraph (induced S) 'K_3 /\ #|G| <= c * #|S|)].

Theorem g242_k5_hyp_inhabited : g242_k5_hyp_claim.
Proof.
split; last by move=> h; exact: h 3 isT.
- by move/has_subgraph_card; rewrite !card_ord.
- by rewrite edge_count_Kn card_ord.
Qed.

(** Contract form: without "no K_5", the dense complete graphs K_(2t+1) have no triangle-free set of three
    vertices. *)
Definition g242_k5_no_free : Prop :=
  forall q : nat, 1 <= q -> exists c n0 : nat,
    forall G : sgraph, n0 <= #|G| -> #|G| ^ 2 <= q * edge_count G ->
      exists S : {set G}, ~ has_subgraph (induced S) 'K_3 /\ #|G| <= c * #|S|.

Definition g242_k5_ntt_claim : Prop :=
  ~ g242_k5_no_free /\ (g242_k5_no_free -> k5_free_dense_linear_triangle_free_set_statement).

Theorem g242_k5_not_trivially_true : g242_k5_ntt_claim.
Proof.
split.
- move=> h; have [c [n0 hc]] := h 4 isT.
  set t := (n0 + c).+1.
  have nK : #|'K_(t.*2.+1)| = t.*2.+1 by rewrite card_ord.
  have n0le : n0 <= #|'K_(t.*2.+1)|.
    rewrite nK /t; apply: leq_trans (leq_addr c n0) _; apply: leq_trans (leqnSn _) _.
    by apply: leq_trans _ (leqnSn _); rewrite -addnn leq_addr.
  have dense : #|'K_(t.*2.+1)| ^ 2 <= 4 * edge_count 'K_(t.*2.+1).
    by rewrite nK g241_edge_count_Kodd mulnCA expnS expn1 leq_pmul2l // -mul2n ltn_pmul2r.
  have [S [noK3 hS]] := hc _ n0le dense.
  have := leq_trans hS (leq_mul (leqnn c) (g242_Kn_induced_triangle noK3)).
  rewrite nK /t leqNgt; apply/negP/negPn.
  by rewrite muln2 ltnS leq_double ltnW // ltnS leq_addl.
- by move=> h q q1; have [c [n0 hc]] := h q q1; exists c, n0 => G nG _; exact: hc.
Qed.
(** ** Row erdos:1008 *)

Definition g242_c4sub_hyp_claim : Prop :=
  [/\ edge_count 'K_2 = 1, E('K_2) \subset E('K_2),
      ~ has_subgraph (del_edge_set 'K_2 (E('K_2) :\: E('K_2))) (cycle_graph 4) &
      (c4_free_subgraph_two_thirds_statement -> exists c : nat, 1 <= c /\
         exists F : {set {set 'K_2}}, [/\ F \subset E('K_2),
           ~ has_subgraph (del_edge_set 'K_2 (E('K_2) :\: F)) (cycle_graph 4) & 1 ^ 2 <= (c * #|F|) ^ 3])].

Theorem g242_c4sub_hyp_inhabited : g242_c4sub_hyp_claim.
Proof.
split=> //; first by rewrite edge_count_Kn.
- by move/has_subgraph_card; rewrite !card_ord.
- by move=> [c [c1 h]]; exists c; split=> //; exact: h 'K_2 1 (edge_count_Kn 2).
Qed.

(** Contract form: without "edge_count G = m", a large m on K_1 (no edge) breaks the bound. *)
Definition g242_c4sub_no_count : Prop :=
  exists c : nat, 1 <= c /\
    forall (G : sgraph) (m : nat),
      exists F : {set {set G}}, [/\ F \subset E(G),
        ~ has_subgraph (del_edge_set G (E(G) :\: F)) (cycle_graph 4) & m ^ 2 <= (c * #|F|) ^ 3].

Definition g242_c4sub_ntt_claim : Prop :=
  ~ g242_c4sub_no_count /\ (g242_c4sub_no_count -> c4_free_subgraph_two_thirds_statement).

Theorem g242_c4sub_not_trivially_true : g242_c4sub_ntt_claim.
Proof.
split.
- move=> [c [c1 h]]; have [F [FE _ hF]] := h 'K_1 1.
  have F0 : #|F| = 0.
    apply/eqP; rewrite -leqn0; apply: leq_trans (subset_leq_card FE) _.
    by rewrite -/(edge_count 'K_1) (proj2 edge_count_K0_K1).
  by move: hF; rewrite F0 muln0.
- by move=> [c [c1 h]]; exists c; split=> // G m _; exact: h.
Qed.

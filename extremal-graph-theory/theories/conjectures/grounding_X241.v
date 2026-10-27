(** * Extremal.conjectures.grounding_X241 -- grounding certificates of wave X241.

    For each of the six rows: hyp_inhabited (the hypotheses hold on a concrete instance, and the statement then
    yields its conclusion there) and not_trivially_true in the contract form of meta/EXPANSION_PLAN.md 4.4 (the row
    with a load-bearing hypothesis dropped is false, and that variant implies the row): "no K_{2,2,2}" for erdos:579
    (the dense complete graphs K_(2t+1) have no stable set of two vertices), the Ramsey hypotheses for erdos:911
    (m = 0 on K_(2 C0 + 1)), erdos:1182 (R = 0 on a long path), erdos:166 (R = 0), erdos:546 (R = 2^(C+1) on K_2) and
    erdos:1014 (R1 = 1, R0 = 0).  The wave has no local helper, so no helper_sanity certificate.  Small instances:
    stable sets of K_n, the edge count of K_(2t+1), K_1 connected, paths with at most n edges, R^(K_2) = 1, and
    grounding_X240's R(H, K_1) = 1 and R(K_m, K_2) = m. *)

From Extremal.conjectures Require Import XE1 grounding_X240 X241.
From GTBase Require Import base common complete_multipartite_graphs path_graphs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Small instances *)

Lemma g241_Kn_stable (n : nat) (S : {set 'K_n}) : stable S -> #|S| <= 1.
Proof.
move=> st; rewrite leqNgt; apply/negP => /card_gt1P [x [y [xS yS xy]]].
have : ~~ stable S by apply/stablePn; exists x, y; split.
by rewrite st.
Qed.

Lemma g241_edge_count_Kodd (t : nat) : edge_count 'K_(t.*2.+1) = t.*2.+1 * t.
Proof. by rewrite edge_count_Kn bin2odd /= ?odd_double // -divn2 -muln2 mulnK. Qed.

Lemma g241_K1_connected : connected [set: 'K_1].
Proof. by apply: connectedTI => x y; rewrite (ord1 x) (ord1 y); exact: connect0. Qed.

(** ** Row erdos:579 *)

Definition g241_octa_hyp_claim : Prop :=
  [/\ ~ has_subgraph 'K_3 (complete_multipartite_graph 3 2), #|'K_3| ^ 2 <= 3 * edge_count 'K_3 &
      (octahedron_free_dense_linear_independent_set_statement -> exists c n0 : nat,
         forall G : sgraph, n0 <= #|G| -> ~ has_subgraph G (complete_multipartite_graph 3 2) ->
           #|G| ^ 2 <= 3 * edge_count G -> exists S : {set G}, stable S /\ #|G| <= c * #|S|)].

Theorem g241_octa_hyp_inhabited : g241_octa_hyp_claim.
Proof.
split; last by move=> h; exact: h 3 isT.
- by move/has_subgraph_card; rewrite card_complete_multipartite_graph card_ord.
- by rewrite edge_count_Kn card_ord.
Qed.

(** Contract form: without "no K_{2,2,2}", the complete graphs K_(2t+1) are dense and have no stable set of two
    vertices. *)
Definition g241_octa_no_free : Prop :=
  forall q : nat, 1 <= q -> exists c n0 : nat,
    forall G : sgraph, n0 <= #|G| -> #|G| ^ 2 <= q * edge_count G ->
      exists S : {set G}, stable S /\ #|G| <= c * #|S|.

Definition g241_octa_ntt_claim : Prop :=
  ~ g241_octa_no_free /\ (g241_octa_no_free -> octahedron_free_dense_linear_independent_set_statement).

Theorem g241_octa_not_trivially_true : g241_octa_ntt_claim.
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
  have [S [st hS]] := hc _ n0le dense.
  have := leq_trans hS (leq_mul (leqnn c) (g241_Kn_stable st)).
  rewrite muln1 nK /t leqNgt; apply/negP/negPn.
  apply: leq_trans (_ : c < (n0 + c).+1) _; first by rewrite ltnS leq_addl.
  by rewrite ltnW // ltnS -addnn leq_addr.
- by move=> h q q1; have [c [n0 hc]] := h q q1; exists c, n0 => G nG _; exact: hc.
Qed.

(** ** Row erdos:911 *)

Lemma g241_size_ramsey_K2 : xe1_size_ramsey_number 'K_2 'K_2 1.
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
  case c01: (col ord0 ord_max); [left | right]; exists id; split=> // x y xy; split=> //; by rewrite (colxy x y xy) c01.
- case=> [[G [eG hG]] | //]; exfalso.
  have := hG (fun _ _ => true) (fun _ _ => erefl).
  by case=> [[f [_ hf]] | [f [_ hf]]]; have [e _] := hf ord0 ord_max isT; exact: noedge eG e.
Qed.

Definition g241_size_hyp_claim : Prop :=
  [/\ 0 < #|'K_2|, 0 * #|'K_2| <= (edge_count 'K_2), xe1_size_ramsey_number 'K_2 'K_2 1 &
      (size_ramsey_superlinear_density_statement -> exists C0 : nat,
         forall (C : nat) (G : sgraph) (m : nat), C0 <= C -> 0 < #|G| -> C * #|G| <= edge_count G ->
           xe1_size_ramsey_number G G m -> 1 * C * edge_count G < m)].

Theorem g241_size_hyp_inhabited : g241_size_hyp_claim.
Proof. by split; [rewrite card_ord | | exact: g241_size_ramsey_K2 | move=> h; exact: h 1]. Qed.

(** Contract form: without the size-Ramsey hypothesis, m = 0 on the dense K_(2 C0 + 1). *)
Definition g241_size_no_ramsey : Prop :=
  forall M : nat, exists C0 : nat,
    forall (C : nat) (G : sgraph) (m : nat), C0 <= C -> 0 < #|G| -> C * #|G| <= edge_count G ->
      M * C * edge_count G < m.

Definition g241_size_ntt_claim : Prop :=
  ~ g241_size_no_ramsey /\ (g241_size_no_ramsey -> size_ramsey_superlinear_density_statement).

Theorem g241_size_not_trivially_true : g241_size_ntt_claim.
Proof.
split.
- move=> h; have [C0 hC] := h 1.
  have := hC C0 'K_(C0.*2.+1) 0 (leqnn C0); rewrite card_ord g241_edge_count_Kodd mulnC.
  by move=> /(_ isT (leqnn _)).
- by move=> h M; have [C0 hC] := h M; exists C0 => C G m CC G0 dense _; exact: hC.
Qed.

(** ** Row erdos:166 *)

Lemma g241_ramsey_K4_K1 : xe1_graph_ramsey_number 'K_4 'K_1 1.
Proof. by apply: g240_ramsey_K1; rewrite card_ord. Qed.

Definition g241_r4_hyp_claim : Prop :=
  [/\ xe1_graph_ramsey_number 'K_4 'K_1 1 &
      (ramsey_four_cubic_polylog_lower_statement -> exists c p k0 : nat, 0 < p /\
         forall k R : nat, k0 <= k -> xe1_graph_ramsey_number 'K_4 'K_k R -> k ^ 3 <= p * R * trunc_log 2 k ^ c)].

Theorem g241_r4_hyp_inhabited : g241_r4_hyp_claim.
Proof. by split; [exact: g241_ramsey_K4_K1 | ]. Qed.

(** Contract form: without the Ramsey hypothesis, R = 0 breaks the bound. *)
Definition g241_r4_no_ramsey : Prop :=
  exists c p k0 : nat, 0 < p /\ forall k R : nat, k0 <= k -> k ^ 3 <= p * R * trunc_log 2 k ^ c.

Definition g241_r4_ntt_claim : Prop :=
  ~ g241_r4_no_ramsey /\ (g241_r4_no_ramsey -> ramsey_four_cubic_polylog_lower_statement).

Theorem g241_r4_not_trivially_true : g241_r4_ntt_claim.
Proof.
split.
- by move=> [c [p [k0 [p0 h]]]]; have := h k0.+1 0 (leqnSn k0); rewrite muln0 !mul0n leqn0 expn_eq0.
- by move=> [c [p [k0 [p0 h]]]]; exists c, p, k0; split=> // k R kk _; exact: h.
Qed.

(** ** Row erdos:546 *)

Lemma g241_K2_min_degree : min_degree_at_least 'K_2 1.
Proof.
move=> v; rewrite card_gt0; apply/set0Pn.
by case: v => [[|[|v]] Hv] //; [exists ord_max | exists ord0]; rewrite inE.
Qed.

Definition g241_sqrt_hyp_claim : Prop :=
  [/\ min_degree_at_least 'K_2 1, xe1_diagonal_ramsey_number 'K_2 2 &
      (ramsey_sqrt_edges_exponential_upper_statement -> exists C : nat, trunc_log 2 2 ^ 2 <= C * edge_count 'K_2)].

Theorem g241_sqrt_hyp_inhabited : g241_sqrt_hyp_claim.
Proof.
split; [exact: g241_K2_min_degree | exact: g240_ramsey_Km_K2 2 |].
by move=> [C h]; exists C; exact: h 'K_2 2 g241_K2_min_degree (g240_ramsey_Km_K2 2).
Qed.

(** Contract form: without the Ramsey hypothesis, R = 2^(C+1) on K_2 breaks the bound. *)
Definition g241_sqrt_no_ramsey : Prop :=
  exists C : nat, forall (G : sgraph) (R : nat), min_degree_at_least G 1 ->
    trunc_log 2 R ^ 2 <= C * edge_count G.

Definition g241_sqrt_ntt_claim : Prop :=
  ~ g241_sqrt_no_ramsey /\ (g241_sqrt_no_ramsey -> ramsey_sqrt_edges_exponential_upper_statement).

Theorem g241_sqrt_not_trivially_true : g241_sqrt_ntt_claim.
Proof.
split.
- move=> [C h]; have := h 'K_2 (2 ^ C.+1) g241_K2_min_degree.
  rewrite trunc_expnK // edge_count_Kn bin2 /= muln1 => le.
  have : C.+1 <= C.+1 ^ 2 by rewrite expnS expn1 leq_pmulr.
  by move/leq_trans/(_ le); rewrite ltnn.
- by move=> [C h]; exists C => G R G1 _; exact: h.
Qed.

(** ** Row erdos:1014 *)

Definition g241_ratio1_hyp_claim : Prop :=
  [/\ xe1_graph_ramsey_number 'K_3 'K_1 1, xe1_graph_ramsey_number 'K_3 'K_2 3 &
      (off_diagonal_ramsey_consecutive_ratio_one_statement -> exists l0 : nat,
         forall l R0 R1 : nat, l0 <= l ->
           xe1_graph_ramsey_number 'K_3 'K_l R0 -> xe1_graph_ramsey_number 'K_3 'K_l.+1 R1 ->
           1 * R1 <= (1 + 1) * R0)].

Theorem g241_ratio1_hyp_inhabited : g241_ratio1_hyp_claim.
Proof.
split; [by apply: g240_ramsey_K1; rewrite card_ord | exact: g240_ramsey_Km_K2 3 |].
by move=> h; exact: h 3 (leqnn 3) 1 (leqnn 1).
Qed.

(** Contract form: without the Ramsey hypotheses, R1 = 1 and R0 = 0 break the bound. *)
Definition g241_ratio1_no_ramsey : Prop :=
  forall k : nat, 3 <= k -> forall q : nat, 1 <= q -> exists l0 : nat,
    forall l R0 R1 : nat, l0 <= l -> q * R1 <= (q + 1) * R0.

Definition g241_ratio1_ntt_claim : Prop :=
  ~ g241_ratio1_no_ramsey /\ (g241_ratio1_no_ramsey -> off_diagonal_ramsey_consecutive_ratio_one_statement).

Theorem g241_ratio1_not_trivially_true : g241_ratio1_ntt_claim.
Proof.
split.
- by move=> h; have [l0 hl] := h 3 (leqnn 3) 1 (leqnn 1); have := hl l0 0 1 (leqnn l0).
- by move=> h k k3 q q1; have [l0 hl] := h k k3 q q1; exists l0 => l R0 R1 ll _ _; exact: hl.
Qed.

(** ** Row erdos:1182 *)

(** A path on n vertices has at most n edges (degrees at most 2). *)
Lemma g241_path_edges (n : nat) : edge_count (ordinal_path n) <= n.
Proof.
rewrite -(leq_pmul2l (isT : 0 < 2)) /edge_count edges_sum_degrees.
apply: (@leq_trans (\sum_(x in ordinal_path n) 2)).
  by apply: leq_sum => i _; exact: ordinal_path_degree.
by rewrite sum_nat_const card_ordinal_path mulnC.
Qed.

Definition g241_good_hyp_claim : Prop :=
  [/\ connected [set: 'K_1], edge_count 'K_1 <= 1 * #|'K_1|, xe1_graph_ramsey_number 'K_3 'K_1 1 &
      (triangle_goodness_sparse_connected_statement -> exists n0 : nat,
         forall (G : sgraph) (R : nat), n0 <= #|G| -> connected [set: G] -> edge_count G <= 1 * #|G| ->
           xe1_graph_ramsey_number 'K_3 G R -> R + 1 = 2 * #|G|)].

Theorem g241_good_hyp_inhabited : g241_good_hyp_claim.
Proof.
split; [exact: g241_K1_connected | by rewrite (proj2 edge_count_K0_K1) | | by move=> h; exact: h 1].
by apply: g240_ramsey_K1; rewrite card_ord.
Qed.

(** Contract form: without the Ramsey hypothesis, R = 0 on a long path (connected, at most n edges) breaks
    R + 1 = 2n. *)
Definition g241_good_no_ramsey : Prop :=
  forall M : nat, exists n0 : nat,
    forall (G : sgraph) (R : nat), n0 <= #|G| -> connected [set: G] -> edge_count G <= M * #|G| ->
      R + 1 = 2 * #|G|.

Definition g241_good_ntt_claim : Prop :=
  ~ g241_good_no_ramsey /\ (g241_good_no_ramsey -> triangle_goodness_sparse_connected_statement).

Theorem g241_good_not_trivially_true : g241_good_ntt_claim.
Proof.
split.
- move=> h; have [n0 hn] := h 1.
  have e1 : edge_count (ordinal_path n0) <= 1 * #|ordinal_path n0|.
    by rewrite mul1n card_ordinal_path; exact: g241_path_edges.
  have n0le : n0 <= #|ordinal_path n0| by rewrite card_ordinal_path.
  have cn : connected [set: ordinal_path n0] by apply: ordinal_path_connected.
  have := hn (ordinal_path n0) 0 n0le cn e1.
  by move/(congr1 odd); rewrite /= oddM.
- by move=> h M; have [n0 hn] := h M; exists n0 => G R nG cG eG _; exact: hn.
Qed.

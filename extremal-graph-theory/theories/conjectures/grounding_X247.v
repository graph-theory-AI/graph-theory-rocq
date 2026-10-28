(** * Extremal.conjectures.grounding_X247 -- grounding certificates of wave X247.

    For each of the three rows: hyp_inhabited (the hypotheses hold on a concrete instance, and the statement then
    yields its conclusion there) and not_trivially_true in the contract form of meta/EXPANSION_PLAN.md 4.4 (the row
    with a load-bearing hypothesis dropped is false, and that variant implies the row): the edge guard
    #|G|^2 < 4 e(G) for erdos:1033 (the edgeless graph compl 'K_n0 has no triangle), the hypothesis "more edges than
    every C_4-free graph" for erdos:60 ('K_1 has no 4-edge set, so the family is empty and 1 <= 0 fails) and
    "min_degree G d" for erdos:612 (at r = 2, d = 8 the path P_(2C+2) is connected, K_4-free and has its ends at
    distance 2C + 1, so 56 (2C + 1) <= 16 (2C + 2) + 56 C fails).  The wave has no local helper, so no helper_sanity
    certificate.  Instances: the complete graphs K_n, n >= 3, meet the edge guard of erdos:1033 (2 C(n,2) = n (n - 1));
    'K_4 has more edges than every C_4-free graph on 4 vertices (6 edges on 4 vertices force K_4, which contains C_4);
    'K_5,5 is connected, of minimum degree exactly 5 and K_5-free (every cycle of 'K_n,m is even), the odd-clique part
    of erdos:612 at r = 2, d = 5. *)

From Extremal.conjectures Require Import X247.
From GTBase Require Import base common graph_metric path_graphs.
From mathcomp Require Import zify.
From Stdlib Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** n^2 < 4 * C(n, 2) for n >= 3: complete graphs meet the edge guard. *)
Lemma g247_Kn_guard (n : nat) : 3 <= n -> #|'K_n| ^ 2 < 4 * edge_count 'K_n.
Proof.
move=> n3; rewrite card_ord edge_count_Kn.
have h : 2 * 'C(n, 2) = n * n.-1.
  case: n n3 => [//|m] _; rewrite binS bin1 /=; elim: m => [//|m IH]; rewrite binS bin1 mulnDr IH; nia.
nia.
Qed.

Definition g247_tri_hyp_claim : Prop :=
  [/\ #|'K_3| ^ 2 < 4 * edge_count 'K_3 &
      (triangle_degree_sum_above_quarter_statement ->
         exists n0 : nat, forall n : nat, n0 <= n -> 3 <= n ->
           exists (x y z : 'K_n), [/\ x -- y, y -- z, x -- z &
             12 * #|'K_n| ^ 2 <= (#|N(x)| + #|N(y)| + #|N(z)| + #|'K_n| + 2 * #|'K_n|) ^ 2])].

Theorem g247_tri_hyp_inhabited : g247_tri_hyp_claim.
Proof.
split; first exact: g247_Kn_guard.
move=> h; have [n0 hn0] := h 1 isT; exists n0 => n n0n n3.
have cn : n0 <= #|'K_n| by rewrite card_ord.
have [x [y [z [xy yz xz hb]]]] := hn0 'K_n cn (g247_Kn_guard n3).
by exists x, y, z; split => //; move: hb; rewrite !exp1n !mul1n !muln1.
Qed.

Definition g247_tri_no_guard : Prop :=
  forall q : nat, 1 <= q -> exists n0 : nat,
    forall G : sgraph, n0 <= #|G| ->
      exists x y z : G, [/\ x -- y, y -- z, x -- z &
        12 * q ^ 2 * #|G| ^ 2 <= (q * (#|N(x)| + #|N(y)| + #|N(z)|) + #|G| + 2 * q * #|G|) ^ 2].

Definition g247_tri_ntt_claim : Prop :=
  ~ g247_tri_no_guard /\ (g247_tri_no_guard -> triangle_degree_sum_above_quarter_statement).

Theorem g247_tri_not_trivially_true : g247_tri_ntt_claim.
Proof.
split; last by move=> h q q1; have [n0 hn0] := h q q1; exists n0 => G nG _; exact: hn0.
move=> h; have [n0 hn0] := h 1 isT.
have cn : n0 <= #|compl 'K_n0| by rewrite card_ord.
have [x [y [z [xy _ _ _]]]] := hn0 (compl 'K_n0) cn.
by move: xy; rewrite (negbTE (compl_Kn_edgeless x y)).
Qed.

(** A graph with 'C(n, 2) edges on n vertices is complete. *)
Lemma g247_complete_of_count (H : sgraph) : 'C(#|H|, 2) <= edge_count H -> forall x y : H, x != y -> x -- y.
Proof.
move=> hc x y xy.
have sub : E(H) \subset [set A : {set H} | #|A| == 2].
  apply/subsetP => e; rewrite sg_edge_setE !inE => /existsP [u /existsP [v /andP [uv /eqP ->]]].
  by rewrite cards2 (sg_edgeNeq uv).
have eqE : E(H) = [set A : {set H} | #|A| == 2].
  by apply/eqP; rewrite eqEcard sub /= card_draws.
have : [set x; y] \in E(H) by rewrite eqE inE cards2 xy.
by rewrite in_edges.
Qed.

(** A graph on 4 vertices with 6 edges contains C_4. *)
Lemma g247_C4_of_count (H : sgraph) : #|H| = 4 -> 6 <= edge_count H -> has_subgraph H (cycle_graph 4).
Proof.
move=> e h6.
have cH : forall x y : H, x != y -> x -- y by apply: g247_complete_of_count; rewrite e.
pose f (i : cycle_graph 4) : H := enum_val (cast_ord (esym e) i).
have fi : injective f by move=> i j /enum_val_inj /cast_ord_inj.
apply/has_subgraphP; exists f; split => // i j ij.
by apply: cH; rewrite (inj_eq fi) (sg_edgeNeq ij).
Qed.

Definition g247_c4_hyp_claim : Prop :=
  [/\ (forall H : sgraph, #|H| = #|'K_4| -> ~ has_subgraph H (cycle_graph 4) -> edge_count H < edge_count 'K_4) &
      (c4_copies_above_ex_statement ->
         exists c : nat, exists Fs : {set {set {set 'K_4}}},
           (forall F : {set {set 'K_4}}, F \in Fs ->
              [/\ F \subset E('K_4), #|F| = 4 & has_subgraph (del_edge_set 'K_4 (E('K_4) :\: F)) (cycle_graph 4)]) /\
           #|'K_4| <= (c * #|Fs|) ^ 2)].

Lemma g247_K4_beats_C4_free (H : sgraph) :
  #|H| = #|'K_4| -> ~ has_subgraph H (cycle_graph 4) -> edge_count H < edge_count 'K_4.
Proof.
rewrite card_ord edge_count_Kn => e nC; rewrite ltnNge; apply/negP => h6.
by apply: nC; apply: g247_C4_of_count.
Qed.

Theorem g247_c4_hyp_inhabited : g247_c4_hyp_claim.
Proof.
split; first exact: g247_K4_beats_C4_free.
move=> [c [_ hc]]; have [Fs [hF hs]] := hc 'K_4 g247_K4_beats_C4_free.
by exists c, Fs.
Qed.

Definition g247_c4_no_edges : Prop :=
  exists c : nat, 1 <= c /\
    forall G : sgraph,
      exists Fs : {set {set {set G}}},
        (forall F : {set {set G}}, F \in Fs ->
           [/\ F \subset E(G), #|F| = 4 & has_subgraph (del_edge_set G (E(G) :\: F)) (cycle_graph 4)]) /\
        #|G| <= (c * #|Fs|) ^ 2.

Definition g247_c4_ntt_claim : Prop :=
  ~ g247_c4_no_edges /\ (g247_c4_no_edges -> c4_copies_above_ex_statement).

Theorem g247_c4_not_trivially_true : g247_c4_ntt_claim.
Proof.
split; last by move=> [c [c1 hc]]; exists c; split => // G _; exact: hc.
move=> [c [_ hc]]; have [Fs [hF hs]] := hc 'K_1.
have F0 : Fs = set0.
  apply/eqP; rewrite -subset0; apply/subsetP => F FFs.
  have [FE F4 _] := hF F FFs.
  have := subset_leq_card FE; rewrite F4 -/(edge_count 'K_1) (proj2 edge_count_K0_K1) //.
by move: hs; rewrite F0 cards0 muln0 card_ord.
Qed.

(** The path P_n is connected. *)
Lemma g247_path_connected (n : nat) : connected [set: ordinal_path n].
Proof.
apply: connectedTI.
have up : forall (i k : nat) (hi : i < n) (hk : i + k < n), connect (--) (Ordinal hi : ordinal_path n) (Ordinal hk).
  move=> i k; elim: k => [|k IH] hi hk.
    have -> : Ordinal hk = Ordinal hi :> ordinal_path n by apply: val_inj; rewrite /= addn0.
    exact: connect0.
  have hk' : i + k < n by apply: ltnW; rewrite -addnS.
  apply: (@connect_trans _ _ (Ordinal hk' : ordinal_path n)); first exact: IH.
  by apply: connect1; rewrite ordinal_path_edgeE /= addnS eqxx.
move=> x y; wlog le : x y / val x <= val y.
  move=> W; case: (leqP (val x) (val y)) => h; first exact: W.
  by rewrite (sconnect_sym x y); apply: W; exact: ltnW.
case: x y le => [i hi] [j hj] /= le.
have hk : i + (j - i) < n by rewrite (subnKC le).
have -> : Ordinal hj = Ordinal hk :> ordinal_path n by apply: val_inj; rewrite /= (subnKC le).
exact: up.
Qed.

(** The path P_n has no triangle, so no K_4. *)
Lemma g247_path_no_K4 (n : nat) : ~ has_subgraph (ordinal_path n) 'K_4.
Proof.
move=> /has_subgraphP [f [fi fh]].
have e01 := fh (Ordinal (isT : 0 < 4)) (Ordinal (isT : 1 < 4)) isT.
have e12 := fh (Ordinal (isT : 1 < 4)) (Ordinal (isT : 2 < 4)) isT.
have e02 := fh (Ordinal (isT : 0 < 4)) (Ordinal (isT : 2 < 4)) isT.
rewrite ordinal_path_edgeE in e01; rewrite ordinal_path_edgeE in e12; rewrite ordinal_path_edgeE in e02.
move: e01 e12 e02 => /orP [] /eqP a /orP [] /eqP b /orP [] /eqP c; lia.
Qed.

(** In P_n a vertex within k steps of x has index at most x + k. *)
Lemma g247_path_ball (n : nat) (k : nat) (x y : ordinal_path n) : y \in rel_ball (--) k x -> val y <= val x + k.
Proof.
elim: k y => [|k IH] y /=.
  by rewrite inE => /eqP ->; rewrite addn0.
case/setUP => [/IH h | /bigcupP [z zb]]; first by rewrite addnS; apply: leqW.
rewrite inE ordinal_path_edgeE => /orP [] /eqP e; have := IH _ zb.
all: move=> h; rewrite /= in e h *; lia.
Qed.

Lemma g247_path_dist (n : nat) : n <= graph_dist (ord0 : ordinal_path n.+1) ord_max.
Proof.
rewrite /graph_dist; case: ex_minnP => m /orP [hb | /eqP ->] _; last by rewrite card_ordinal_path leqnSn.
by move/g247_path_ball: hb; rewrite /= add0n.
Qed.

(** 'K_5,5 has no triangle (every cycle of 'K_n,m is even), so no K_5. *)
Lemma g247_K55_no_K5 : ~ has_subgraph ('K_5,5) ('K_(2 * 2 + 1)).
Proof.
move=> /has_subgraphP [f [fi fh]].
have e01 := fh (Ordinal (isT : 0 < 5)) (Ordinal (isT : 1 < 5)) isT.
have e12 := fh (Ordinal (isT : 1 < 5)) (Ordinal (isT : 2 < 5)) isT.
have e20 := fh (Ordinal (isT : 2 < 5)) (Ordinal (isT : 0 < 5)) isT.
have cyc : cycle (--) [:: f (Ordinal (isT : 0 < 5)); f (Ordinal (isT : 1 < 5)); f (Ordinal (isT : 2 < 5))].
  by rewrite /= e01 e12 e20.
by have := even_cycle_Knm cyc.
Qed.

(** 'K_5,5 has minimum degree exactly 5. *)
Lemma g247_K55_min_degree : min_degree ('K_5,5) 5.
Proof. by split; [exact: (@min_degree_at_least_Knm 5 5) | exists (inl ord0); exact: deg_Knm_l]. Qed.

(** hyp_inhabited: the odd-clique part at r = 2 and d = 5 holds for 'K_5,5 (connected, minimum degree 5,
    K_5-free, 5 divides 5), and the statement then bounds its distances. *)
Definition g247_diam_hyp_claim : Prop :=
  [/\ connected [set: ('K_5,5)], min_degree ('K_5,5) 5, ~ has_subgraph ('K_5,5) ('K_(2 * 2 + 1)), (3 * 2 - 1) %| 5 &
      (clique_free_diameter_min_degree_statement ->
         exists C : nat, forall x y : ('K_5,5),
           2 * 5 * graph_dist x y <= (3 * 2 - 1) * #|('K_5,5)| + C * 2 * 5)].

Theorem g247_diam_hyp_inhabited : g247_diam_hyp_claim.
Proof.
have conn : connected [set: ('K_5,5)] by exact: Knm_connected.
split => //; [exact: g247_K55_min_degree | exact: g247_K55_no_K5 |].
move=> h; have [C [_ hC]] := h 2 5 (leqnn 2) isT; exists C.
exact: (hC ('K_5,5) conn g247_K55_min_degree g247_K55_no_K5 (dvdnn 5)).
Qed.

(** not_trivially_true: without "min_degree G d" the even-clique part fails at r = 2, d = 8 on the path
    P_(2C+2) (connected, K_4-free, its ends at distance 2C + 1), and the variant implies the row. *)
Definition g247_diam_no_min_degree : Prop :=
  forall r d : nat, 2 <= r -> 2 <= d -> exists C : nat,
    (forall G : sgraph, connected [set: G] ->
       ~ has_subgraph G 'K_(2 * r) -> ((r - 1) * (3 * r + 2)) %| d ->
       forall x y : G,
         (2 * r ^ 2 - 1) * d * graph_dist x y <= 2 * (r - 1) * (3 * r + 2) * #|G| + C * (2 * r ^ 2 - 1) * d) /\
    (forall G : sgraph, connected [set: G] ->
       ~ has_subgraph G 'K_(2 * r + 1) -> (3 * r - 1) %| d ->
       forall x y : G, r * d * graph_dist x y <= (3 * r - 1) * #|G| + C * r * d).

Definition g247_diam_ntt_claim : Prop :=
  ~ g247_diam_no_min_degree /\ (g247_diam_no_min_degree -> clique_free_diameter_min_degree_statement).

Theorem g247_diam_not_trivially_true : g247_diam_ntt_claim.
Proof.
split; last first.
  move=> h r d r2 d2; have [C [h1 h2]] := h r d r2 d2; exists C; split.
  - by move=> G c _ k dv; exact: h1.
  - by move=> G c _ k dv; exact: h2.
move=> h; have [C [h1 _]] := h 2 8 (leqnn 2) isT.
have hb := h1 (ordinal_path (2 * C + 1).+1) (@g247_path_connected (2 * C + 1).+1) (@g247_path_no_K4 (2 * C + 1).+1) (dvdnn 8) ord0 ord_max.
have hd := @g247_path_dist (2 * C + 1).
rewrite card_ordinal_path (_ : 2 * 2 ^ 2 - 1 = 7) // in hb.
lia.
Qed.

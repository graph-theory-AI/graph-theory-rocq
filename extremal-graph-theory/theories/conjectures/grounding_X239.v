(** * Extremal.conjectures.grounding_X239 -- grounding certificates of wave X239.

    For each of the six rows: hyp_inhabited (the hypotheses hold on a concrete instance, and the
    statement then yields its conclusion there) and not_trivially_true in the contract form of
    meta/EXPANSION_PLAN.md 4.4 (the row with a load-bearing hypothesis dropped is false, and that
    variant implies the row): the edge-count hypothesis for erdos:86 (no C_4 without edges), the
    Ramsey hypotheses for erdos:554, the Turan hypothesis for erdos:573, "q <= p" for erdos:571 (at
    alpha = 0 no bipartite G has 1 <= ex(n; G) <= c eventually: a matching, a star or a one-edge
    embedding beats it), "n0 <= |G|" for erdos:82 (K_2) and "some member is bipartite" for erdos:575
    ({K_3}).  The wave has no local helper, so no helper_sanity certificate.  Small instances: Q_0,
    C_5, K_1, K_2, K_3, the perfect matching and the star on 'I_N. *)

From mathcomp Require Import fingroup perm.
From Extremal.foundations Require Import edge_colourings.
From Extremal.conjectures Require Import X195 D2tur X239.
(* GTBase last: its canonical [edge_count] must shadow D2tur's eta-alias of the same name. *)
From GTBase Require Import base common hypercubes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Small instances *)

Lemma g239_mono_copy_card (Host F : sgraph) (C : eqType) (col : {set Host} -> C) (c : C) :
  mono_copy F col c -> #|F| <= #|Host|.
Proof. by case=> emb [ei _ _]; exact: leq_card ei. Qed.

(** One colour: C_5 and K_3 are their own Ramsey numbers. *)
Lemma g239_C5_one_colour : x195_ramsey_number 1 (fun _ : 'I_1 => cycle_graph 5) 5.
Proof.
split.
- move=> col; exists ord0, ord0, (fun x : cycle_graph 5 => (x : 'K_5)); split => //.
  + by move=> x y; rewrite /edge_rel /= /cyc_rel => /andP [].
  + by move=> x y _; rewrite (ord1 (col _)).
- move=> m m5 h; have [i [c hc]] := h (fun _ => ord0).
  by have := g239_mono_copy_card hc; rewrite !card_ord leqNgt m5.
Qed.

Lemma g239_K3_one_colour : x195_ramsey_number 1 (fun _ : 'I_1 => 'K_3) 3.
Proof.
split.
- move=> col; exists ord0, ord0, id; split => //.
  by move=> x y _; rewrite (ord1 (col _)).
- move=> m m3 h; have [i [c hc]] := h (fun _ => ord0).
  by have := g239_mono_copy_card hc; rewrite !card_ord leqNgt m3.
Qed.

(** At most 'C(n, 2) edges on n vertices. *)
Lemma g239_edge_count_le (G : sgraph) (n : nat) : #|G| = n -> edge_count G <= 'C(n, 2).
Proof.
move=> e; rewrite -(edge_count_Kn n).
pose h (v : G) : 'K_n := cast_ord e (enum_rank v).
have hi : injective h by move=> x y /cast_ord_inj /enum_rank_inj.
apply: (@sub_card_edge G 'K_n h hi).
by move=> x y xy; rewrite /edge_rel /= (inj_eq hi) (sg_edgeNeq xy).
Qed.

(** ex(1; {C_3, C_4}) = 0. *)
Lemma g239_turan_C3C4_1 : is_turan_number 1 (fun i : 'I_2 => cycle_graph (i + 3)) 0.
Proof.
split.
- exists 'K_1; split; [by rewrite card_ord | by rewrite /D2tur.edge_count (proj2 edge_count_K0_K1) |].
  move=> i [h hi _]; have := leq_card h hi; rewrite !card_ord.
  by move/(leq_trans (leq_addl i 3)).
- by move=> m' [G [hG <- _]]; exact: g239_edge_count_le hG.
Qed.

(** A graph with every edge deleted has no C_4. *)
Lemma g239_no_edge_no_C4 (G : sgraph) : ~ has_subgraph (del_edge_set G E(G)) (cycle_graph 4).
Proof.
case/has_subgraphP => f [_ fh].
have e01 : (ord0 : cycle_graph 4) -- (Ordinal (isT : 1 < 4)) by [].
have := fh _ _ e01; rewrite del_edge_setE => /andP [xy]; apply/negP; rewrite negbK.
by apply/(@edgesP G); exists (f ord0), (f (Ordinal (isT : 1 < 4))).
Qed.

Lemma g239_K2_bipartite : bipartite 'K_2.
Proof.
exists (fun x : 'K_2 => x == ord0) => x y.
by case: x => [[|[|x]] hx] //; case: y => [[|[|y]] hy].
Qed.

Lemma g239_K3_not_bipartite : ~ bipartite 'K_3.
Proof.
case=> f hf.
have h01 := hf ord0 (Ordinal (isT : 1 < 3)) isT.
have h12 := hf (Ordinal (isT : 1 < 3)) (Ordinal (isT : 2 < 3)) isT.
have h02 := hf ord0 (Ordinal (isT : 2 < 3)) isT.
by move: h01 h12 h02; case: (f ord0); case: (f (Ordinal _)); case: (f (Ordinal _)).
Qed.

Lemma g239_trunc_log_2 : trunc_log 2 2 = 1.
Proof. by []. Qed.

(** ** Row erdos:86 *)

(** At q = 1 the edge hypothesis holds only at n = 0 (|F| <= n 2^(n-1) < (3/2) n 2^(n-1) for n >= 1),
    so the instance is the degenerate Q_0; an every-n instance (q = 2, F = E(Q_n)) would need
    |E(Q_n)| = n 2^(n-1), which GTBase.hypercubes does not provide (Arthur, A3 (144)). *)
Definition g239_cube_hyp_claim : Prop :=
  [/\ (set0 : {set {set product_hypercube 0}}) \subset E(product_hypercube 0),
      (1 + 2) * (0 * 2 ^ 0) <= 4 * 1 * #|(set0 : {set {set product_hypercube 0}})| &
      (hypercube_dense_subgraph_C4_statement -> exists n0 : nat,
         forall (n : nat) (F : {set {set product_hypercube n}}), n0 <= n -> F \subset E(product_hypercube n) ->
           (1 + 2) * (n * 2 ^ n) <= 4 * 1 * #|F| ->
           has_subgraph (del_edge_set (product_hypercube n) (E(product_hypercube n) :\: F)) (cycle_graph 4))].

Theorem g239_cube_hyp_inhabited : g239_cube_hyp_claim.
Proof. by split; [exact: sub0set | rewrite cards0 | move=> h; exact: h 1 (leqnn 1)]. Qed.

(** Contract form: without the edge-count hypothesis, F = set0 leaves no edge, so no C_4. *)
Definition g239_cube_no_density : Prop :=
  forall q : nat, 1 <= q -> exists n0 : nat,
    forall (n : nat) (F : {set {set product_hypercube n}}), n0 <= n -> F \subset E(product_hypercube n) ->
      has_subgraph (del_edge_set (product_hypercube n) (E(product_hypercube n) :\: F)) (cycle_graph 4).

Definition g239_cube_ntt_claim : Prop :=
  ~ g239_cube_no_density /\ (g239_cube_no_density -> hypercube_dense_subgraph_C4_statement).

Theorem g239_cube_not_trivially_true : g239_cube_ntt_claim.
Proof.
split.
- move=> h; have [n0 hn] := h 1 (leqnn 1).
  have := hn n0 set0 (leqnn n0) (sub0set _); rewrite setD0.
  exact: g239_no_edge_no_C4.
- by move=> h q q1; have [n0 hn] := h q q1; exists n0 => n F nn FE _; exact: hn.
Qed.

(** ** Row erdos:554 *)

Definition g239_odd_hyp_claim : Prop :=
  [/\ x195_ramsey_number 1 (fun _ : 'I_1 => cycle_graph (2 * 2 + 1)) 5,
      x195_ramsey_number 1 (fun _ : 'I_1 => 'K_3) 3 &
      (odd_cycle_triangle_ramsey_ratio_statement -> exists k0 : nat, forall k R1 R3 : nat, k0 <= k ->
         x195_ramsey_number k (fun _ : 'I_1 => cycle_graph (2 * 2 + 1)) R1 ->
         x195_ramsey_number k (fun _ : 'I_1 => 'K_3) R3 -> 1 * R1 <= R3)].

Theorem g239_odd_hyp_inhabited : g239_odd_hyp_claim.
Proof.
split; [exact: g239_C5_one_colour | exact: g239_K3_one_colour |].
by move=> h; exact: h 2 (leqnn 2) 1 (leqnn 1).
Qed.

(** Contract form: without the two Ramsey hypotheses, R1 = 1 and R3 = 0. *)
Definition g239_odd_no_ramsey : Prop :=
  forall n : nat, 2 <= n -> forall q : nat, 1 <= q ->
    exists k0 : nat, forall k R1 R3 : nat, k0 <= k -> q * R1 <= R3.

Definition g239_odd_ntt_claim : Prop :=
  ~ g239_odd_no_ramsey /\ (g239_odd_no_ramsey -> odd_cycle_triangle_ramsey_ratio_statement).

Theorem g239_odd_not_trivially_true : g239_odd_ntt_claim.
Proof.
split.
- by move=> h; have [k0 hk] := h 2 (leqnn 2) 1 (leqnn 1); have := hk k0 1 0 (leqnn k0).
- by move=> h n n2 q q1; have [k0 hk] := h n n2 q q1; exists k0 => k R1 R3 kk _ _; exact: hk.
Qed.

(** ** Row erdos:573 *)

Definition g239_c3c4_hyp_claim : Prop :=
  is_turan_number 1 (fun i : 'I_2 => cycle_graph (i + 3)) 0 /\
  (triangle_square_free_turan_asymptotic_statement -> exists n0 : nat, forall n m : nat, n0 <= n ->
     is_turan_number n (fun i : 'I_2 => cycle_graph (i + 3)) m ->
     1 ^ 2 * n ^ 3 <= 8 * (1 + 1) ^ 2 * m ^ 2 /\ 8 * 1 ^ 2 * m ^ 2 <= (1 + 1) ^ 2 * n ^ 3).

Theorem g239_c3c4_hyp_inhabited : g239_c3c4_hyp_claim.
Proof. by split; [exact: g239_turan_C3C4_1 | move=> h; exact: h 1 (leqnn 1)]. Qed.

(** Contract form: without the Turan hypothesis, m = 0 at n = n0 + 1. *)
Definition g239_c3c4_no_turan : Prop :=
  forall q : nat, 1 <= q -> exists n0 : nat, forall n m : nat, n0 <= n ->
    q ^ 2 * n ^ 3 <= 8 * (q + 1) ^ 2 * m ^ 2 /\ 8 * q ^ 2 * m ^ 2 <= (q + 1) ^ 2 * n ^ 3.

Definition g239_c3c4_ntt_claim : Prop :=
  ~ g239_c3c4_no_turan /\ (g239_c3c4_no_turan -> triangle_square_free_turan_asymptotic_statement).

Theorem g239_c3c4_not_trivially_true : g239_c3c4_ntt_claim.
Proof.
split.
- move=> h; have [n0 hn] := h 1 (leqnn 1); have [+ _] := hn n0.+1 0 (leqnSn n0).
  by rewrite exp1n mul1n exp0n // muln0 leqn0 expn_eq0.
- by move=> h q q1; have [n0 hn] := h q q1; exists n0 => n m nn _; exact: hn.
Qed.

(** ** Row erdos:82 *)

Definition g239_reg_hyp_claim : Prop :=
  (forall n0 : nat, exists G : sgraph, n0 <= #|G|) /\
  (regular_induced_subgraph_superlogarithmic_statement -> exists n0 : nat, forall G : sgraph, n0 <= #|G| ->
     exists S : {set G}, (exists d : nat, regular (induced S) d) /\ 1 * trunc_log 2 #|G| <= #|S|).

Theorem g239_reg_hyp_inhabited : g239_reg_hyp_claim.
Proof. by split; [move=> n0; exists 'K_n0; rewrite card_ord | move=> h; exact: h 1]. Qed.

(** Contract form: without "n0 <= |G|", K_2 has |S| <= 2 < 3 * trunc_log 2 2. *)
Definition g239_reg_no_size : Prop :=
  forall M : nat, exists n0 : nat, forall G : sgraph,
    exists S : {set G}, (exists d : nat, regular (induced S) d) /\ M * trunc_log 2 #|G| <= #|S|.

Definition g239_reg_ntt_claim : Prop :=
  ~ g239_reg_no_size /\ (g239_reg_no_size -> regular_induced_subgraph_superlogarithmic_statement).

Theorem g239_reg_not_trivially_true : g239_reg_ntt_claim.
Proof.
split.
- move=> h; have [_ hn] := h 3; have [S [_ hS]] := hn 'K_2.
  move: hS; rewrite card_ord g239_trunc_log_2 muln1 => hS.
  by have := leq_trans hS (max_card S); rewrite card_ord.
- by move=> h M; have [n0 hn] := h M; exists n0 => G _; exact: hn.
Qed.

(** ** Row erdos:575 *)

Definition g239_compact_hyp_claim : Prop :=
  bipartite 'K_2 /\
  (bipartite_turan_compactness_statement -> exists (i : 'I_1) (C N : nat), bipartite 'K_2 /\
     forall n m1 m : nat, N <= n -> is_turan_number n (fun _ : 'I_1 => 'K_2) m1 ->
       is_turan_number n (fun _ : 'I_1 => 'K_2) m -> m1 <= C * m).

Theorem g239_compact_hyp_inhabited : g239_compact_hyp_claim.
Proof.
split; first exact: g239_K2_bipartite.
by move=> h; exact: h 1 (fun _ => 'K_2) (ex_intro _ ord0 g239_K2_bipartite).
Qed.

(** Contract form: without "some member is bipartite", the family {K_3} fails. *)
Definition g239_compact_no_bipartite : Prop :=
  forall (k : nat) (Fam : 'I_k -> sgraph),
    exists (i : 'I_k) (C N : nat), bipartite (Fam i) /\
      forall n m1 m : nat, N <= n ->
        is_turan_number n (fun _ : 'I_1 => Fam i) m1 -> is_turan_number n Fam m -> m1 <= C * m.

Definition g239_compact_ntt_claim : Prop :=
  ~ g239_compact_no_bipartite /\ (g239_compact_no_bipartite -> bipartite_turan_compactness_statement).

Theorem g239_compact_not_trivially_true : g239_compact_ntt_claim.
Proof.
split.
- by move=> h; have [i [C [N [hb _]]]] := h 1 (fun _ => 'K_3); exact: g239_K3_not_bipartite hb.
- by move=> h k Fam _; exact: h k Fam.
Qed.

(** ** Row erdos:571 (hyp_inhabited) *)

Definition g239_exp_hyp_claim : Prop :=
  [/\ 1 <= 1, 1 <= 1, 1 < 2 * 1 &
      (rational_turan_exponent_statement -> exists G : sgraph, bipartite G /\ exists c n0 : nat, 1 <= c /\
         forall n : nat, n0 <= n -> exists m : nat,
           [/\ is_turan_number n (fun _ : 'I_1 => G) m, n ^ 1 <= (c * m) ^ 1 & m ^ 1 <= c ^ 1 * n ^ 1])].

Theorem g239_exp_hyp_inhabited : g239_exp_hyp_claim.
Proof. by split => // h; exact: h 1 1 (leqnn 1) (leqnn 1) isT. Qed.

(** ** Row erdos:571: two G-free hosts with many edges *)

(** The perfect matching on 'I_N (2i ~ 2i+1) and the star on 'I_N (centre 0). *)
Definition g239_matching (N : nat) : sgraph := fg_mk_sgraph (fun a b : 'I_N => a./2 == b./2).
Definition g239_star (N : nat) : sgraph := fg_mk_sgraph (fun a b : 'I_N => val a == 0).

(** Three distinct numbers never share their half. *)
Lemma g239_half3 (a b c : nat) : a != b -> b != c -> a != c -> a./2 = b./2 -> a./2 = c./2 -> False.
Proof.
move=> ab bc ac hab hac.
move: ab bc ac; rewrite -(odd_double_half a) -(odd_double_half b) -(odd_double_half c) -hab -hac.
rewrite !eqn_add2r.
by case: (odd a); case: (odd b); case: (odd c).
Qed.

(** A vertex with two distinct neighbours does not embed in the matching. *)
Lemma g239_matching_free (G : sgraph) (N : nat) (v x y : G) :
  v -- x -> v -- y -> x != y -> ~ subgraph G (g239_matching N).
Proof.
move=> vx vy xy hs; have : has_subgraph (g239_matching N) G := hs.
case/has_subgraphP => f [fi fh].
have := fh _ _ vx; have := fh _ _ vy; rewrite /edge_rel /= /fg_srel.
case/andP => ny /orP hy; case/andP => nx /orP hx.
have nxy : f x != f y by rewrite (inj_eq fi).
apply: (@g239_half3 (f v) (f x) (f y)) => //.
- by case: hx => /eqP.
- by case: hy => /eqP.
Qed.

(** Two disjoint edges do not embed in the star. *)
Lemma g239_star_free (G : sgraph) (N : nat) (x y u w : G) :
  x -- y -> u -- w -> x != u -> x != w -> y != u -> y != w -> ~ subgraph G (g239_star N).
Proof.
move=> xy uw xu xw yu yw hs; have : has_subgraph (g239_star N) G := hs.
case/has_subgraphP => f [fi fh].
have := fh _ _ xy; have := fh _ _ uw; rewrite /edge_rel /= /fg_srel.
case/andP => _ huw; case/andP => _ hxy.
have z (p q : G) : val (f p) == 0 -> val (f q) == 0 -> p = q.
  by move=> /eqP hp /eqP hq; apply: fi; apply: val_inj; rewrite hp hq.
case/orP: hxy => hx; case/orP: huw => hu.
- by move: xu; rewrite (z _ _ hx hu) eqxx.
- by move: xw; rewrite (z _ _ hx hu) eqxx.
- by move: yu; rewrite (z _ _ hx hu) eqxx.
- by move: yw; rewrite (z _ _ hx hu) eqxx.
Qed.

(** Edge counts: k disjoint pairs {2i, 2i+1} in the matching, k spokes {0, i+1} in the star. *)
Lemma g239_matching_edges (N k : nat) : 2 * k <= N -> k <= #|E(g239_matching N)|.
Proof.
move=> kN.
have lt1 (i : 'I_k) : (2 * i).+1 < N.
  apply: leq_trans kN; have h : 2 * i.+1 <= 2 * k by rewrite leq_mul2l ltn_ord orbT.
  by rewrite mulnS add2n in h.
pose e (i : 'I_k) : {set g239_matching N} := [set Ordinal (ltnW (lt1 i)); Ordinal (lt1 i)].
have eE (i : 'I_k) : e i \in E(g239_matching N).
  apply/(@edgesP (g239_matching N)); exists (Ordinal (ltnW (lt1 i))), (Ordinal (lt1 i)); split=> //.
  rewrite /edge_rel /= /fg_srel; apply/andP; split; first by rewrite -(inj_eq val_inj) /= neq_ltn ltnSn.
  by apply/orP; left; rewrite /= mul2n doubleK uphalf_double.
have ei : injective e.
  move=> i j eij; have : Ordinal (ltnW (lt1 i)) \in e j by rewrite -eij !inE eqxx.
  rewrite !inE; case/orP => /eqP [] h; apply: val_inj.
  - by move/eqP: h; rewrite eqn_mul2l /= => /eqP.
  - by move: (congr1 odd h); rewrite /= !mul2n !odd_double.
have := subset_leq_card (_ : [set e i | i : 'I_k] \subset E(g239_matching N)).
rewrite card_imset // card_ord; apply.
by apply/subsetP => x /imsetP [i _ ->].
Qed.

Lemma g239_star_edges (N k : nat) : k < N -> k <= #|E(g239_star N)|.
Proof.
move=> kN; have N0 : 0 < N by apply: leq_ltn_trans kN.
have lt1 (i : 'I_k) : i.+1 < N by apply: leq_ltn_trans kN.
pose e (i : 'I_k) : {set g239_star N} := [set Ordinal N0; Ordinal (lt1 i)].
have eE (i : 'I_k) : e i \in E(g239_star N).
  by apply/(@edgesP (g239_star N)); exists (Ordinal N0), (Ordinal (lt1 i)); split=> //.
have ei : injective e.
  move=> i j eij; have : Ordinal (lt1 i) \in e j by rewrite -eij !inE eqxx orbT.
  by rewrite !inE; case/orP => /eqP [] // h; exact: val_inj.
have := subset_leq_card (_ : [set e i | i : 'I_k] \subset E(g239_star N)).
rewrite card_imset // card_ord; apply.
by apply/subsetP => x /imsetP [i _ ->].
Qed.

(** Embeddings into a host with enough vertices: an edgeless G, and a G whose only edge is xy. *)
Lemma g239_inj (G H : sgraph) : #|G| <= #|H| -> exists g : G -> H, injective g.
Proof.
move=> le; exists (fun x => enum_val (widen_ord le (enum_rank x))).
by move=> x y /enum_val_inj /(congr1 val) /= /val_inj /enum_rank_inj.
Qed.

Lemma g239_edgeless_embeds (G H : sgraph) :
  (forall x y : G, ~~ (x -- y)) -> #|G| <= #|H| -> subgraph G H.
Proof.
move=> e0 le; have [g gi] := g239_inj le.
have : has_subgraph H G by apply/has_subgraphP; exists g; split=> // x y; rewrite (negbTE (e0 x y)).
by [].
Qed.

Lemma g239_one_edge_embeds (G H : sgraph) (x y : G) (a b : H) :
  x -- y -> (forall u w : G, u -- w -> (u == x) && (w == y) || (u == y) && (w == x)) ->
  a -- b -> #|G| <= #|H| -> subgraph G H.
Proof.
move=> xy only ab le; have [g gi] := g239_inj le.
pose s1 : {perm H} := tperm (g x) a.
pose s2 : {perm H} := tperm (s1 (g y)) b.
pose f (v : G) : H := s2 (s1 (g v)).
have fi : injective f by move=> u w /perm_inj /perm_inj /gi.
have s1x : s1 (g x) = a by rewrite /s1 tpermL.
have s1y : s1 (g y) != a.
  by rewrite -s1x (inj_eq (@perm_inj _ s1)) (inj_eq gi) eq_sym (sg_edgeNeq xy).
have fx : f x = a by rewrite /f s1x /s2 tpermD // eq_sym (sg_edgeNeq ab).
have fy : f y = b by rewrite /f /s2 tpermL.
have : has_subgraph H G.
  apply/has_subgraphP; exists f; split=> // u w /only /orP [] /andP [/eqP -> /eqP ->].
  - by rewrite fx fy.
  - by rewrite fx fy sg_sym.
by [].
Qed.

(** ** Row erdos:571 (not_trivially_true) *)

(** Contract form: without "q <= p" (alpha >= 1), alpha = 0 asks for a bipartite G with
    1 <= ex(n; G) <= c eventually.  No G does: a vertex with two distinct neighbours misses the
    matching (floor(n/2) edges), two disjoint edges miss the star (n - 1 edges), and a G with at
    most one edge embeds in every G-free host with an edge (or in every host, if edgeless). *)
Definition g239_exp_no_lower : Prop :=
  forall p q : nat, 1 <= q -> p < 2 * q ->
    exists G : sgraph, bipartite G /\ exists c n0 : nat, 1 <= c /\
      forall n : nat, n0 <= n -> exists m : nat,
        [/\ is_turan_number n (fun _ : 'I_1 => G) m, n ^ p <= (c * m) ^ q & m ^ q <= c ^ q * n ^ p].

Lemma g239_exp_no_lower_false : ~ g239_exp_no_lower.
Proof.
move=> h; have [G [_ [c [n0 [c1 hn]]]]] := h 0 1 (leqnn 1) isT.
pose N := n0 + #|G| + (2 * c).+2.
have n0N : n0 <= N by rewrite /N -addnA leq_addr.
have GN : #|G| <= N by rewrite /N (leq_trans (leq_addl n0 _)) // leq_addr.
have [m [[[H0 [cH0 eH0 fH0]] mx] lo hi]] := hn N n0N.
rewrite expn0 expn1 in lo; rewrite expn1 expn1 expn0 muln1 in hi.
have m0 : 0 < m by move: lo; rewrite muln_gt0 => /andP [].
have bound (H : sgraph) : #|H| = N -> ~ subgraph G H -> #|E(H)| <= m.
  by move=> cH fH; apply: mx; exists H; split => // i; exact: fH.
have big (k : nat) : c < k -> k <= m -> False.
  by move=> ck km; move: (leq_ltn_trans hi (leq_trans ck km)); rewrite ltnn.
case: (boolP [exists v : G, exists x : G, exists y : G, [&& v -- x, v -- y & x != y]]) => [|/existsPn A].
  case/existsP => v /existsP [x /existsP [y /and3P [vx vy xy]]].
  have hN : 2 * c.+1 <= N by rewrite /N mulnS add2n leq_addl.
  apply: (big c.+1 (ltnSn c)); apply: leq_trans (g239_matching_edges hN) _.
  by apply: bound; [rewrite card_ord | exact: g239_matching_free vx vy xy].
have deg1 (v x y : G) : v -- x -> v -- y -> x = y.
  move=> vx vy; apply/eqP; apply/negPn/negP => nxy.
  by move: (A v) => /existsPn /(_ x) /existsPn /(_ y); rewrite vx vy nxy.
case: (boolP [exists x : G, exists y : G, exists u : G, exists w : G,
               [&& x -- y, u -- w, x != u, x != w, y != u & y != w]]) => [|/existsPn B].
  case/existsP => x /existsP [y /existsP [u /existsP [w /and5P [xy uw xu xw /andP [yu yw]]]]].
  have hN : c.+1 < N.
    by apply: leq_trans (leq_addl (n0 + #|G|) _); rewrite !ltnS leq_pmull.
  apply: (big c.+1 (ltnSn c)); apply: leq_trans (g239_star_edges hN) _.
  by apply: bound; [rewrite card_ord | exact: g239_star_free xy uw xu xw yu yw].
case: (boolP [exists x : G, exists y : G, x -- y]) => [|/existsPn C].
  case/existsP => x /existsP [y xy].
  have only (u w : G) : u -- w -> (u == x) && (w == y) || (u == y) && (w == x).
    move=> uw; move: (B x) => /existsPn /(_ y) /existsPn /(_ u) /existsPn /(_ w).
    rewrite xy uw /=.
    case: (eqVneq x u) => [ex _ | xu].
      by rewrite -ex in uw; rewrite (deg1 x w y uw xy) eqxx.
    case: (eqVneq x w) => [ew _ | xw].
      by rewrite -ew sg_sym in uw; rewrite (deg1 x u y uw xy) eqxx.
    case: (eqVneq y u) => [eu _ | yu].
      rewrite -eu in uw; have yx : y -- x by rewrite sg_sym.
      by move: xw; rewrite (deg1 y w x uw yx) eqxx.
    rewrite /= negbK => /eqP yw; rewrite -yw in uw.
    have yu' : y -- u by rewrite sg_sym.
    have yx : y -- x by rewrite sg_sym.
    by move: xu; rewrite (deg1 y u x yu' yx) eqxx.
  have : 0 < #|E(H0)| by rewrite -eH0 in m0.
  rewrite card_gt0 => /set0Pn [e /(@edgesP H0) [a [b [_ ab]]]].
  by apply: (fH0 ord0); apply: (g239_one_edge_embeds xy only ab); rewrite cH0.
apply: (fH0 ord0); apply: g239_edgeless_embeds; last by rewrite cH0.
by move=> x y; move: (C x) => /existsPn /(_ y).
Qed.

Definition g239_exp_ntt_claim : Prop :=
  ~ g239_exp_no_lower /\ (g239_exp_no_lower -> rational_turan_exponent_statement).

Theorem g239_exp_not_trivially_true : g239_exp_ntt_claim.
Proof.
split; first exact: g239_exp_no_lower_false.
by move=> h p q q1 _ pq; exact: h p q q1 pq.
Qed.

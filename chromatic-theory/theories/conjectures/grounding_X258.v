(** * Chromatic.conjectures.grounding_X258 -- grounding certificates of wave X258.

    For each of the four rows: hyp_inhabited (the hypotheses hold on a concrete instance, with a concrete value of
    every relational number, and the statement then yields its conclusion there) and not_trivially_true in the
    contract form of meta/EXPANSION_PLAN.md 4.4 (a variant obtained from the body by deleting one hypothesis is false
    and implies the row): each row without its relational hypothesis (erdos:921: f = 0 against n <= A f^2 at k = 4;
    erdos:1013 without both order hypotheses: a = 0, b = 1 at q = 1; erdos:917's first clause: f = 0 against
    n^2 <= C f at k = 4; erdos:744's first clause: m = 0 against M = 1).  The concrete values are f_4(4) = 2 for
    erdos:921 and f_4(4) = 6 for erdos:917 (K_4: a graph whose chromatic number is its order is complete,
    g258_adj_of_chi), h_3(1) = 1 and h_3(2) = 2 (K_1, K_2) and f_4(4) = 2 for erdos:744 (K_4 minus a perfect matching
    is a 4-cycle; one deletion leaves a triangle).  helper_sanity: K_4's odd cycles are longer than 2 but not than 3,
    f_4(4) is 2, not 3; h_3(2) is not 1; K_4 is edge-critical at 4, K_2 is not at 1, f_4(4) of erdos:917 is 6, not 5;
    f_3(3) is 1, not 0 (the page's odd cycles).  g258_order_mono (h_3(k) <= h_3(k+1)) is the fact X258.v's erdos:1013
    Notes use for the ratio's lower half; g258_chi_sub_exact (each value below chi(A) is chi of a subset) proves it. *)

From GTBase Require Import base common colourings bipartitions.
From Chromatic.conjectures Require Import X219 X258.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Chromatic-number facts *)

(** A non-adjacent pair of distinct vertices shares a colour: chi < #|G|. *)
Lemma g258_chi_lt_nonedge (G : sgraph) (x y : G) : x != y -> ~~ x -- y -> χ([set: G]) < #|G|.
Proof.
move=> xy nxy; have st : stable [set x; y].
  apply/stableP => u v; rewrite !inE => /orP[] /eqP-> /orP[] /eqP->;
  by rewrite ?sg_irrefl ?(negbTE nxy) // sg_sym (negbTE nxy).
apply: leq_ltn_trans (chiD1 [set: G] st) _.
have := leq_chi ([set: G] :\: [set x; y]); rewrite cardsDS ?subsetT // cards2 xy cardsT => h2.
have n2 : 2 <= #|G| by have := subset_leq_card (subsetT [set x; y]); rewrite cards2 xy cardsT.
apply: leq_ltn_trans (_ : (#|G| - 2).+1 < #|G|); first by rewrite ltnS.
by move: n2; case: #|G| => [|[|n]] // _; rewrite !subSS subn0 ltnS.
Qed.

(** A graph whose chromatic number is its order is complete. *)
Lemma g258_adj_of_chi (G : sgraph) : χ([set: G]) = #|G| -> forall x y : G, x != y -> x -- y.
Proof.
move=> h x y xy; apply/negPn/negP => nxy.
by have := g258_chi_lt_nonedge xy nxy; rewrite h ltnn.
Qed.

Lemma g258_chi_K (n : nat) : χ([set: 'K_n]) = n.
Proof. by rewrite chi_clique ?cardsT ?card_ord // => x y _ _ xy. Qed.

(** An odd cycle has length at least 3 (a one-vertex cycle would be a loop). *)
Lemma g258_odd_ucycle_gt2 (G : sgraph) (c : seq G) : ucycle (--) c -> odd (size c) -> 2 < size c.
Proof. by case: c => [|x [|y [|z s]]] //; rewrite /ucycle /= sg_irrefl. Qed.

(** A triangle is a cycle of length 3. *)
Lemma g258_triangle_ucycle (G : sgraph) (x y z : G) :
  x -- y -> y -- z -> z -- x -> ucycle (--) [:: x; y; z].
Proof.
move=> xy yz zx; rewrite /ucycle /= xy yz zx /= !inE negb_or.
by rewrite (sg_edgeNeq xy) (sg_edgeNeq yz) eq_sym (sg_edgeNeq zx).
Qed.

(** f_4(4) = 2: K_4 is the only 4-chromatic graph on 4 vertices, and its odd cycles are triangles. *)
Lemma g258_odd_girth_K4 : x258_odd_girth_number 4 4 2.
Proof.
split.
  exists 'K_4; split; [by rewrite card_ord | exact: g258_chi_K |].
  by move=> c uc oc; exact: g258_odd_ucycle_gt2.
move=> G m hG hchi hm; have adj := g258_adj_of_chi (etrans hchi (esym hG)).
have /card_gt2P[x [y [z [_ [xy yz zx]]]]] : 2 < #|[set: G]| by rewrite cardsT hG.
have := hm _ (g258_triangle_ucycle (adj _ _ xy) (adj _ _ yz) (adj _ _ zx)) isT.
by rewrite /= ltnS.
Qed.

Lemma g258_K1_triangle_free : triangle_free 'K_1.
Proof. by move=> x y z; rewrite (ord1 x) (ord1 y) sg_irrefl. Qed.

Lemma g258_K2_triangle_free : triangle_free 'K_2.
Proof. by move=> [[|[|?]] ?] [[|[|?]] ?] [[|[|?]] ?]. Qed.

Lemma g258_order_1 : x258_triangle_free_order 1 1.
Proof.
split; first by exists 'K_1; split; [rewrite card_ord | exact: g258_K1_triangle_free | exact: g258_chi_K].
by move=> G _ h; have := leq_chi [set: G]; rewrite h cardsT.
Qed.

Lemma g258_order_2 : x258_triangle_free_order 2 2.
Proof.
split; first by exists 'K_2; split; [rewrite card_ord | exact: g258_K2_triangle_free | exact: g258_chi_K].
by move=> G _ h; have := leq_chi [set: G]; rewrite h cardsT.
Qed.

(** Removing one vertex lowers chi by at most one, so every value below chi(A) is chi of a subset of A. *)
Lemma g258_chi_sub_exact (G : sgraph) (A : {set G}) (j : nat) :
  j <= χ(A) -> exists2 B : {set G}, B \subset A & χ(B) = j.
Proof.
have [n] := ubnP #|A|; elim: n A => // n IH A hA hj.
case: (ltngtP j χ(A)) hj => // [jlt _ | -> _]; last by exists A.
have /set0Pn[v vA] : A != set0 by apply: contraTneq jlt => ->; rewrite chi0.
have st : stable [set v] by apply/stableP => x y; rewrite !inE => /eqP-> /eqP->; rewrite sg_irrefl.
have hj : j <= χ(A :\: [set v]) by rewrite -ltnS; exact: leq_trans jlt (chiD1 A st).
have hA' : #|A :\: [set v]| < n.
  by move: hA; rewrite ltnS (cardsD1 v A) vA add1n.
have [B BA hB] := IH _ hA' hj; exists B => //; exact: subset_trans BA (subsetDl _ _).
Qed.

(** The kernel lemma of erdos:1013: h_3(k) <= h_3(k+1) (an induced subgraph of a triangle-free (k+1)-chromatic graph
    is triangle-free and k-chromatic). *)
Lemma g258_order_mono (k a b : nat) :
  x258_triangle_free_order k a -> x258_triangle_free_order k.+1 b -> a <= b.
Proof.
move=> [_ ha] [[G [hG tf hchi]] _].
have kle : k <= χ([set: G]) by rewrite hchi.
have [B _ hB] := g258_chi_sub_exact kle.
apply: leq_trans (ha (induced B) _ _) _.
- by move=> x y z; exact: tf.
- by rewrite chiT chi_induced.
- by rewrite -hG card_sig; exact: max_card.
Qed.

(** Deleting an edge leaves a non-adjacent pair, so chi then drops below the order: every graph is edge-critical at
    k = #|G| (so x258_edge_critical G k is a real constraint only below the order). *)
Lemma g258_edge_critical_order (G : sgraph) : x258_edge_critical G #|G|.
Proof.
move=> u v uv; have uv' : u != v by rewrite (sg_edgeNeq uv).
apply: (@g258_chi_lt_nonedge (del_edges [set u; v]) u v uv').
by rewrite /edge_rel /= subxx andbF.
Qed.

Lemma g258_edge_count_le (G : sgraph) : edge_count G <= 'C(#|G|, 2).
Proof.
rewrite /edge_count -card_edge_Kn; apply: (@sub_card_edge G 'K_#|G| enum_rank enum_rank_inj).
by move=> x y xy; rewrite /edge_rel /= (inj_eq enum_rank_inj) (sg_edgeNeq xy).
Qed.

(** f_4(4) = 6 for erdos:917: K_4 is edge-critical with 6 edges, and no graph on 4 vertices has more. *)
Lemma g258_critical_edges_K4 : x258_critical_edge_number 4 4 6.
Proof.
split; last by move=> G hG _ _; have := g258_edge_count_le G; rewrite hG.
exists 'K_4; split; [by rewrite card_ord | exact: g258_chi_K | | by rewrite edge_count_Kn].
by have := @g258_edge_critical_order 'K_4; rewrite card_ord.
Qed.

(** A bipartition is a proper 2-colouring. *)
Lemma g258_bipartition_chi (G : sgraph) (A : {set G}) : bipartition A -> χ([set: G]) <= 2.
Proof.
move=> /bipartition_neq bA; have := @proper_colouring_chi G bool (fun x => x \in A).
by rewrite card_bool; apply; apply/proper_colouringP => x y xy; exact: bA.
Qed.

(** A graph of chromatic number above 2 needs at least one deletion to become bipartite. *)
Lemma g258_bipartizing_pos (G : sgraph) (S : {set {set G}}) :
  2 < χ([set: G]) -> bipartite_after_deletion S -> 0 < #|S|.
Proof.
move=> h3 [A bA]; rewrite card_gt0; apply: contraTneq h3 => S0; rewrite -leqNgt.
apply: (@g258_bipartition_chi G A) => x y xy; apply: bA.
by rewrite /edge_rel /= /del_es_rel /= xy S0 inE.
Qed.

Lemma g258_critical_K3 : x219_subgraph_critical_for (fun H : sgraph => χ([set: H]) < 3) 'K_3.
Proof.
split; first by rewrite g258_chi_K ltnn.
  move=> v; rewrite chiT chi_induced; apply: leq_ltn_trans (leq_chi _) _.
  by have := cardsD1 v [set: 'K_3]; rewrite inE cardsT card_ord add1n => -[<-].
by move=> u v uv; have := @g258_edge_critical_order 'K_3 u v uv; rewrite card_ord.
Qed.

(** f_3(3) = 1 for erdos:744: K_3 is 3-critical and one deletion makes it a path; no 3-chromatic graph is bipartite. *)
Lemma g258_bipartizing_K3 : x258_critical_bipartizing_number 3 3 1.
Proof.
split; last by move=> G _ hchi _ S hS; apply: g258_bipartizing_pos hS; rewrite hchi.
exists 'K_3; split; [by rewrite card_ord | exact: g258_chi_K | exact: g258_critical_K3 |].
exists [set [set ord0; ord_max]]; split; first by rewrite cards1.
exists [set z : 'K_3 | val z == 1] => x y; rewrite /edge_rel /= /del_es_rel /= !inE.
move: x y => [[|[|[|?]]] ?] [[|[|[|?]]] ?] //=.
- move/negP; case; apply/eqP; congr [set _; _]; exact: val_inj.
- move/negP; case; apply/eqP; rewrite setUC; congr [set _; _]; exact: val_inj.
Qed.

(** ** helper_sanity *)

(** K_4: every odd cycle is longer than 2 but not than 3; f_4(4) = 2 and not 3. *)
Definition g258_og_helper_claim : Prop :=
  [/\ x258_odd_cycles_longer 'K_4 2, ~ x258_odd_cycles_longer 'K_4 3, x258_odd_girth_number 4 4 2 &
      ~ x258_odd_girth_number 4 4 3].

(** h_3(1) = 1 and h_3(2) = 2, not 1: two colours need two vertices. *)
Definition g258_tf_helper_claim : Prop :=
  [/\ x258_triangle_free_order 1 1, x258_triangle_free_order 2 2 & ~ x258_triangle_free_order 2 1].

(** K_4 is edge-critical at 4 but K_2 is not at 1 (one vertex keeps one colour); f_4(4) = 6, not 5. *)
Definition g258_ce_helper_claim : Prop :=
  [/\ x258_edge_critical 'K_4 4, ~ x258_edge_critical 'K_2 1, x258_critical_edge_number 4 4 6 &
      ~ x258_critical_edge_number 4 4 5].

(** f_3(3) = 1, not 0. *)
Definition g258_bz_helper_claim : Prop :=
  x258_critical_bipartizing_number 3 3 1 /\ ~ x258_critical_bipartizing_number 3 3 0.

Lemma g258_chi_pos (G : sgraph) (x : G) : 0 < χ([set: G]).
Proof.
apply: leq_trans (_ : 0 < χ([set x])) (sub_chi (subsetT _)).
by rewrite chi_clique ?cards1 // => u v; rewrite !inE => /eqP-> /eqP->; rewrite eqxx.
Qed.

Theorem g258_og_helper_sanity : g258_og_helper_claim.
Proof.
have [hK4 up] := g258_odd_girth_K4.
split => //; first by move=> c uc oc; exact: g258_odd_ucycle_gt2.
- by move=> h; have := up 'K_4 3 (card_ord 4) (g258_chi_K 4) h.
- by move=> [[G [hG hchi hm]] _]; have := up G 3 hG hchi hm.
Qed.

Theorem g258_tf_helper_sanity : g258_tf_helper_claim.
Proof.
split; [exact: g258_order_1 | exact: g258_order_2 |].
by move=> [[G [hG _ hchi]] _]; have := leq_chi [set: G]; rewrite hchi cardsT hG.
Qed.

Theorem g258_ce_helper_sanity : g258_ce_helper_claim.
Proof.
split; [by have := @g258_edge_critical_order 'K_4; rewrite card_ord | | exact: g258_critical_edges_K4 |].
- move=> h; have := h ord0 ord_max isT; rewrite ltnS leqn0 => /eqP.
  by move=> h0; have := @g258_chi_pos (del_edges [set (ord0 : 'K_2); ord_max]) ord0; rewrite h0.
- move=> [_ up]; have := up 'K_4 (card_ord 4) (g258_chi_K 4).
  by have := @g258_edge_critical_order 'K_4; rewrite card_ord edge_count_Kn => h /(_ h).
Qed.

Theorem g258_bz_helper_sanity : g258_bz_helper_claim.
Proof.
split; first exact: g258_bipartizing_K3.
move=> [[G [_ hchi _ [S [hS bS]]]] _].
have h3 : 2 < χ([set: G]) by rewrite hchi.
by have := g258_bipartizing_pos h3 bS; rewrite lt0n -leqn0 hS.
Qed.

(** ** erdos:921 *)

(** hyp_inhabited: f_4(4) = 2 (K_4); the statement at k = 4. *)
Definition g258_og_hyp_claim : Prop :=
  [/\ 4 <= 4, x258_odd_girth_number 4 4 2 &
      (chromatic_odd_girth_order_statement ->
         exists A B N : nat, forall n f : nat, N <= n ->
           x258_odd_girth_number 4 n f -> n <= A * f ^ 2 /\ f ^ 2 <= B * n)].

Theorem g258_og_hyp_inhabited : g258_og_hyp_claim.
Proof. by split => //; [exact: g258_odd_girth_K4 | move=> h; exact: h 4 isT]. Qed.

(** not_trivially_true: without the odd-girth hypothesis, f = 0 breaks n <= A f^(k-2) at k = 4. *)
Definition g258_og_no_number : Prop :=
  forall k : nat, 4 <= k -> exists A B N : nat, forall n f : nat, N <= n ->
    n <= A * f ^ (k - 2) /\ f ^ (k - 2) <= B * n.

Definition g258_og_ntt_claim : Prop :=
  ~ g258_og_no_number /\ (g258_og_no_number -> chromatic_odd_girth_order_statement).

Theorem g258_og_not_trivially_true : g258_og_ntt_claim.
Proof.
split.
- by move=> h; have [A [B [N hN]]] := h 4 isT; case: (hN N.+1 0 (leqnSn N)); rewrite muln0.
- by move=> h k hk; have [A [B [N hN]]] := h k hk; exists A, B, N => n f hn _; exact: hN.
Qed.

(** ** erdos:1013 *)

(** hyp_inhabited: h_3(1) = 1 (K_1) and h_3(2) = 2 (K_2); the statement at q = 1. *)
Definition g258_tf_hyp_claim : Prop :=
  [/\ x258_triangle_free_order 1 1, x258_triangle_free_order 2 2 &
      (triangle_free_chromatic_order_ratio_statement ->
         exists K : nat, forall k a b : nat, K <= k ->
           x258_triangle_free_order k a -> x258_triangle_free_order k.+1 b -> 1 * b <= 2 * a)].

Theorem g258_tf_hyp_inhabited : g258_tf_hyp_claim.
Proof. by split; [exact: g258_order_1 | exact: g258_order_2 | move=> h; exact: h 1 isT]. Qed.

(** not_trivially_true: without the two order hypotheses, a = 0 and b = 1 break the ratio bound at q = 1. *)
Definition g258_tf_no_order : Prop :=
  forall q : nat, 1 <= q -> exists K : nat, forall k a b : nat, K <= k -> q * b <= (q + 1) * a.

Definition g258_tf_ntt_claim : Prop :=
  ~ g258_tf_no_order /\ (g258_tf_no_order -> triangle_free_chromatic_order_ratio_statement).

Theorem g258_tf_not_trivially_true : g258_tf_ntt_claim.
Proof.
split.
- by move=> h; have [K hK] := h 1 isT; have := hK K 0 1 (leqnn K).
- by move=> h q hq; have [K hK] := h q hq; exists K => k a b hk _ _; exact: hK.
Qed.

(** ** erdos:917 *)

(** hyp_inhabited: f_4(4) = 6 (K_4); the statement's first clause at k = 4. *)
Definition g258_ce_hyp_claim : Prop :=
  x258_critical_edge_number 4 4 6 /\
  (critical_graph_edge_count_statement ->
     exists C N : nat, forall n f : nat, N <= n -> x258_critical_edge_number 4 n f -> n ^ 2 <= C * f).

Theorem g258_ce_hyp_inhabited : g258_ce_hyp_claim.
Proof. by split; [exact: g258_critical_edges_K4 | case=> h _ _; exact: h 4 isT]. Qed.

(** not_trivially_true: the first clause without its edge-number hypothesis: f = 0 breaks n^2 <= C f at k = 4. *)
Definition g258_ce_no_number : Prop :=
  [/\ forall k : nat, 4 <= k -> exists C N : nat, forall n f : nat, N <= n -> n ^ 2 <= C * f,
      forall q : nat, 1 <= q -> exists N : nat, forall n f : nat, N <= n ->
        x258_critical_edge_number 6 n f -> q * (4 * f) <= (q + 1) * n ^ 2 /\ q * n ^ 2 <= (q + 1) * (4 * f) &
      forall k q : nat, 6 <= k -> 1 <= q -> exists N : nat, forall n f : nat, N <= n ->
        x258_critical_edge_number k n f ->
        q * (2 * (k %/ 3) * f) <= (q + 1) * ((k %/ 3 - 1) * n ^ 2) /\
        q * ((k %/ 3 - 1) * n ^ 2) <= (q + 1) * (2 * (k %/ 3) * f)].

Definition g258_ce_ntt_claim : Prop :=
  ~ g258_ce_no_number /\ (g258_ce_no_number -> critical_graph_edge_count_statement).

Theorem g258_ce_not_trivially_true : g258_ce_ntt_claim.
Proof.
split.
- by move=> [h _ _]; have [C [N hN]] := h 4 isT; have := hN N.+1 0 (leqnSn N); rewrite muln0 leqn0 expn_eq0.
- move=> [h1 h2 h3]; split=> // k hk; have [C [N hN]] := h1 k hk.
  by exists C, N => n f hn _; exact: hN.
Qed.

(** ** erdos:744 *)

(** In a complete graph made bipartite by deleting S, two distinct vertices on one side form a pair of S. *)
Lemma g258_same_side_pair (G : sgraph) (S : {set {set G}}) (A : {set G}) (x y : G) :
  (forall u v : G, u != v -> u -- v) -> @bipartition (del_edge_set G S) A -> x != y ->
  (x \in A) = (y \in A) -> [set x; y] \in S.
Proof.
move=> adj bA xy same; apply/negPn/negP => nS.
have e : @edge_rel (del_edge_set G S) x y by rewrite /edge_rel /= /del_es_rel /= adj // nS.
by move: (bA x y e); rewrite same; case: (y \in A).
Qed.

(** Two distinct pairs of S give #|S| >= 2. *)
Lemma g258_two_pairs (G : sgraph) (S : {set {set G}}) (a b c : G) (P : {set G}) :
  [set a; b] \in S -> P \in S -> c \in P -> c \notin [set a; b] -> 1 < #|S|.
Proof.
move=> ab P_S cP cab; apply/card_gt1P; exists [set a; b], P; split => //.
by apply: contraNneq cab => ->.
Qed.

(** Deleting at most one edge never makes a complete graph on four vertices bipartite: one side holds three vertices,
    or each side holds two, and each pair inside a side must be deleted. *)
Lemma g258_bipartizing_ge2 (G : sgraph) (S : {set {set G}}) :
  #|G| = 4 -> (forall u v : G, u != v -> u -- v) -> bipartite_after_deletion S -> 1 < #|S|.
Proof.
move=> hG adj [A bA].
have pair := g258_same_side_pair adj bA.
have hC : #|A| + #|~: A| = 4 by rewrite cardsC hG.
case: (leqP 3 #|A|) => [/card_gt2P[x [y [z [[xA yA zA] [xy yz zx]]]]] | hA].
  apply: (@g258_two_pairs G S x y z [set x; z]).
  - by apply: pair => //; rewrite xA yA.
  - by apply: pair; [rewrite eq_sym | rewrite xA zA].
  - by rewrite !inE eqxx orbT.
  - by rewrite !inE negb_or zx eq_sym yz.
case: (leqP 3 #|~: A|) => [/card_gt2P[x [y [z [[xA yA zA] [xy yz zx]]]]] | hA'].
  move: xA yA zA; rewrite !inE => xA yA zA.
  apply: (@g258_two_pairs G S x y z [set x; z]).
  - by apply: pair => //; rewrite (negbTE xA) (negbTE yA).
  - by apply: pair; [rewrite eq_sym | rewrite (negbTE xA) (negbTE zA)].
  - by rewrite !inE eqxx orbT.
  - by rewrite !inE negb_or zx eq_sym yz.
have h2 : 1 < #|A|.
  by rewrite ltnNge; apply/negP => le1; have := leq_add le1 (hA' : #|~: A| <= 2); rewrite hC.
have h2' : 1 < #|~: A|.
  by rewrite ltnNge; apply/negP => le1; have := leq_add (hA : #|A| <= 2) le1; rewrite hC.
have /card_gt1P[x [y [xA yA xy]]] := h2.
have /card_gt1P[u [v [uA vA uv]]] := h2'.
move: uA vA; rewrite !inE => uA vA.
apply: (@g258_two_pairs G S x y u [set u; v]).
- by apply: pair => //; rewrite xA yA.
- by apply: pair => //; rewrite (negbTE uA) (negbTE vA).
- by rewrite !inE eqxx.
- by rewrite !inE negb_or; apply/andP; split; apply: contraNneq uA => ->.
Qed.

(** Two distinct vertices of a two-element set are the set. *)
Lemma g258_side_pair (T : finType) (A : {set T}) (x y : T) :
  #|A| = 2 -> x != y -> x \in A -> y \in A -> [set x; y] = A.
Proof.
move=> hA xy xA yA; apply/eqP; rewrite eqEcard cards2 xy hA; apply/andP; split => //.
by apply/subsetP => z; rewrite !inE => /orP[] /eqP->.
Qed.

Lemma g258_critical_K4 : x219_subgraph_critical_for (fun H : sgraph => χ([set: H]) < 4) 'K_4.
Proof.
split; first by rewrite g258_chi_K ltnn.
  move=> v; rewrite chiT chi_induced; apply: leq_ltn_trans (leq_chi _) _.
  by have := cardsD1 v [set: 'K_4]; rewrite inE cardsT card_ord add1n => -[<-].
by move=> u v uv; have := @g258_edge_critical_order 'K_4 u v uv; rewrite card_ord.
Qed.

(** f_4(4) = 2 for erdos:744: K_4 is 4-critical; deleting the pairs {0, 3} and {1, 2} leaves the 4-cycle with side
    {0, 3}; one deletion never suffices (g258_bipartizing_ge2), and K_4 is the only 4-chromatic graph on 4 vertices. *)
Lemma g258_bipartizing_K4 : x258_critical_bipartizing_number 4 4 2.
Proof.
split; last first.
  move=> G hG hchi _ S hS; apply: (g258_bipartizing_ge2 hG _ hS).
  by apply: g258_adj_of_chi; rewrite hchi hG.
exists 'K_4; split; [by rewrite card_ord | exact: g258_chi_K | exact: g258_critical_K4 |].
pose A0 : {set 'K_4} := [set ord0; ord_max].
have hA0 : #|A0| = 2 by rewrite /A0 cards2.
have hC0 : #|~: A0| = 2 by rewrite cardsCs setCK card_ord hA0.
exists [set A0; ~: A0]; split; first by rewrite cards2 ltnS leq_b1.
exists A0 => x y; rewrite /edge_rel /= /del_es_rel /= => /andP[xy nS].
have xy' : x != y by rewrite (sg_edgeNeq xy).
case xA: (x \in A0); case yA: (y \in A0) => //=.
- by move: nS; rewrite (g258_side_pair hA0 xy' xA yA) !inE eqxx /=.
- have xA' : x \in ~: A0 by rewrite inE xA.
  have yA' : y \in ~: A0 by rewrite inE yA.
  by move: nS; rewrite (g258_side_pair hC0 xy' xA' yA') !inE eqxx orbT /=.
Qed.

(** hyp_inhabited: f_4(4) = 2 (K_4); the statement's second clause, at k = 4. *)
Definition g258_bz_hyp_claim : Prop :=
  x258_critical_bipartizing_number 4 4 2 /\
  (critical_graph_bipartizing_edges_statement ->
     exists C N : nat, forall n m : nat, N <= n -> x258_critical_bipartizing_number 4 n m -> n <= 2 ^ (C * m)).

Theorem g258_bz_hyp_inhabited : g258_bz_hyp_claim.
Proof. by split; [exact: g258_bipartizing_K4 | case]. Qed.

(** not_trivially_true: the first clause without its number hypothesis: m = 0 breaks M <= m at M = 1. *)
Definition g258_bz_no_number : Prop :=
  (exists K : nat, forall k : nat, K <= k -> forall M : nat, exists N : nat, forall n m : nat, N <= n -> M <= m) /\
  (exists C N : nat, forall n m : nat, N <= n -> x258_critical_bipartizing_number 4 n m -> n <= 2 ^ (C * m)).

Definition g258_bz_ntt_claim : Prop :=
  ~ g258_bz_no_number /\ (g258_bz_no_number -> critical_graph_bipartizing_edges_statement).

Theorem g258_bz_not_trivially_true : g258_bz_ntt_claim.
Proof.
split.
- by move=> [[K hK] _]; have [N hN] := hK K (leqnn K) 1; have := hN N 0 (leqnn N).
- move=> [[K hK] h2]; split=> //; exists K => k hk M; have [N hN] := hK k hk M.
  by exists N => n m hn _; exact: hN.
Qed.

Print Assumptions g258_og_helper_sanity.
Print Assumptions g258_tf_helper_sanity.
Print Assumptions g258_ce_helper_sanity.
Print Assumptions g258_bz_helper_sanity.
Print Assumptions g258_order_mono.
Print Assumptions g258_og_hyp_inhabited.
Print Assumptions g258_og_not_trivially_true.
Print Assumptions g258_tf_hyp_inhabited.
Print Assumptions g258_tf_not_trivially_true.
Print Assumptions g258_ce_hyp_inhabited.
Print Assumptions g258_ce_not_trivially_true.
Print Assumptions g258_bz_hyp_inhabited.
Print Assumptions g258_bz_not_trivially_true.

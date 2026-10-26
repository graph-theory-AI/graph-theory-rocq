(** * Extremal.conjectures.grounding_X233 -- grounding certificates of wave X233.

    For each of the six rows: hyp_inhabited (the hypotheses hold on a concrete instance, and the
    statement then yields its conclusion object there) and not_trivially_true (a stronger variant
    that would make the row easy is false, and that variant implies the row).  The helper_sanity
    certificates are shared by the six rows, since check_milestone asks every row to cover every
    x233_ helper of X233.v.  Small instances: K_n, the edgeless graph on n vertices, the 5-cycle
    (degree 2 in it and in its complement), K_{2,2}, a 6-vertex graph made of three perfect
    matchings between three blocks of size 2 (no transversal triangle, no pure pair of blocks),
    and the classes of graphs with at most 2 or 4 vertices (hereditary, proper). *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries bij digraph sgraph.
From GTBase Require Import base common set_pairs triangles graph_classes poly_nat.
From Extremal.conjectures Require Import X233.
From mathcomp Require Import zify.
From Stdlib Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Instances and shared lemmas *)

(** ** Instances *)

Definition g233_edgeless (n : nat) : sgraph :=
  @SGraph 'I_n (fun _ _ => false) (fun _ _ => erefl) (fun _ => erefl).

Definition g233_singletons (G : sgraph) (f : 'I_3 -> G) : 'I_3 -> {set G} := fun i => [set f i].

(** Graphs with at most k vertices. *)
Definition g233_small (k : nat) (G : sgraph) : Prop := #|G| <= k.

(** Three blocks {0,1}, {2,3}, {4,5} joined pairwise by perfect matchings:
    0-2, 1-3 (B0-B1), 2-4, 3-5 (B1-B2), 1-4, 0-5 (B2-B0). *)
Definition g233_m6_rel (i j : 'I_6) : bool :=
  let p := (val i, val j) in
  [|| p == (0, 2), p == (2, 0), p == (1, 3), p == (3, 1), p == (2, 4), p == (4, 2),
      p == (3, 5), p == (5, 3), p == (1, 4), p == (4, 1), p == (0, 5) | p == (5, 0)].

Lemma g233_m6_sym : symmetric g233_m6_rel.
Proof. by move=> [[|[|[|[|[|[|i]]]]]] hi] [[|[|[|[|[|[|j]]]]]] hj]. Qed.

Lemma g233_m6_irrefl : irreflexive g233_m6_rel.
Proof. by move=> [[|[|[|[|[|[|i]]]]]] hi]. Qed.

Definition g233_m6 : sgraph := SGraph g233_m6_sym g233_m6_irrefl.

Definition g233_m6_blocks (i : 'I_3) : {set g233_m6} :=
  match val i with
  | 0 => [set (@Ordinal 6 0 isT : g233_m6); (@Ordinal 6 1 isT : g233_m6)]
  | 1 => [set (@Ordinal 6 2 isT : g233_m6); (@Ordinal 6 3 isT : g233_m6)]
  | _ => [set (@Ordinal 6 4 isT : g233_m6); (@Ordinal 6 5 isT : g233_m6)]
  end.

(** ** Degrees, edges and induced subgraphs *)

Lemma g233_Delta0 (G : sgraph) : (forall x y : G, ~~ (x -- y)) -> Delta G = 0.
Proof.
move=> h; apply/eqP; rewrite -leqn0; apply/bigmax_leqP => x _.
rewrite leqn0 cards_eq0; apply/eqP/setP => y; rewrite in_opn inE.
exact: negbTE (h x y).
Qed.

Lemma g233_Delta_induced_ge2 (G : sgraph) (S : {set G}) (v u w : G)
    (vS : v \in S) (uS : u \in S) (wS : w \in S) :
  u != w -> v -- u -> v -- w -> 2 <= Delta (induced S).
Proof.
move=> uw vu vw.
pose sv : induced S := Sub v vS.
pose su : induced S := Sub u uS.
pose sw : induced S := Sub w wS.
have ne : su != sw by apply: contra uw => /eqP e; apply/eqP; exact: (congr1 val e).
apply: leq_trans (leq_bigmax sv).
have -> : 2 = #|[set su; sw]| by rewrite cards2 ne.
apply: subset_leq_card; apply/subsetP => x; rewrite !inE => /orP [] /eqP ->.
- exact: vu.
- exact: vw.
Qed.

Lemma g233_edge_count0 (G : sgraph) : (forall x y : G, ~~ (x -- y)) -> edge_count G = 0.
Proof.
move=> h; apply/eqP; rewrite /edge_count cards_eq0; apply/eqP/setP => e.
rewrite sg_edge_setE !inE; apply/negbTE/negP => /existsP [x /existsP [y /andP [xy _]]].
by move: (h x y); rewrite xy.
Qed.

Lemma g233_edge_count_le (G : sgraph) : edge_count G <= 'C(#|G|, 2).
Proof.
rewrite /edge_count -card_draws; apply: subset_leq_card; apply/subsetP => e.
rewrite sg_edge_setE !inE => /existsP [x /existsP [y /andP [xy /eqP ->]]].
by rewrite cards2 (sg_edgeNeq xy).
Qed.

Lemma g233_card_induced (G : sgraph) (S : {set G}) : #|induced S| = #|S|.
Proof. by rewrite card_sig; apply: eq_card => x; rewrite !inE. Qed.

Lemma g233_induced_setT_diso (G : sgraph) : induced [set: G] ≃ G.
Proof.
apply: (@Diso'' (induced [set: G]) G val (fun x => Sub x (in_setT x))).
- by move=> x; apply: val_inj.
- by move=> x; rewrite SubK.
- by move=> x y.
- by move=> x y.
Qed.

Lemma g233_edge_count_setT (G : sgraph) : edge_count (induced [set: G]) = edge_count G.
Proof. exact: edge_count_diso (g233_induced_setT_diso G). Qed.

(** ** Copies *)

Lemma g233_copies0 (G H : sgraph) : #|G| < #|H| -> x233_induced_copies G H = 0.
Proof.
move=> lt; apply/eqP; rewrite cards_eq0; apply/eqP/setP => f; rewrite !inE.
apply/negbTE/negP => /andP [/injectiveP inj _].
by move: (leq_card _ inj); rewrite leqNgt lt.
Qed.

(** ** The 5-cycle is not 1/4-restricted: degree 2 in C_5 and in its complement *)

Lemma g233_C5_not_restricted : ~ x233_restricted 1 4 [set: cycle_graph 5].
Proof.
have c5 : #|[set: cycle_graph 5]| = 5 by rewrite cardsT card_ord.
pose v0 : cycle_graph 5 := @Ordinal 5 0 isT.
pose v1 : cycle_graph 5 := @Ordinal 5 1 isT.
pose v2 : cycle_graph 5 := @Ordinal 5 2 isT.
pose v3 : cycle_graph 5 := @Ordinal 5 3 isT.
pose v4 : cycle_graph 5 := @Ordinal 5 4 isT.
have d1 : 2 <= Delta (induced [set: cycle_graph 5]).
  exact: (@g233_Delta_induced_ge2 _ _ v0 v1 v4 (in_setT _) (in_setT _) (in_setT _) isT isT isT).
have d2 : 2 <= Delta (@induced (compl (cycle_graph 5)) [set: cycle_graph 5]).
  exact: (@g233_Delta_induced_ge2 (compl (cycle_graph 5)) _ v0 v2 v3
            (in_setT _) (in_setT _) (in_setT _) isT isT isT).
rewrite /x233_restricted c5 => -[le|le].
- by have := leq_trans (leq_mul (leqnn 4) d1) le.
- by have := leq_trans (leq_mul (leqnn 4) d2) le.
Qed.

(** ** Singleton blockades *)

Lemma g233_singletons_blockade (G : sgraph) (f : 'I_3 -> G) :
  injective f -> x233_blockade (g233_singletons f).
Proof.
move=> inj; split=> [i|i j ij].
- by apply/set0Pn; exists (f i); rewrite /g233_singletons inE.
- by rewrite /g233_singletons disjoints1 inE (inj_eq inj).
Qed.

Lemma g233_singletons_width (G : sgraph) (f : 'I_3 -> G) : x233_width (g233_singletons f) = 1.
Proof.
rewrite /x233_width /g233_singletons /= (eq_bigr (fun _ => 1)); first by move=> i _; exact: cards1.
by rewrite cards1 big_const_ord.
Qed.

Lemma g233_edgeless3_no_transversal :
  ~ x233_transversal_triangle (g233_singletons (fun i : 'I_3 => i : g233_edgeless 3)).
Proof.
case=> T [/andP [_ /cliqueP cT] h].
have inT (i : 'I_3) : (i : g233_edgeless 3) \in T.
  have /set0Pn [x] : T :&: [set (i : g233_edgeless 3)] != set0.
    by rewrite -cards_eq0; move: (h i); rewrite /g233_singletons => ->.
  by rewrite !inE => /andP [xT /eqP <-].
by have := cT _ _ (inT (@Ordinal 3 0 isT)) (inT (@Ordinal 3 1 isT)) isT.
Qed.

(** ** The three-matching blockade *)

Lemma g233_m6_blocks_val (i : 'I_3) (x : g233_m6) : (x \in g233_m6_blocks i) = (val x %/ 2 == val i).
Proof.
case: i => [[|[|[|i]]] hi] //=; rewrite !inE;
  by case: x => [[|[|[|[|[|[|x]]]]]] hx].
Qed.

Lemma g233_m6_card (i : 'I_3) : #|g233_m6_blocks i| = 2.
Proof. by case: i => [[|[|[|i]]] hi] //=; rewrite cards2. Qed.

Lemma g233_m6_width : x233_width g233_m6_blocks = 2.
Proof.
rewrite /x233_width (eq_bigr (fun _ => 2)); first by move=> i _; exact: g233_m6_card.
by rewrite g233_m6_card big_const_ord.
Qed.

Lemma g233_m6_blockade : x233_blockade g233_m6_blocks.
Proof.
split=> [i|i j ij].
- by rewrite -cards_eq0 g233_m6_card.
- rewrite -setI_eq0; apply/eqP/setP => x; rewrite !inE !g233_m6_blocks_val.
  apply/negbTE/negP => /andP [/eqP a /eqP b].
  by move: ij; rewrite -(inj_eq val_inj) -a b eqxx.
Qed.

Lemma g233_m6_no_rainbow_triangle (a b c : g233_m6) :
  val a %/ 2 = 0 -> val b %/ 2 = 1 -> val c %/ 2 = 2 -> a -- b -> b -- c -> a -- c -> False.
Proof.
case: a b c => [[|[|[|[|[|[|a]]]]]] ha] [[|[|[|[|[|[|b]]]]]] hb] [[|[|[|[|[|[|c]]]]]] hc] //=.
Qed.

Lemma g233_m6_no_transversal : ~ x233_transversal_triangle g233_m6_blocks.
Proof.
case=> T [/andP [_ /cliqueP cT] h].
have pick (i : 'I_3) : exists2 x : g233_m6, x \in T & val x %/ 2 = val i.
  have /set0Pn [x] : T :&: g233_m6_blocks i != set0 by rewrite -cards_eq0 h.
  by rewrite inE g233_m6_blocks_val => /andP [xT /eqP xi]; exists x.
have [a aT ha] := pick (@Ordinal 3 0 isT).
have [b bT hb] := pick (@Ordinal 3 1 isT).
have [c cT' hc] := pick (@Ordinal 3 2 isT).
have ne (x y : g233_m6) : val x %/ 2 != val y %/ 2 -> x != y by apply: contra => /eqP ->.
apply: (g233_m6_no_rainbow_triangle ha hb hc).
- by apply: cT => //; apply: ne; rewrite ha hb.
- by apply: cT => //; apply: ne; rewrite hb hc.
- by apply: cT => //; apply: ne; rewrite ha hc.
Qed.

(** No two blocks form a pure pair: each pair of blocks is joined by a perfect matching. *)
Lemma g233_m6_not_pure (i j : 'I_3) :
  i != j -> ~~ (complete_between (g233_m6_blocks i) (g233_m6_blocks j) ||
                anticomplete (g233_m6_blocks i) (g233_m6_blocks j)).
Proof.
case: i => [[|[|[|i]]] hi]; case: j => [[|[|[|j]]] hj] //= _;
  apply/negP => /orP [/complete_betweenP h | /anticompleteP [_ h]].
(* goals in order (i, j) = (0,1), (0,2), (1,0), (1,2), (2,0), (2,1); complete then anticomplete *)
- by have := h _ _ (set21 _ _) (set22 _ _).
- exact: (h _ _ (set21 _ _) (set21 _ _) isT).
- by have := h _ _ (set21 _ _) (set21 _ _).
- exact: (h _ _ (set21 _ _) (set22 _ _) isT).
- by have := h _ _ (set21 _ _) (set22 _ _).
- exact: (h _ _ (set21 _ _) (set21 _ _) isT).
- by have := h _ _ (set21 _ _) (set22 _ _).
- exact: (h _ _ (set21 _ _) (set21 _ _) isT).
- by have := h _ _ (set21 _ _) (set21 _ _).
- exact: (h _ _ (set21 _ _) (set22 _ _) isT).
- by have := h _ _ (set21 _ _) (set22 _ _).
- exact: (h _ _ (set21 _ _) (set21 _ _) isT).
Qed.

(** ** Small graphs: hereditary and proper *)

Lemma g233_small_hereditary (k : nat) : hereditary_class (g233_small k).
Proof.
split.
- move=> G H; rewrite /g233_small => le i.
  by rewrite -(card_bij (diso_v i)).
- move=> G S; rewrite /g233_small => le.
  by rewrite g233_card_induced; apply: leq_trans (max_card _) le.
Qed.

Lemma g233_small_proper (k : nat) : ~ g233_small k 'K_k.+1.
Proof. by rewrite /g233_small card_ord ltnn. Qed.

(** ** The complete bipartite graph K_{2,2} (= C_4): 4 vertices, 4 edges *)

Lemma g233_KB_card (m n : nat) : #|'K_m,n| = m + n.
Proof. by rewrite card_sum !card_ord. Qed.

Lemma g233_KB_deg (m n : nat) (x : 'K_m,n) : #|N(x)| = if x is inl _ then n else m.
Proof.
case: x => i.
- have -> : N(inl i : 'K_m,n) = inr @: [set: 'I_n].
    apply/setP => -[j|j]; rewrite !inE /edge_rel /= /kb_rel /=.
    + by apply/esym/imsetP => -[k _].
    + by rewrite imset_f // inE.
  by rewrite card_imset ?cardsT ?card_ord //; exact: inr_inj.
- have -> : N(inr i : 'K_m,n) = inl @: [set: 'I_m].
    apply/setP => -[j|j]; rewrite !inE /edge_rel /= /kb_rel /=.
    + by rewrite imset_f // inE.
    + by apply/esym/imsetP => -[k _].
  by rewrite card_imset ?cardsT ?card_ord //; exact: inl_inj.
Qed.

Lemma g233_KB_edges (m n : nat) : edge_count 'K_m,n = m * n.
Proof.
rewrite /edge_count; apply/eqP; rewrite -(eqn_pmul2l (isT : 0 < 2)) edges_sum_degrees.
rewrite (eq_bigr (fun x : 'K_m,n => if x is inl _ then n else m)); first by move=> x _; exact: g233_KB_deg.
rewrite big_sumType /= !sum_nat_const.
rewrite (eq_card (B := 'I_m)) // (eq_card (B := 'I_n)) // !card_ord.
by rewrite mulnC mul2n addnn.
Qed.

(** [set: K_{2,2}] is not 1/4-homogeneous: 4 edges among C(4,2) = 6 pairs. *)
Lemma g233_K22_not_homogeneous : ~ x233_homogeneous 1 4 [set: 'K_2,2].
Proof.
rewrite /x233_homogeneous g233_edge_count_setT g233_KB_edges cardsT g233_KB_card.
by case.
Qed.

(** ** Closeness to a family the graph belongs to: no edit needed *)

Lemma g233_close_self (F : sgraph -> Prop) (G : sgraph) (a b : nat) : F G -> x233_close F G a b.
Proof.
case: G => T e s i FG; exists e, s, i; split=> //.
rewrite (_ : [set p | _] = set0); first by apply/setP => p; rewrite !inE eqxx.
by rewrite cards0 muln0.
Qed.

(** ** Graphs on at most 2 vertices are degree-bounded (g = 1) *)

Lemma g233_small2_degree_bounded : x233_degree_bounded (g233_small 2).
Proof.
exists (fun _ => 1) => G small /=; rewrite muln1.
apply: leq_trans (leq_mul (leqnn 2) (g233_edge_count_le G)) _.
by move: small; rewrite /g233_small; case: #|G| => [|[|[|k]]].
Qed.

(** ** Arithmetic for the complete-graph variant of arXiv:2311.05500#00 *)

Lemma g233_arith (C : nat) :
  C ^ 2 * (2 * C ^ 2).+1.*2.+1 ^ 3 < ((2 * C ^ 2).+1.*2.+1 * (2 * C ^ 2).+1) ^ 2.
Proof.
set k := (2 * C ^ 2).+1; set n := k.*2.+1.
have nk : C ^ 2 * n < k ^ 2 by rewrite /n /k; nia.
by rewrite expnMn (expnSr n 2) mulnCA ltn_pmul2l ?expn_gt0.
Qed.

(** ** Helper sanity (shared by the six rows) *)

Definition g233_restricted_claim : Prop :=
  [/\ forall (G : sgraph) (a b : nat), x233_restricted a b (set0 : {set G}),
      forall n a b : nat, x233_restricted a b [set: 'K_n],
      forall (G : sgraph) (a b a' b' : nat) (X : {set G}),
        0 < b -> a * b' <= a' * b -> x233_restricted a b X -> x233_restricted a' b' X
    & ~ x233_restricted 1 4 [set: cycle_graph 5]].

Theorem g233_restricted_sanity : g233_restricted_claim.
Proof.
split.
- move=> G a b; rewrite /x233_restricted; left.
  have D : Delta (induced (set0 : {set G})) = 0.
    by apply: g233_Delta0 => x y; have := valP x; rewrite inE.
  by rewrite D muln0.
- move=> n a b; rewrite /x233_restricted; right.
  have D : Delta (@induced (compl 'K_n) [set: 'K_n]) = 0.
    by apply: g233_Delta0 => x y; exact: (compl_Kn_edgeless (val x) (val y)).
  by rewrite D muln0.
- move=> G a b a' b' X bpos hab.
  have key : forall D s, b * D <= a * s -> b' * D <= a' * s.
    move=> D s h; rewrite -(leq_pmul2l bpos) mulnCA.
    apply: leq_trans (leq_mul (leqnn b') h) _.
    rewrite mulnA (mulnC b' a) [b * _]mulnA (mulnC b a').
    exact: leq_mul hab (leqnn s).
  by rewrite /x233_restricted => -[h|h]; [left|right]; exact: key h.
- exact: g233_C5_not_restricted.
Qed.

Definition g233_copies_claim : Prop :=
  (forall H : sgraph, 0 < x233_induced_copies H H) /\
  (forall G H : sgraph, #|G| < #|H| -> x233_induced_copies G H = 0).

Theorem g233_copies_sanity : g233_copies_claim.
Proof.
split; last exact: g233_copies0.
move=> H; apply/card_gt0P; exists [ffun x => x]; rewrite inE.
apply/andP; split.
- by apply/injectiveP => x y; rewrite !ffunE.
- by apply/forallP => x; apply/forallP => y; rewrite !ffunE eqxx.
Qed.

Definition g233_blockade_claim : Prop :=
  [/\ x233_blockade (g233_singletons (fun i : 'I_3 => i : 'K_3)),
      x233_width (g233_singletons (fun i : 'I_3 => i : 'K_3)) = 1,
      x233_transversal_triangle (g233_singletons (fun i : 'I_3 => i : 'K_3))
    & ~ x233_transversal_triangle (g233_singletons (fun i : 'I_3 => i : g233_edgeless 3))].

Theorem g233_blockade_sanity : g233_blockade_claim.
Proof.
split.
- by apply: g233_singletons_blockade => i j.
- exact: g233_singletons_width.
- exists [set: 'K_3]; split.
  + apply/andP; split; first by rewrite cardsT card_ord.
    by apply/cliqueP => x y _ _.
  + by move=> i; rewrite /g233_singletons setTI cards1.
- exact: g233_edgeless3_no_transversal.
Qed.

Definition g233_density_claim : Prop :=
  [/\ forall n : nat, x233_max_density_at_most (g233_edgeless n) 0 1,
      x233_max_density_at_most 'K_3 1 1
    & ~ x233_max_density_at_most 'K_3 2 3].

Theorem g233_density_sanity : g233_density_claim.
Proof.
split.
- move=> n S; have e0 : edge_count (induced S) = 0 by apply: g233_edge_count0 => x y.
  by rewrite e0.
- move=> S; rewrite !mul1n; apply: leq_trans (g233_edge_count_le _) _.
  rewrite g233_card_induced.
  have : #|S| <= 3 by apply: leq_trans (max_card _) _; rewrite card_ord.
  by case: #|S| => [|[|[|[|k]]]].
- move=> h; have := h [set: 'K_3].
  by rewrite g233_edge_count_setT edge_count_K3 cardsT card_ord.
Qed.

Definition g233_close_homogeneous_claim : Prop :=
  [/\ forall (F : sgraph -> Prop) (G : sgraph) (b : nat), F G -> x233_close F G 0 b,
      forall n a b : nat, a < b -> x233_homogeneous a b [set: 'K_n],
      forall (G : sgraph) (a b : nat) (S : {set G}), #|S| <= 1 -> x233_homogeneous a b S
    & ~ x233_homogeneous 1 4 [set: 'K_2,2]].

Theorem g233_close_homogeneous_sanity : g233_close_homogeneous_claim.
Proof.
split.
- by move=> F G b FG; exact: g233_close_self.
- move=> n a b ab; rewrite /x233_homogeneous; right.
  rewrite g233_edge_count_setT edge_count_Kn cardsT card_ord.
  exact: leq_mul (leq_subr a b) (leqnn _).
- move=> G a b S S1; rewrite /x233_homogeneous; left.
  have c0 : 'C(#|S|, 2) = 0 by case: #|S| S1 => [|[|]].
  have e0 : edge_count (induced S) = 0.
    by apply/eqP; rewrite -leqn0 -c0 -(g233_card_induced S) g233_edge_count_le.
  by rewrite e0 c0 !muln0.
- exact: g233_K22_not_homogeneous.
Qed.

Lemma g233_biclique_half (G : sgraph) : x233_biclique_number G <= #|G| %/ 2.
Proof.
apply/bigmax_leqP => s /existsP [A /existsP [B /and3P [/eqP As /eqP Bs c]]].
rewrite leq_divRL // muln2 -addnn -{1}As -Bs -cardsUI.
rewrite (_ : A :&: B = set0) ?cards0 ?addn0 ?max_card //.
by apply/eqP; rewrite setI_eq0; exact: complete_between_disjoint c.
Qed.

Definition g233_biclique_claim : Prop :=
  [/\ x233_biclique_number 'K_1 = 0,
      x233_biclique_number 'K_2 = 1,
      forall G : sgraph, 2 * x233_biclique_number G <= #|G|
    & x233_degree_bounded (g233_small 2)].

Theorem g233_biclique_sanity : g233_biclique_claim.
Proof.
have half (G : sgraph) : 2 * x233_biclique_number G <= #|G|.
  apply: leq_trans (_ : 2 * (#|G| %/ 2) <= #|G|).
  - by rewrite leq_mul2l g233_biclique_half orbT.
  - by rewrite mulnC leq_trunc_div.
split=> //.
- apply/eqP; rewrite -leqn0; apply: leq_trans (g233_biclique_half _) _.
  by rewrite card_ord.
- apply/eqP; rewrite eqn_leq; apply/andP; split.
  + by apply: leq_trans (g233_biclique_half _) _; rewrite card_ord.
  + have h1 : 1 < #|'K_2|.+1 by rewrite card_ord.
    pose s1 : 'I_(#|'K_2|.+1) := Ordinal h1.
    have P1 : [exists A : {set 'K_2}, exists B : {set 'K_2},
                 [&& #|A| == s1, #|B| == s1 & complete_between A B]].
      apply/existsP; exists [set (@Ordinal 2 0 isT : 'K_2)].
      apply/existsP; exists [set (@Ordinal 2 1 isT : 'K_2)].
      rewrite !cards1; apply/and3P; split=> //.
      by apply/complete_betweenP => a b; rewrite !inE => /eqP -> /eqP ->.
    rewrite /x233_biclique_number; apply: (@leq_trans s1) => //; apply: leq_bigmax_cond; exact: P1.
- exact: g233_small2_degree_bounded.
Qed.

(** ** Rows *)

Definition g233_cover_hyp_claim : Prop :=
  induced_free 'K_1 'K_2 /\
  (restricted_union_cover_statement ->
     exists N : nat, exists P : 'I_N -> {set 'K_1},
       (forall v, exists i, v \in P i) /\ forall i, x233_restricted 1 1 (P i)).

Theorem g233_cover_hyp_inhabited : g233_cover_hyp_claim.
Proof.
have fr : induced_free 'K_1 'K_2 by apply: induced_free_card; rewrite !card_ord.
split=> // h; have [N hN] := h 'K_2 1 1 isT isT.
by exists N; exact: hN 'K_1 fr.
Qed.

(** The variant with N = 1 (every H-free graph is itself restricted) is false: C_5 is
    K_6-free and not 1/4-restricted. It implies the row (N = 1, P = [set: G]). *)
Definition g233_cover_one : Prop :=
  forall (H : sgraph) (a b : nat), 0 < a -> 0 < b ->
    forall G : sgraph, induced_free G H -> x233_restricted a b [set: G].

Definition g233_cover_ntt_claim : Prop :=
  ~ g233_cover_one /\ (g233_cover_one -> restricted_union_cover_statement).

Theorem g233_cover_not_trivially_true : g233_cover_ntt_claim.
Proof.
split.
- move=> h; apply: g233_C5_not_restricted.
  by apply: (h 'K_6 1 4 isT isT); apply: induced_free_card; rewrite !card_ord.
- move=> h H a b a0 b0; exists 1 => G fr; exists (fun _ => [set: G]); split.
  + by move=> v; exists ord0; rewrite in_setT.
  + by move=> i; exact: h H a b a0 b0 G fr.
Qed.

Definition g233_nikiforov_hyp_claim : Prop :=
  [/\ 0 < #|'K_2|, x233_induced_copies 'K_1 'K_2 = 0 &
      (polynomial_nikiforov_statement ->
         exists2 d : nat, 0 < d & exists S : {set 'K_1},
           x233_restricted 1 3 S /\ 1 ^ d * #|'K_1| <= 3 ^ d * #|S|)].

Theorem g233_nikiforov_hyp_inhabited : g233_nikiforov_hyp_claim.
Proof.
have k2 : 0 < #|'K_2| by rewrite card_ord.
have c0 : x233_induced_copies 'K_1 'K_2 = 0 by apply: g233_copies0; rewrite !card_ord.
split=> // h; have [d [d0 hd]] := h 'K_2 k2.
exists d => //; apply: (hd 1 3 'K_1 isT isT).
by rewrite c0 muln0.
Qed.

(** The variant with S = V(G) is false (H = K_6, G = C_5, eps = 1/4: no copy, and C_5 is
    not 1/4-restricted); it implies the row (the size bound holds since a < b). *)
Definition g233_nikiforov_whole : Prop :=
  forall H : sgraph, 0 < #|H| ->
    exists d : nat, 0 < d /\
      forall (a b : nat) (G : sgraph), 0 < a -> 2 * a < b ->
        b ^ (d * #|H|) * x233_induced_copies G H <= (a ^ d * #|G|) ^ #|H| ->
        x233_restricted a b [set: G].

Definition g233_nikiforov_ntt_claim : Prop :=
  ~ g233_nikiforov_whole /\ (g233_nikiforov_whole -> polynomial_nikiforov_statement).

Theorem g233_nikiforov_not_trivially_true : g233_nikiforov_ntt_claim.
Proof.
split.
- move=> h; have k6 : 0 < #|'K_6| by rewrite card_ord.
  have [d [_ hd]] := h 'K_6 k6.
  apply: g233_C5_not_restricted; apply: (hd 1 4 (cycle_graph 5) isT isT).
  by rewrite g233_copies0 ?muln0 // !card_ord.
- move=> h H H0; have [d [d0 hd]] := h H H0.
  exists d; split=> // a b G a0 h2 hyp; exists [set: G]; split; first exact: hd a b G a0 h2 hyp.
  have ab : a <= b := leq_trans (leq_pmull a (isT : 0 < 2)) (ltnW h2).
  rewrite cardsT; apply: (leq_mul _ (leqnn _)); by rewrite leq_exp2r.
Qed.

Definition g233_pure_hyp_claim : Prop :=
  [/\ x233_blockade (g233_singletons (fun i : 'I_3 => i : g233_edgeless 3)),
      ~ x233_transversal_triangle (g233_singletons (fun i : 'I_3 => i : g233_edgeless 3)) &
      (transversal_triangle_pure_pair_statement ->
         exists (i j : 'I_3) (X Y : {set g233_edgeless 3}),
           [/\ i != j, X \subset g233_singletons (fun i : 'I_3 => i : g233_edgeless 3) i,
               Y \subset g233_singletons (fun i : 'I_3 => i : g233_edgeless 3) j
             & complete_between X Y || anticomplete X Y])].

Theorem g233_pure_hyp_inhabited : g233_pure_hyp_claim.
Proof.
have bl : x233_blockade (g233_singletons (fun i : 'I_3 => i : g233_edgeless 3)).
  by apply: g233_singletons_blockade => i j.
have nt := g233_edgeless3_no_transversal.
split=> // -[p [q [p0 q0 h]]].
have [i [j [X [Y [ij Xi Yj pur _]]]]] := h _ _ bl nt.
by exists i, j, X, Y.
Qed.

(** The variant with c = eps = 1 (p = q = 1) is false on the three-matching blockade of
    g233_m6 (width 2: only whole blocks are large enough, and no two are pure); it implies
    the row. *)
Definition g233_pure_linear : Prop :=
  forall (G : sgraph) (B : 'I_3 -> {set G}),
    x233_blockade B -> ~ x233_transversal_triangle B ->
    exists (i j : 'I_3) (X Y : {set G}),
      [/\ i != j, X \subset B i, Y \subset B j,
          complete_between X Y || anticomplete X Y &
          x233_width B <= #|X| /\ x233_width B <= #|Y|].

Definition g233_pure_ntt_claim : Prop :=
  [/\ x233_blockade g233_m6_blocks, ~ x233_transversal_triangle g233_m6_blocks,
      ~ g233_pure_linear & (g233_pure_linear -> transversal_triangle_pure_pair_statement)].

Theorem g233_pure_not_trivially_true : g233_pure_ntt_claim.
Proof.
split.
- exact: g233_m6_blockade.
- exact: g233_m6_no_transversal.
- move=> h.
  have [i [j [X [Y [ij Xi Yj pur [wX wY]]]]]] := h _ _ g233_m6_blockade g233_m6_no_transversal.
  rewrite g233_m6_width in wX wY.
  have eX : X = g233_m6_blocks i by apply/eqP; rewrite eqEcard Xi g233_m6_card wX.
  have eY : Y = g233_m6_blocks j by apply/eqP; rewrite eqEcard Yj g233_m6_card wY.
  by move: pur; rewrite eX eY; apply/negP; exact: g233_m6_not_pure ij.
- move=> h; exists 1, 1; split=> // G B b nt.
  have [i [j [X [Y [ij Xi Yj pur [wX wY]]]]]] := h G B b nt.
  by exists i, j, X, Y; split=> //; rewrite !mul1n expn1.
Qed.

Definition g233_universal_hyp_claim : Prop :=
  (forall n : nat, x233_max_density_at_most (g233_edgeless n) 2 1) /\
  (bounded_density_universal_graph_statement ->
     exists C : nat, forall n : nat, exists G : sgraph,
       edge_count G ^ 2 <= C ^ 2 * n ^ 3 /\ has_subgraph G (g233_edgeless n)).

Theorem g233_universal_hyp_inhabited : g233_universal_hyp_claim.
Proof.
have dens (n : nat) : x233_max_density_at_most (g233_edgeless n) 2 1.
  move=> S; have e0 : edge_count (induced S) = 0 by apply: g233_edge_count0 => x y.
  by rewrite e0.
split=> // h; have [C hC] := h 2 1 isT isT.
exists C => n; have [G [eG uG]] := hC n.
exists G; split; first exact: eG.
by apply: uG; [rewrite card_ord | exact: dens].
Qed.

(** The variant with G = K_n (trivially universal) is false: at d = 2, e(K_n)^2 = C(n,2)^2
    outgrows C^2 n^3 (n = 2k + 1, k = 2 C^2 + 1); it implies the row (K_n contains every
    n-vertex graph). *)
Definition g233_universal_complete : Prop :=
  forall a b : nat, 0 < b -> b < a ->
    exists C : nat, forall n : nat, edge_count 'K_n ^ a <= C ^ a * n ^ (2 * a - b).

Definition g233_universal_ntt_claim : Prop :=
  ~ g233_universal_complete /\ (g233_universal_complete -> bounded_density_universal_graph_statement).

Theorem g233_universal_not_trivially_true : g233_universal_ntt_claim.
Proof.
split.
- move=> h; have [C hC] := h 2 1 isT isT.
  have oddn : odd (2 * C ^ 2).+1.*2.+1 by rewrite /= odd_double.
  have := hC (2 * C ^ 2).+1.*2.+1.
  rewrite edge_count_Kn (bin2odd oddn) doubleK => le.
  by have := leq_ltn_trans le (g233_arith C); rewrite ltnn.
- move=> h a b b0 ba; have [C hC] := h a b b0 ba.
  exists C => n; exists 'K_n; split; first exact: hC.
  move=> H Hn _; apply/has_subgraphP.
  exists (fun x => cast_ord Hn (enum_rank x)); split.
  + by move=> x y /cast_ord_inj /enum_rank_inj.
  + move=> x y xy; have : x != y := negbT (sg_edgeNeq xy).
    apply: contra => /eqP e; apply/eqP; apply: enum_rank_inj; exact: cast_ord_inj e.
Qed.

Definition g233_rodl_hyp_claim : Prop :=
  [/\ hereditary_class (g233_small 4), ~ g233_small 4 ('K_5), x233_close (g233_small 4) 'K_1 0 1 &
      (polynomial_close_rodl_statement ->
         exists C : nat, exists S : {set 'K_1}, x233_homogeneous 1 3 S /\ 1 ^ C * #|'K_1| <= 3 ^ C * #|S|)].

Theorem g233_rodl_hyp_inhabited : g233_rodl_hyp_claim.
Proof.
have her := g233_small_hereditary 4.
have pr : ~ g233_small 4 ('K_5) := @g233_small_proper 4.
have cl : x233_close (g233_small 4) 'K_1 0 1.
  by apply: g233_close_self; rewrite /g233_small card_ord.
have pr2 : exists G0 : sgraph, ~ g233_small 4 G0 by exists ('K_5).
split=> // h; have [C [d [C0 d0 hC]]] := h _ her pr2.
exists C; apply: (hC 1 3 'K_1 isT isT).
by apply: g233_close_self; rewrite /g233_small card_ord.
Qed.

(** The variant with S = V(G) and C = d = 1 is false (F = graphs on at most 4 vertices,
    G = K_{2,2}, which is in F and not 1/4-homogeneous: density 4/6); it implies the row. *)
Definition g233_rodl_whole : Prop :=
  forall F : sgraph -> Prop, hereditary_class F -> (exists G0 : sgraph, ~ F G0) ->
    forall (a b : nat) (G : sgraph), 0 < a -> 2 * a < b ->
      x233_close F G a b -> x233_homogeneous a b [set: G].

Definition g233_rodl_ntt_claim : Prop :=
  ~ g233_rodl_whole /\ (g233_rodl_whole -> polynomial_close_rodl_statement).

Theorem g233_rodl_not_trivially_true : g233_rodl_ntt_claim.
Proof.
split.
- move=> h; apply: g233_K22_not_homogeneous.
  have pr2 : exists G0 : sgraph, ~ g233_small 4 G0 by exists ('K_5); exact: @g233_small_proper 4.
  apply: (h _ (g233_small_hereditary 4) pr2 1 4 _ isT isT).
  by apply: g233_close_self; rewrite /g233_small g233_KB_card.
- move=> h F her pr; exists 1, 1; split=> // a b G a0 h2; rewrite !expn1 => cl.
  have ab : a <= b := leq_trans (leq_pmull a (isT : 0 < 2)) (ltnW h2).
  exists [set: G]; split; first exact: h F her pr a b G a0 h2 cl.
  by rewrite cardsT leq_mul2r ab orbT.
Qed.

Definition g233_degree_hyp_claim : Prop :=
  [/\ hereditary_class (g233_small 2), x233_degree_bounded (g233_small 2) &
      (polynomial_degree_bounding_statement ->
         exists p : seq nat, 2 * edge_count 'K_2 <= #|'K_2| * horner_nat p (x233_biclique_number 'K_2))].

Theorem g233_degree_hyp_inhabited : g233_degree_hyp_claim.
Proof.
have her := g233_small_hereditary 2.
have db := g233_small2_degree_bounded.
split=> // h; have [p hp] := h _ her db.
by exists p; apply: hp; rewrite /g233_small card_ord.
Qed.

(** The variant with the zero polynomial (every hereditary degree-bounded class is edgeless)
    is false (graphs on at most 2 vertices: K_2 has 2 e = 2 > 0); it implies the row
    (p = [::]). *)
Definition g233_degree_zero : Prop :=
  forall F : sgraph -> Prop, hereditary_class F -> x233_degree_bounded F ->
    forall G : sgraph, F G -> 2 * edge_count G <= #|G| * horner_nat [::] (x233_biclique_number G).

Definition g233_degree_ntt_claim : Prop :=
  ~ g233_degree_zero /\ (g233_degree_zero -> polynomial_degree_bounding_statement).

Theorem g233_degree_not_trivially_true : g233_degree_ntt_claim.
Proof.
split.
- move=> h; have := h _ (g233_small_hereditary 2) g233_small2_degree_bounded 'K_2.
  by rewrite /g233_small card_ord edge_count_K2 horner_nat_nil muln0 => /(_ isT).
- by move=> h F her db; exists [::]; exact: h F her db.
Qed.

(** * Extremal.conjectures.grounding_X276 -- grounding certificates of wave X276.

    For each of the two rows: hyp_inhabited (the hypotheses hold on a concrete instance, and the statement gives
    its consequence there) and not_trivially_true in the contract form (a variant obtained from the body by
    deleting one hypothesis is false and implies the row).  X276.v has no local helper, so there is no
    helper_sanity certificate.
    - (k,r)-graphs: k = 4 meets 4 <= k, and the statement gives a 4-vertex-critical graph with no critical edge
      (r = 1).  Without 4 <= k the row is false at k = 2, r = 0: a 2-vertex-critical graph has an edge xy (chi = 2),
      and on n >= 3 vertices deleting a third vertex keeps xy, so chi stays 2.
    - Hajebi: K_1 is K_{1,1}-free (it has fewer vertices), and the statement gives a cover of K_1 at t = 1.
      Without K_{t,t}-freeness the row is false at t = 1: K_{n,n} is triangle-free, so a clique holds at most one
      vertex of each side and covering its n * n edges takes n * n cliques, while (n * n)^q <= C (2n)^(2q - 1)
      fails at n = C 2^(2q) + 1 (powers kept symbolic). *)

From Extremal.conjectures Require Import X276.
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Row 1 *)

Lemma g276_chi_edge (G : sgraph) (A : {set G}) (x y : G) :
  x \in A -> y \in A -> x -- y -> 2 <= χ(A).
Proof.
move=> xA yA xy; apply: leq_trans (omega_leq_chi A).
have K : [set x; y] \in cliques A.
  by rewrite inE subUset !sub1set xA yA /=; apply/cliqueP/clique2.
by have := clique_bound K; rewrite cards2 (sg_edgeNeq xy).
Qed.

Lemma g276_edge_of_chi (G : sgraph) : 2 <= χ([set: G]) -> exists x y : G, x -- y.
Proof.
move=> h; case: (boolP (stable [set: G])) => [st|/stablePn [x [y [_ _ xy]]]]; last by exists x, y.
by have := chiD1 [set: G] st; rewrite setDv chi0 => /(leq_trans h).
Qed.

Definition g276_kr_hyp_claim : Prop :=
  4 <= 4 /\
  (erdos_kr_graphs_unbounded_statement ->
     exists G : sgraph,
       [/\ χ([set: G]) = 4,
           forall v : G, χ([set: induced (~: [set v])]) < 4 &
           forall F : {set {set G}}, F \subset E(G) -> #|F| <= 1 -> 4 <= χ([set: del_edge_set G F])]).

Theorem g276_kr_hyp_inhabited : g276_kr_hyp_claim.
Proof.
split=> // h; have [n0 hn] := h 4 isT 1.
by have [G [_ HG]] := hn n0 (leqnn n0); exists G.
Qed.

Definition g276_kr_no_k_bound : Prop :=
  forall k r : nat, exists n0 : nat, forall n : nat, n0 <= n ->
    exists G : sgraph, #|G| = n /\
      [/\ χ([set: G]) = k,
          forall v : G, χ([set: induced (~: [set v])]) < k &
          forall F : {set {set G}}, F \subset E(G) -> #|F| <= r -> k <= χ([set: del_edge_set G F])].

Definition g276_kr_ntt_claim : Prop :=
  ~ g276_kr_no_k_bound /\ (g276_kr_no_k_bound -> erdos_kr_graphs_unbounded_statement).

Theorem g276_kr_not_trivially_true : g276_kr_ntt_claim.
Proof.
split; last by move=> h k _; exact: h k.
move=> h; have [n0 hn] := h 2 0.
have [G [cG [c2 crit _]]] := hn (n0 + 3) (leq_addr _ _).
have [x [y xy]] : exists x y : G, x -- y by apply: g276_edge_of_chi; rewrite c2.
have [v vxy] : exists v : G, v \notin [set x; y].
  case: (pickP (fun v : G => v \notin [set x; y])) => [v vn|none]; first by exists v.
  have sub : [set: G] \subset [set x; y].
    by apply/subsetP => w _; have := none w; rewrite /= => /negbFE.
  have := subset_leq_card sub; rewrite cardsT cG cards2.
  by case: (x != y); rewrite ?addn3 // ltnS ?leqn0.
have := crit v.
move: vxy; rewrite !inE negb_or => /andP [vx vy].
have xin : x \in [set~ v] by rewrite !inE eq_sym.
have yin : y \in [set~ v] by rewrite !inE eq_sym.
pose x' : induced [set~ v] := Sub x xin.
pose y' : induced [set~ v] := Sub y yin.
have xy' : x' -- y' by [].
by rewrite ltnNge (@g276_chi_edge _ _ x' y').
Qed.

(** ** Row 2 *)

Definition g276_hj_hyp_claim : Prop :=
  [/\ 1 <= 1, induced_free ('K_1) ('K_1,1) &
      (hajebi_ktt_free_subquadratic_clique_cover_statement ->
         exists q C : nat, 0 < q /\
           exists cover : {set {set ('K_1)}},
             [/\ forall A, A \in cover -> cliqueb A,
                 forall x y : ('K_1), x -- y -> exists2 A, A \in cover & (x \in A) && (y \in A) &
                 #|cover| ^ q <= C * #|'K_1| ^ (2 * q - 1)])].

Theorem g276_hj_hyp_inhabited : g276_hj_hyp_claim.
Proof.
have fr : induced_free ('K_1) ('K_1,1) by apply: induced_free_card; rewrite card_ord card_sum !card_ord.
split=> // h; have [q [C [q0 hq]]] := h 1 isT.
by exists q, C; split=> //; exact: hq _ fr.
Qed.

(** In K_{n,n} a clique holds at most one vertex of each side, so covering its n * n edges by cliques takes at
    least n * n of them. *)
Lemma g276_KB_cover (n : nat) (cover : {set {set ('K_n,n)}}) :
  (forall A, A \in cover -> cliqueb A) ->
  (forall x y : ('K_n,n), x -- y -> exists2 A, A \in cover & (x \in A) && (y \in A)) ->
  n * n <= #|cover|.
Proof.
move=> cl cov.
have ex (p : 'I_n * 'I_n) :
    exists A, [&& A \in cover, (inl p.1 : ('K_n,n)) \in A & (inr p.2 : ('K_n,n)) \in A].
  have [A Ac /andP [a b]] := cov (inl p.1) (inr p.2) isT.
  by exists A; rewrite Ac a b.
pose g p := xchoose (ex p).
have gP p : [/\ g p \in cover, (inl p.1 : ('K_n,n)) \in g p & (inr p.2 : ('K_n,n)) \in g p].
  by have /and3P [] := xchooseP (ex p).
have inj : injective g.
  move=> [i j] [i' j'] e; have [c1 a1 b1] := gP (i, j); have [_ a2 b2] := gP (i', j').
  rewrite /= e in a1 b1 c1; move: (cl _ c1) => /cliqueP K.
  have ei : i = i'.
    apply/eqP; apply: contraTT isT => ne; apply/negP => _.
    by have := K _ _ a1 a2; rewrite /= (inj_eq (@inl_inj _ _)) ne => /(_ isT).
  have ej : j = j'.
    apply/eqP; apply: contraTT isT => ne; apply/negP => _.
    by have := K _ _ b1 b2; rewrite /= (inj_eq (@inr_inj _ _)) ne => /(_ isT).
  by rewrite ei ej.
have sub : [set g p | p in [set: 'I_n * 'I_n]] \subset cover.
  by apply/subsetP => A /imsetP [p _ ->]; have [] := gP p.
by have := subset_leq_card sub; rewrite card_imset // cardsT card_prod card_ord.
Qed.

Definition g276_hj_no_free : Prop :=
  forall t : nat, 1 <= t -> exists q C : nat, 0 < q /\
    forall G : sgraph,
      exists cover : {set {set G}},
        [/\ forall A, A \in cover -> cliqueb A,
            forall x y : G, x -- y -> exists2 A, A \in cover & (x \in A) && (y \in A) &
            #|cover| ^ q <= C * #|G| ^ (2 * q - 1)].

Definition g276_hj_ntt_claim : Prop :=
  ~ g276_hj_no_free /\ (g276_hj_no_free -> hajebi_ktt_free_subquadratic_clique_cover_statement).

Theorem g276_hj_not_trivially_true : g276_hj_ntt_claim.
Proof.
split; last by move=> h t t1; have [q [C [q0 hq]]] := h t t1; exists q, C; split=> // G _; exact: hq.
move=> h; have [q [C [q0 hq]]] := h 1 isT.
pose n := (C * 2 ^ (2 * q)).+1.
have [cover [cl cov bnd]] := hq ('K_n,n).
have nn := g276_KB_cover cl cov.
have le : (n * n) ^ q <= C * (n + n) ^ (2 * q - 1).
  have cK : #|'K_n,n| = n + n by rewrite card_sum !card_ord.
  by rewrite -cK; apply: leq_trans _ bnd; rewrite leq_exp2r.
have e1 : 2 * q = (2 * q - 1).+1 by rewrite subn1 prednK // muln_gt0 q0.
move: le; set e := 2 * q - 1.
rewrite mulnn -expnM e1 expnS addnn -mul2n expnMn mulnA -/e [n * _]mulnC.
rewrite [C * 2 ^ e * _]mulnC leq_pmul2l ?expn_gt0 ?ltn0Sn //.
rewrite /n e1 -/e expnS ltnNge => /negP; apply.
by rewrite leq_mul2l leq_pmull ?orbT.
Qed.

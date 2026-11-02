(** * Chromatic.conjectures.grounding_X281 -- grounding certificates for wave X281 (2026-11-02)

    - erdos:1092.  hyp_inhabited at r = 2 on K_2: for every q, every nonempty vertex set meets the hypothesis with no
      deletion, since a graph on at most r vertices is r-colourable.  The statement gives its r = 2 instance (the
      page's f_2 question).  not_trivially_true drops the hypothesis on the subgraphs: that variant is false at r = 1
      (K_3) and implies the statement.  Teeth: for every fixed graph G the implication holds at any q > |G|
      ([g281_ehs_fixed_graph]: fewer than |S| / q < 1 deletions means none), so no single graph refutes the body; its
      content is that q does not depend on G.
    - erdos:627.  hyp_inhabited: a maximiser exists on 'I_n for every n ([g281_maximizer_exists], an arg max of the
      integer key chi (n! / omega)), and trunc_log 2 n is positive from n = 2.  The statement gives, at eps = 1, one
      maximiser of each of two orders beyond its N, with ratios within 1.  not_trivially_true: the Cauchy condition
      from N = 2 for every eps is false, and it implies the statement.  K_2 and K_3 are maximisers (chi <= omega on
      at most three vertices), with b(2) = 1/2 and b(3) = 1/3, and eps = 1/7.
    - arxiv:2402.04237#01.  hyp_inhabited: G(n, 1/2) has positive mass, the polynomial hypothesis holds at G' = G, and
      the statement forces a nonempty family.  not_trivially_true: the variant without the polynomial hypothesis asks
      every G' on the same vertex set to be isomorphic to G.  Its event fails for n >= 2 (the edgeless and the
      complete graph), so it is not whp, and it is the statement's event for the empty family.
    - helper_sanity for [x281_gen_chromatic_poly], listed in every row (gate_contracts.py l.273-275).
      pi^(K_1)_G(k) is the number of proper k-colourings (the chromatic polynomial, chromaticpolys.tex l.134).
      pi^(K_2) of K_1 is k (k - 1) / 2 = 'C(k, 2), which is 3 at k = 3 (the Mac's example, degree 2 > n = 1). *)

From GTBase Require Import base common finite_graph colourings.
From Chromatic.conjectures Require Import X281.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** erdos:1092 *************************************************************** *)

(* every nonempty vertex set of a graph with at most r vertices meets the hypothesis with no deletion *)
Lemma g281_small_hyp (r q : nat) (G : sgraph) : 0 < q -> #|G| <= r ->
  forall S : {set G}, S != set0 ->
    exists F : {set {set induced S}},
      [/\ F \subset E(induced S), χ([set: del_edge_set (induced S) F]) <= r & q * #|F| < #|S|].
Proof.
move=> q0 Gr S S0; exists set0; split.
- exact: sub0set.
- apply: leq_trans (leq_chi _) _; rewrite cardsT card_del_edge_set card_sig.
  exact: leq_trans (max_card _) Gr.
- by rewrite cards0 muln0 card_gt0.
Qed.

(** not_trivially_true for erdos:1092: without the hypothesis on the subgraphs the claim is false at r = 1
    (chi(K_3) = 3), and that variant implies the statement. *)
Definition g281_ehs_no_hyp : Prop :=
  forall r : nat, 1 <= r -> exists q : nat, 0 < q /\ forall G : sgraph, χ([set: G]) <= r.+1.

Definition g281_ehs_ntt_claim : Prop :=
  ~ g281_ehs_no_hyp /\ (g281_ehs_no_hyp -> erdos_hajnal_szemeredi_almost_r_chromatic_subgraphs_statement).

Theorem g281_ehs_not_trivially_true : g281_ehs_ntt_claim.
Proof.
split.
- move=> /(_ 1 (leqnn 1)) [q [_ /(_ 'K_3)]].
  have K3c : clique [set: 'K_3] by move=> x y _ _.
  by rewrite (chi_clique K3c) cardsT card_ord.
- move=> V r r1; have [q [q0 Vq]] := V r r1.
  by exists q; split=> // G _; exact: Vq.
Qed.

(* every graph meets the body at q > |G|: no fixed graph refutes it *)
Lemma g281_ehs_fixed_graph (r q : nat) (G : sgraph) : #|G| < q ->
  (forall S : {set G}, S != set0 ->
     exists F : {set {set induced S}},
       [/\ F \subset E(induced S), χ([set: del_edge_set (induced S) F]) <= r & q * #|F| < #|S|]) ->
  χ([set: G]) <= r.
Proof.
move=> Gq hyp.
have [G0|GN] := eqVneq [set: G] set0.
  by have := leq_chi [set: G]; rewrite G0 cards0 leqn0 => /eqP ->.
have [F [_ chiF qF]] := hyp _ GN.
have F0 : F = set0.
  apply/eqP; rewrite -cards_eq0; apply/negPn/negP => Fn.
  move: qF; rewrite cardsT; apply/negP; rewrite -leqNgt.
  by apply: leq_trans (ltnW Gq) _; rewrite leq_pmulr // lt0n.
subst F; rewrite -(chi_induced [set: G]).
pose g : induced [set: G] -> del_edge_set (induced [set: G]) set0 := fun x => x.
have gmono : {mono g : x y / x -- y >-> x -- y} by move=> x y; rewrite /g del_edge_set0.
pose j := @ISubgraph _ _ g (fun x y (e : g x = g y) => e) gmono.
have e := chi_isubgraph j [set: induced [set: G]].
have jT : [set j x | x in [set: induced [set: G]]] = [set: del_edge_set (induced [set: G]) set0].
  by apply/setP=> x; rewrite !inE; apply/imsetP; exists x.
by rewrite -chiT e jT.
Qed.

(** hyp_inhabited: 1 <= r at r = 2; K_2 meets the hypothesis for every q ([g281_small_hyp]); the statement gives
    its r = 2 instance, the page's f_2 question. *)
Definition g281_ehs_hyp_claim : Prop :=
  [/\ 1 <= 2,
      (forall q : nat, 0 < q -> forall S : {set 'K_2}, S != set0 ->
         exists F : {set {set induced S}},
           [/\ F \subset E(induced S), χ([set: del_edge_set (induced S) F]) <= 2 & q * #|F| < #|S|]) &
      (erdos_hajnal_szemeredi_almost_r_chromatic_subgraphs_statement ->
         exists q : nat, 0 < q /\ forall G : sgraph,
           (forall S : {set G}, S != set0 ->
              exists F : {set {set induced S}},
                [/\ F \subset E(induced S), χ([set: del_edge_set (induced S) F]) <= 2 & q * #|F| < #|S|]) ->
           χ([set: G]) <= 3)].

Theorem g281_ehs_hyp_inhabited : g281_ehs_hyp_claim.
Proof.
split=> //.
- by move=> q q0; apply: g281_small_hyp => //; rewrite card_ord.
- move=> /(_ 2 isT) [q [q0 hq]]; exists q; split=> // G; exact: hq.
Qed.


(** ** erdos:627 **************************************************************** *)

Lemma g281_chi_le_omega_small (H : sgraph) : #|H| <= 3 -> χ([set: H]) <= ω([set: H]).
Proof.
move=> H3.
have chiH : χ([set: H]) <= #|H| by rewrite -cardsT leq_chi.
have [wH|wlt] := leqP #|H| ω([set: H]); first exact: leq_trans chiH wH.
have H0 : [set: H] != set0 by rewrite -card_gt0 cardsT (leq_ltn_trans (leq0n _) wlt).
have w1 : 1 <= ω([set: H]) by rewrite lt0n omega_eq0.
have [/existsP [x /existsP [y xy]] | noedge] := boolP [exists x : H, [exists y : H, x -- y]]; last first.
  have pc : proper_colouring (fun _ : H => tt).
    apply/proper_colouringP => a b ab; move/negP: noedge; apply: contra_notN => _.
    by apply/existsP; exists a; apply/existsP; exists b.
  by apply: leq_trans (proper_colouring_chi pc) _; rewrite card_unit.
have w2 : 2 <= ω([set: H]).
  have xy' : x != y by rewrite (sg_edgeNeq xy).
  have c2 : #|[set x; y]| = 2 by rewrite cards2 xy'.
  rewrite -c2; apply: clique_bound.
  by rewrite inE subsetT /=; apply/cliqueP; exact: clique2.
have H3e : #|H| = 3 by apply/eqP; rewrite eqn_leq H3 (leq_trans _ wlt).
have [/existsP [u /existsP [v /andP [uv nuv]]] | cpl] :=
  boolP [exists u : H, [exists v : H, (u != v) && ~~ u -- v]]; last first.
  have cT : [set: H] \in cliques [set: H].
    rewrite inE subxx /=; apply/cliqueP => a b _ _ ab; apply/negPn/negP => nab.
    by move/negP: cpl; apply; apply/existsP; exists a; apply/existsP; exists b; rewrite ab.
  by have := clique_bound cT; rewrite cardsT leqNgt wlt.
have one : forall a b : H, a \notin [set u; v] -> b \notin [set u; v] -> a = b.
  have : #|~: [set u; v]| = 1 by rewrite cardsCs setCK H3e cards2 uv.
  move=> /eqP /cards1P [z zE] a b au bu.
  have : a \in ~: [set u; v] by rewrite inE.
  have : b \in ~: [set u; v] by rewrite inE.
  by rewrite zE !inE => /eqP -> /eqP ->.
pose col := fun w : H => (w == u) || (w == v).
have pc : proper_colouring col.
  apply/proper_colouringP => a b ab; rewrite /col.
  have ba : b -- a by rewrite sgP.
  case: (boolP ((a == u) || (a == v))) => ha; case: (boolP ((b == u) || (b == v))) => hb //=.
  - exfalso; move: ha hb ab ba.
    by case/orP => /eqP ->; case/orP => /eqP ->; rewrite ?sg_irrefl ?(negbTE nuv).
  - exfalso; have e : a = b by apply: one; rewrite !inE.
    by move: ab; rewrite e sg_irrefl.
apply: leq_trans (proper_colouring_chi pc) _.
by rewrite card_bool.
Qed.

Lemma g281_complete_lab (n : nat) (x y : fg_labelled_sgraph (fg_complete_edge_universe n)) :
  (x -- y) = (x != y).
Proof.
rewrite /edge_rel /= /fg_srel /fg_edge_set_rel /fg_complete_edge_universe.
rewrite !inE !cards2 eq_sym.
by case: eqP.
Qed.

Lemma g281_complete_chi_omega (n : nat) :
  χ([set: fg_labelled_sgraph (fg_complete_edge_universe n)]) = n /\
  ω([set: fg_labelled_sgraph (fg_complete_edge_universe n)]) = n.
Proof.
have cT : clique [set: fg_labelled_sgraph (fg_complete_edge_universe n)].
  by move=> x y _ _ xy; rewrite g281_complete_lab.
have chiT : χ([set: fg_labelled_sgraph (fg_complete_edge_universe n)]) = n.
  by rewrite (chi_clique cT) cardsT card_ord.
split=> //; apply/eqP; rewrite eqn_leq; apply/andP; split.
  by apply: leq_trans (omega_leq_chi _) _; rewrite chiT.
have cl : [set: fg_labelled_sgraph (fg_complete_edge_universe n)]
            \in cliques [set: fg_labelled_sgraph (fg_complete_edge_universe n)].
  by rewrite inE subxx /=; apply/cliqueP.
by have := clique_bound cl; rewrite cardsT card_ord.
Qed.

Lemma g281_maximizer_exists (n : nat) : exists E1 : {set {set 'I_n}},
  forall E : {set {set 'I_n}},
    χ([set: fg_labelled_sgraph E]) * ω([set: fg_labelled_sgraph E1])
      <= χ([set: fg_labelled_sgraph E1]) * ω([set: fg_labelled_sgraph E]).
Proof.
case: n => [|n].
  (* no vertex: omega is 0 everywhere; rewrites are kept local (unification would evaluate chi on 'I_0) *)
  exists set0 => E.
  have z (E' : {set {set 'I_0}}) : ω([set: fg_labelled_sgraph E']) = 0.
    by apply/eqP; rewrite omega_eq0; apply/eqP/setP => -[].
  rewrite (z set0) (z E) [X in X <= _]muln0.
  exact: (leq0n (χ([set: fg_labelled_sgraph (set0 : {set {set 'I_0}})]) * 0)).
pose c (E : {set {set 'I_n.+1}}) := χ([set: fg_labelled_sgraph E]).
pose w (E : {set {set 'I_n.+1}}) := ω([set: fg_labelled_sgraph E]).
have wle (E : {set {set 'I_n.+1}}) : w E <= n.+1.
  apply: leq_trans (omega_leq_chi _) _; apply: leq_trans (leq_chi _) _.
  by rewrite cardsT card_ord.
have wpos (E : {set {set 'I_n.+1}}) : 0 < w E.
  rewrite lt0n /w omega_eq0; apply/set0Pn; exists ord0; exact: in_setT.
have wdvd (E : {set {set 'I_n.+1}}) : w E %| n.+1`! by rewrite dvdn_fact // wpos wle.
(* chi / omega compared through the integer key chi * (n! / omega) *)
pose key (E : {set {set 'I_n.+1}}) := c E * (n.+1`! %/ w E).
case: (@arg_maxnP _ set0 xpredT key isT) => E1 _ maxE1.
exists E1 => E; have kE := maxE1 E isT.
change (c E * w E1 <= c E1 * w E).
have dE := divnK (wdvd E).
have d1 := divnK (wdvd E1).
have F0 := fact_gt0 n.+1.
move: kE dE d1 F0; rewrite /key /geq /=.
move: (c E) (c E1) (w E) (w E1) (n.+1`!) => a b x y F kE dE d1 F0.
rewrite -(@leq_pmul2r F) //.
have L : a * y * F = a * (F %/ x) * (x * y).
  by rewrite -{1}dE mulnA [RHS]mulnA (mulnAC a y) (mulnAC (a * _) y).
have R : b * x * F = b * (F %/ y) * (x * y).
  by rewrite -{1}d1 mulnA [RHS]mulnA (mulnAC b x).
by rewrite L R leq_mul2r kE orbT.
Qed.

(** hyp_inhabited: a maximiser exists on 'I_n for every n; trunc_log 2 n is positive from n = 2; the statement at
    eps = 1 gives, for any two orders beyond its N, a maximiser of each with ratios within 1. *)
Definition g281_ratio_hyp_claim : Prop :=
  [/\ forall n : nat, exists E1 : {set {set 'I_n}}, forall E : {set {set 'I_n}},
        χ([set: fg_labelled_sgraph E]) * ω([set: fg_labelled_sgraph E1])
          <= χ([set: fg_labelled_sgraph E1]) * ω([set: fg_labelled_sgraph E]),
      forall n : nat, 2 <= n -> 0 < trunc_log 2 n &
      (chi_over_omega_max_ratio_limit_exists_statement ->
         exists N : nat, 2 <= N /\ forall n1 n2 : nat, N <= n1 -> N <= n2 ->
           exists (E1 : {set {set 'I_n1}}) (E2 : {set {set 'I_n2}}),
             let G1 := fg_labelled_sgraph E1 in let G2 := fg_labelled_sgraph E2 in
             χ([set: G1]) * trunc_log 2 n1 ^ 2 * (ω([set: G2]) * n2)
               < χ([set: G2]) * trunc_log 2 n2 ^ 2 * (ω([set: G1]) * n1) + ω([set: G1]) * n1 * (ω([set: G2]) * n2))].

Theorem g281_ratio_hyp_inhabited : g281_ratio_hyp_claim.
Proof.
split; [exact: g281_maximizer_exists | by move=> n n2; rewrite trunc_log_gt0 |].
move=> /(_ 1 1 isT isT) [N [N2 hN]]; exists N; split=> // n1 n2 Nn1 Nn2.
have [E1 m1] := g281_maximizer_exists n1.
have [E2 m2] := g281_maximizer_exists n2.
exists E1, E2; have [h _] := hN n1 n2 E1 E2 Nn1 Nn2 m1 m2.
by move: h; rewrite !mul1n.
Qed.

(** not_trivially_true for erdos:627: the Cauchy condition from N = 2 for every eps (all ratios from n = 2 equal)
    is false (K_2 and K_3 at eps = 1/7), and it implies the statement (N = 2). *)
Definition g281_ratio_uniform : Prop :=
  forall p q : nat, 0 < p -> 0 < q ->
    forall (n1 n2 : nat) (E1 : {set {set 'I_n1}}) (E2 : {set {set 'I_n2}}), 2 <= n1 -> 2 <= n2 ->
      let G1 := fg_labelled_sgraph E1 in let G2 := fg_labelled_sgraph E2 in
      (forall E : {set {set 'I_n1}},
         χ([set: fg_labelled_sgraph E]) * ω([set: G1]) <= χ([set: G1]) * ω([set: fg_labelled_sgraph E])) ->
      (forall E : {set {set 'I_n2}},
         χ([set: fg_labelled_sgraph E]) * ω([set: G2]) <= χ([set: G2]) * ω([set: fg_labelled_sgraph E])) ->
      q * (χ([set: G1]) * trunc_log 2 n1 ^ 2 * (ω([set: G2]) * n2))
        < q * (χ([set: G2]) * trunc_log 2 n2 ^ 2 * (ω([set: G1]) * n1))
          + p * (ω([set: G1]) * n1 * (ω([set: G2]) * n2)) /\
      q * (χ([set: G2]) * trunc_log 2 n2 ^ 2 * (ω([set: G1]) * n1))
        < q * (χ([set: G1]) * trunc_log 2 n1 ^ 2 * (ω([set: G2]) * n2))
          + p * (ω([set: G1]) * n1 * (ω([set: G2]) * n2)).

Definition g281_ratio_ntt_claim : Prop :=
  ~ g281_ratio_uniform /\ (g281_ratio_uniform -> chi_over_omega_max_ratio_limit_exists_statement).

Theorem g281_ratio_not_trivially_true : g281_ratio_ntt_claim.
Proof.
split; last first.
  by move=> V p q p0 q0; exists 2; split=> // n1 n2 E1 E2 N1 N2; exact: V.
move=> V.
have mx (n : nat) : n <= 3 -> forall E : {set {set 'I_n}},
    χ([set: fg_labelled_sgraph E]) * ω([set: fg_labelled_sgraph (fg_complete_edge_universe n)])
      <= χ([set: fg_labelled_sgraph (fg_complete_edge_universe n)]) * ω([set: fg_labelled_sgraph E]).
  move=> n3 E; have [-> ->] := g281_complete_chi_omega n.
  rewrite mulnC leq_mul2l; apply/orP; right.
  by apply: g281_chi_le_omega_small; rewrite card_ord.
have t2 : trunc_log 2 2 = 1 by [].
have t3 : trunc_log 2 3 = 1 by [].
have := V 1 7 isT isT 2 3 (fg_complete_edge_universe 2) (fg_complete_edge_universe 3) isT isT
  (mx 2 isT) (mx 3 isT).
case=> h _; move: h.
(* generalize chi and omega of K_2 and K_3 before computing (unification would evaluate them) *)
have [c2 w2] := g281_complete_chi_omega 2.
have [c3 w3] := g281_complete_chi_omega 3.
move: c2 w2 c3 w3.
move: (χ([set: fg_labelled_sgraph (fg_complete_edge_universe 2)]))
  (ω([set: fg_labelled_sgraph (fg_complete_edge_universe 2)])).
move: (χ([set: fg_labelled_sgraph (fg_complete_edge_universe 3)]))
  (ω([set: fg_labelled_sgraph (fg_complete_edge_universe 3)])).
move=> a b c d -> -> -> ->.
by rewrite t2 t3.
Qed.


(** ** arxiv:2402.04237#01 ******************************************************* *)

Lemma g281_gnp_half_total_pos (n : nat) : 0 < fg_total_weight (@fg_gnp_weight 1 2 n).
Proof.
rewrite /fg_total_weight (bigD1 set0) //=.
apply: (leq_trans _ (leq_addr _ _)).
by rewrite /fg_gnp_weight /fg_valid_labelled_edges sub0set cards0 /= !exp1n.
Qed.

(* an event that fails at every order n >= 2 is not whp in G(n, 1/2) *)
Lemma g281_whp_fails (P : forall n : nat, pred {set {set 'I_n}}) :
  (forall (n : nat) (E : {set {set 'I_n}}), 2 <= n -> ~~ P n E) ->
  ~ @fg_whp (fun n : nat => {set {set 'I_n}}) (fun n => @fg_gnp_weight 1 2 n) P.
Proof.
move=> nP /(_ 1 2 isT isT) [N hN].
have [pos ge] := hN (maxn N 2) (leq_maxl _ _).
have e0 : fg_event_weight (@fg_gnp_weight 1 2 (maxn N 2)) (P (maxn N 2)) = 0.
  rewrite /fg_event_weight big_pred0 // => E; apply/negbTE/nP; exact: leq_maxr.
by move: ge; rewrite e0 muln0 mul1n leqn0 => /eqP z; move: pos; rewrite z.
Qed.

Lemma g281_whp_ext (P Q : forall n : nat, pred {set {set 'I_n}}) :
  (forall (n : nat) (E : {set {set 'I_n}}), P n E = Q n E) ->
  @fg_whp (fun n : nat => {set {set 'I_n}}) (fun n => @fg_gnp_weight 1 2 n) P ->
  @fg_whp (fun n : nat => {set {set 'I_n}}) (fun n => @fg_gnp_weight 1 2 n) Q.
Proof.
move=> e h a b a0 ab; have [N hN] := h a b a0 ab; exists N => n Nn.
have [t1 t2] := hN n Nn; split=> //.
by rewrite /fg_event_weight -(eq_bigl _ _ (e n)).
Qed.

(* on n >= 2 vertices, not every labelled graph is isomorphic to a given one (edgeless versus complete) *)
Lemma g281_not_all_iso (n : nat) (E : {set {set 'I_n}}) : 2 <= n ->
  ~~ [forall E' : {set {set 'I_n}}, [exists f : {ffun 'I_n -> 'I_n}, injectiveb f && [forall x : 'I_n, [forall y : 'I_n,
        @edge_rel (fg_labelled_sgraph E') x y == @edge_rel (fg_labelled_sgraph E) (f x) (f y)]]]].
Proof.
move=> n2; apply/negP => /forallP h.
have /existsP [f /andP [/injectiveP finj /forallP f0]] := h set0.
have /existsP [g /andP [_ /forallP g1]] := h (fg_complete_edge_universe n).
pose x0 : 'I_n := Ordinal (ltnW n2).
pose x1 : 'I_n := Ordinal n2.
have gE : @edge_rel (fg_labelled_sgraph E) (g x0) (g x1).
  by move: (g1 x0) => /forallP /(_ x1) /eqP <-; rewrite g281_complete_lab.
have [fi fK fiK] := injF_bij finj.
move: (f0 (fi (g x0))) => /forallP /(_ (fi (g x1))) /eqP.
rewrite !fiK gE.
by rewrite /edge_rel /= /fg_srel /fg_edge_set_rel !inE andbF.
Qed.

(** not_trivially_true for arxiv:2402.04237#01: without the polynomial hypothesis every G' on the vertex set of G
    would be isomorphic to G, which fails for n >= 2, so the variant is false; it is the statement's event for the
    empty family, so it implies the statement. *)
Definition g281_pcr_no_polynomials : Prop :=
  @fg_whp (fun n : nat => {set {set 'I_n}}) (fun n => @fg_gnp_weight 1 2 n)
    (fun n E => [forall E' : {set {set 'I_n}},
       [exists f : {ffun 'I_n -> 'I_n}, injectiveb f && [forall x : 'I_n, [forall y : 'I_n,
          @edge_rel (fg_labelled_sgraph E') x y == @edge_rel (fg_labelled_sgraph E) (f x) (f y)]]]]).

Definition g281_pcr_ntt_claim : Prop :=
  ~ g281_pcr_no_polynomials /\
  (g281_pcr_no_polynomials -> generalised_chromatic_polynomials_determine_almost_every_graph_statement).

Theorem g281_pcr_not_trivially_true : g281_pcr_ntt_claim.
Proof.
split.
  by apply: g281_whp_fails => n E n2; exact: g281_not_all_iso.
(* the empty family: the polynomial hypothesis is vacuous, the event is the variant's *)
move=> V; exists 0, (fun _ => 'K_1); apply: g281_whp_ext V => n E.
apply: eq_forallb => E'.
apply/idP/idP => [h|]; first by apply/implyP.
by move/implyP; apply; apply/forallP => -[].
Qed.

(** hyp_inhabited: G(n, 1/2) has positive mass; the polynomial hypothesis holds at G' = G; the statement forces a
    nonempty family. *)
Definition g281_pcr_hyp_claim : Prop :=
  [/\ forall n : nat, 0 < fg_total_weight (@fg_gnp_weight 1 2 n),
      forall (t : nat) (Hs : 'I_t -> sgraph) (n : nat) (E : {set {set 'I_n}}) (i : 'I_t) (k : nat),
        x281_gen_chromatic_poly (fg_labelled_sgraph E) (Hs i) k
          == x281_gen_chromatic_poly (fg_labelled_sgraph E) (Hs i) k &
      (generalised_chromatic_polynomials_determine_almost_every_graph_statement ->
         exists (t : nat) (Hs : 'I_t -> sgraph), 0 < t)].

Theorem g281_pcr_hyp_inhabited : g281_pcr_hyp_claim.
Proof.
split; [exact: g281_gnp_half_total_pos | by move=> *; exact: eqxx |].
move=> [[|t] [Hs W]]; last by exists t.+1, Hs.
(* the empty family would make the event "every G' is isomorphic to G", which fails for n >= 2 *)
exfalso; apply: (g281_whp_fails _ W) => n E n2.
apply/negP => /forallP h; move/negP: (g281_not_all_iso E n2); apply.
by apply/forallP => E'; move/implyP: (h E'); apply; apply/forallP => -[].
Qed.


(** ** helper_sanity: x281_gen_chromatic_poly *************************************** *)

Lemma g281_gcp_K1 (G : sgraph) (k : nat) :
  x281_gen_chromatic_poly G 'K_1 k
    = #|[set c : {ffun G -> 'I_k} | [forall x : G, [forall y : G, (x -- y) ==> (c x != c y)]]]|.
Proof.
rewrite /x281_gen_chromatic_poly -[RHS](card_imset _ (@set1_inj _)).
apply: eq_card => S; rewrite !inE.
apply/andP/imsetP.
- case=> /forall_inP Spr /existsP [f /and3P [_ /eqP SE _]].
  exists (f ord0); first by rewrite inE Spr // SE; apply/imsetP; exists ord0.
  rewrite SE; apply/setP => c; rewrite !inE; apply/imsetP/eqP => [[x _ ->]|->]; last by exists ord0.
  by rewrite (ord1 x).
- case=> c; rewrite inE => cpr ->; split.
    by apply/forall_inP => c'; rewrite inE => /eqP ->.
  apply/existsP; exists [ffun _ => c]; apply/and3P; split.
  + by apply/injectiveP => x y _; rewrite (ord1 x) (ord1 y).
  + apply/eqP/setP => c'; rewrite !inE; apply/eqP/imsetP => [->|[x _ ->]]; last by rewrite ffunE.
    by exists ord0; rewrite ?ffunE.
  + apply/forallP => x; apply/forallP => y; rewrite (ord1 x) (ord1 y) sg_irrefl !ffunE.
    by rewrite (_ : [set v | c v != c v] = set0) ?cards0 //; apply/setP => v; rewrite !inE eqxx.
Qed.

Lemma g281_gcp_K1_K2 (k : nat) : x281_gen_chromatic_poly 'K_1 'K_2 k = 'C(k, 2).
Proof.
have -> : 'C(k, 2) = #|[set A : {set {ffun 'K_1 -> 'I_k}} | #|A| == 2]|.
  by rewrite card_draws card_ffun !card_ord expn1.
have cardK1 (P : pred 'K_1) : #|[set v | P v]| = P ord0.
  case: (boolP (P ord0)) => h.
    rewrite (_ : [set v | P v] = [set: 'K_1]) ?cardsT ?card_ord //.
    by apply/setP => v; rewrite (ord1 v) !inE h.
  rewrite (_ : [set v | P v] = set0) ?cards0 //.
  by apply/setP => v; rewrite (ord1 v) !inE (negbTE h).
have o (z : 'K_2) : z != ord0 -> z = ord_max.
  by case: z => -[|[|m]] //= p _; apply/val_inj.
rewrite /x281_gen_chromatic_poly; apply: eq_card => S; rewrite !inE.
apply/andP/idP.
  by case=> _ /existsP [f /and3P [/injectiveP fi /eqP -> _]]; rewrite card_imset // card_ord.
move=> /cards2P [c1 [c2 [c12 ->]]]; split.
  by apply/forall_inP => c _; apply/forallP => x; apply/forallP => y; rewrite (ord1 x) (ord1 y) sg_irrefl.
have c12' : c1 ord0 != c2 ord0.
  apply/negP => /eqP e; move/negP: c12; apply; apply/eqP/ffunP => v; by rewrite (ord1 v) e.
apply/existsP; exists [ffun x : 'K_2 => if x == ord0 then c1 else c2]; apply/and3P; split.
- apply/injectiveP => x y; rewrite !ffunE.
  case: (x =P ord0) => [->|/eqP x0]; case: (y =P ord0) => [->|/eqP y0] // e.
  + by move: c12; rewrite e eqxx.
  + by move: c12; rewrite e eqxx.
  + by rewrite (o _ x0) (o _ y0).
- apply/eqP/setP => c; rewrite !inE; apply/orP/imsetP => [[/eqP ->|/eqP ->]|[x _ ->]].
  + by exists ord0; rewrite ?ffunE.
  + by exists ord_max; rewrite ?ffunE.
  + by rewrite ffunE; case: (x == ord0); [left | right].
- apply/forallP => x; apply/forallP => y; rewrite cardK1 !ffunE.
  case: (x =P ord0) => [->|/eqP x0]; case: (y =P ord0) => [->|/eqP y0].
  + by rewrite eqxx sg_irrefl.
  + by rewrite (o _ y0) /= (negbTE c12').
  + by rewrite (o _ x0) [c2 ord0 == _]eq_sym (negbTE c12').
  + by rewrite (o _ x0) (o _ y0) eqxx sg_irrefl.
Qed.

(** helper_sanity: pi^(K_1)_G(k) is the number of proper k-colourings (the chromatic polynomial), and pi^(K_2) of
    K_1 is 'C(k, 2), 3 at k = 3. *)
Definition g281_gcp_helper_claim : Prop :=
  [/\ forall (G : sgraph) (k : nat), x281_gen_chromatic_poly G 'K_1 k
        = #|[set c : {ffun G -> 'I_k} | [forall x : G, [forall y : G, (x -- y) ==> (c x != c y)]]]|,
      forall k : nat, x281_gen_chromatic_poly 'K_1 'K_2 k = 'C(k, 2) &
      x281_gen_chromatic_poly 'K_1 'K_2 3 = 3].

Theorem g281_gcp_helper_sanity : g281_gcp_helper_claim.
Proof. by split; [exact: g281_gcp_K1 | exact: g281_gcp_K1_K2 | rewrite g281_gcp_K1_K2]. Qed.

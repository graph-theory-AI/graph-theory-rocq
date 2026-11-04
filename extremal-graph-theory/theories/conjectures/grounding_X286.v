(** * Extremal.conjectures.grounding_X286 -- grounding certificates of wave X286.

    For each of the two rows: hyp_inhabited (the hypotheses hold on a concrete instance, and the statement gives its
    consequence there) and not_trivially_true in the contract form (a variant obtained from the body by deleting one
    hypothesis or alternative is false and implies the row); one helper_sanity covers both helpers and is cited in
    both rows.
    - Helpers: the 4-cycle on 'I_4 (edges between the odd and the even vertices) has as edge set the biclique edges of
      its two parity classes; it is partitioned by one biclique and by none of zero.
    - Erdos #615: K_N has at least N^2 / 8 edges from N = 2 on, and a graph with n^2 <= 8 |E(G)| meets the edge
      hypothesis for every m; the statement then gives every large such graph a K_4 or the independent set.  Without
      the K_4 alternative the row is false at K_N, N = max(n0, 2): its stable sets have at most one vertex, and the
      bound at k = 1 asks 2^N <= N.
    - Erdos #807: G(n, 1/2) has positive total weight, the edgeless graph meets the event (alpha = n, no edge to
      cover), and the statement gives a positive event weight for all large n.  With the probability dropped (the
      event for every labelled graph) the row is false at the 4-cycle, one biclique while n - alpha >= 2. *)

From Extremal.conjectures Require Import X286.
From GTBase Require Import base finite_graph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The helpers on the 4-cycle *)

(** The labelled cycle C_4 = K_(2,2) on 'I_4: its edges join the odd vertices to the even ones. *)
Definition g286_odd : {set 'I_4} := [set x : 'I_4 | odd x].
Definition g286_even : {set 'I_4} := [set x : 'I_4 | ~~ odd x].
Definition g286_C4_edges : {set {set 'I_4}} := [set [set a; b] | a in g286_odd, b in g286_even].
Definition g286_C4 : sgraph := fg_labelled_sgraph g286_C4_edges.

Lemma g286_card_odd : #|g286_odd| = 2.
Proof.
have -> : g286_odd = [set (Ordinal (isT : 1 < 4)); (Ordinal (isT : 3 < 4))].
  by apply/setP => -[[|[|[|[|m]]]] lm] //=; rewrite !inE.
by rewrite cards2.
Qed.

Lemma g286_card_even : #|g286_even| = 2.
Proof.
have -> : g286_even = [set (Ordinal (isT : 0 < 4)); (Ordinal (isT : 2 < 4))].
  by apply/setP => -[[|[|[|[|m]]]] lm] //=; rewrite !inE.
by rewrite cards2.
Qed.

Lemma g286_C4_adj (x y : g286_C4) : odd (x : 'I_4) != odd (y : 'I_4) -> x -- y.
Proof.
move=> xy; rewrite /edge_rel /= /fg_srel /fg_edge_set_rel.
have -> /= : x != y by apply/eqP => e; move: xy; rewrite e eqxx.
case ox: (odd (x : 'I_4)); move: xy; rewrite ox => oy.
  by apply/orP; left; apply/imset2P; exists x y; rewrite // inE; move: oy; case: (odd _).
by apply/orP; right; apply/imset2P; exists y x; rewrite // inE ?ox; move: oy; case: (odd _).
Qed.

Lemma g286_C4_edge (x y : g286_C4) : x -- y -> [set x; y] \in g286_C4_edges.
Proof. by case/andP => _ /orP [//|h]; rewrite setUC. Qed.

Lemma g286_C4_E : E(g286_C4) = x286_biclique_edges (g286_odd : {set g286_C4}) g286_even.
Proof.
apply/setP => e; rewrite in_sg_edge_set; apply/existsP/imset2P.
  by move=> [x /existsP [y /andP [xy /eqP ->]]]; exact/imset2P/g286_C4_edge.
move=> [a b aO bE ->]; exists a; apply/existsP; exists b; rewrite eqxx andbT.
by apply: g286_C4_adj; move: aO bE; rewrite !inE => -> ->.
Qed.

Lemma g286_C4_partition1 : x286_biclique_partition g286_C4 1.
Proof.
apply/existsP; exists [ffun _ => ((g286_odd : {set g286_C4}), (g286_even : {set g286_C4}))].
apply/and3P; split.
- apply/forallP => i; rewrite ffunE /= -g286_C4_E subxx andbT.
  by rewrite -setI_eq0; apply/eqP/setP => x; rewrite !inE; case: (odd _).
- by apply/forallP => i; apply/forallP => j; rewrite (ord1 i) (ord1 j) eqxx.
- by rewrite big_ord1 ffunE /= -g286_C4_E.
Qed.

Lemma g286_partition0 (G : sgraph) : E(G) != set0 -> ~~ x286_biclique_partition G 0.
Proof.
move=> En; apply/existsP => -[AB /and3P [_ _]].
by rewrite big_ord0 subset0 (negbTE En).
Qed.

Lemma g286_C4_E_neq0 : E(g286_C4) != set0.
Proof.
apply/set0Pn; exists [set (Ordinal (isT : 1 < 4)); (Ordinal (isT : 0 < 4))]; rewrite g286_C4_E.
by apply/imset2P; exists (Ordinal (isT : 1 < 4)) (Ordinal (isT : 0 < 4)); rewrite ?inE.
Qed.

Lemma g286_C4_alpha : α([set: g286_C4]) <= 2.
Proof.
rewrite /alpha_mem; apply/bigmax_leqP => S /stabsetsP [_ /stableP st].
have [/existsP [x /andP [xS ox]] | no] := boolP [exists x in S, odd (x : 'I_4)].
  apply: leq_trans (subset_leq_card (_ : S \subset (g286_odd : {set g286_C4}))) _; last by rewrite g286_card_odd.
  apply/subsetP => y yS; rewrite inE; apply/negPn/negP => ey.
  by case/negP: (st x y xS yS); apply: g286_C4_adj; rewrite ox (negbTE ey).
apply: leq_trans (subset_leq_card (_ : S \subset (g286_even : {set g286_C4}))) _; last by rewrite g286_card_even.
apply/subsetP => y yS; rewrite inE; apply/negP => oy.
by move/negP: no; apply; apply/existsP; exists y; rewrite yS oy.
Qed.

(** helper_sanity: on C_4 the bicliques odd / even give the whole edge set, so it is one biclique and not zero. *)
Definition g286_helper_claim : Prop :=
  [/\ E(g286_C4) = x286_biclique_edges (g286_odd : {set g286_C4}) g286_even,
      x286_biclique_partition g286_C4 1 & ~~ x286_biclique_partition g286_C4 0].

Theorem g286_helper_sanity : g286_helper_claim.
Proof. by split; [exact: g286_C4_E | exact: g286_C4_partition1 | exact: g286_partition0 g286_C4_E_neq0]. Qed.

(** ** Row 1: erdos:615 *)

(** K_N has at least N^2 / 8 edges from N = 2 on: 8 'C(N, 2) = 4 N (N - 1). *)
Lemma g286_Kn_dense (N : nat) : 2 <= N -> N ^ 2 <= 8 * #|E('K_N)|.
Proof.
case: N => [|[|n]] // _; rewrite card_edge_Kn bin2.
have e : ((n.+2 * n.+1)./2).*2 = n.+2 * n.+1 by rewrite halfK oddM /= andNb subn0.
rewrite /= -[8]/(4 * 2) -mulnA mul2n e -mulnn mulnCA leq_pmul2l //.
by rewrite mulnS -addn2 addnC leq_add // leq_pmull.
Qed.

(** n^2 <= 8 |E(G)| gives the edge hypothesis for every m. *)
Lemma g286_dense_hyp (m : nat) (G : sgraph) :
  #|G| ^ 2 <= 8 * #|E(G)| -> m * #|G| ^ 2 <= 8 * (m * #|E(G)| + #|G| ^ 2).
Proof.
move=> h; rewrite mulnDr; apply: leq_trans (leq_addr _ _).
by rewrite mulnCA leq_mul2l h orbT.
Qed.

(** A stable set of K_N has at most one vertex. *)
Lemma g286_Kn_stable (N : nat) (S : {set 'K_N}) : stable S -> #|S| <= 1.
Proof.
move/stableP => st; apply/card_le1_eqP => x y xS yS; apply/eqP/negPn/negP => xy.
by move: (st x y xS yS); rewrite /edge_rel /= eq_sym xy.
Qed.

Definition g286_e615_hyp_claim : Prop :=
  [/\ forall N : nat, 2 <= N -> #|'K_N| ^ 2 <= 8 * #|E('K_N)|,
      forall (m : nat) (G : sgraph), #|G| ^ 2 <= 8 * #|E(G)| -> m * #|G| ^ 2 <= 8 * (m * #|E(G)| + #|G| ^ 2) &
      (erdos_615_k4_or_large_independent_set_statement ->
         exists n0 : nat, forall G : sgraph, n0 <= #|G| -> #|G| ^ 2 <= 8 * #|E(G)| ->
           has_subgraph G 'K_4 \/ exists2 S : {set G}, stable S &
             forall k : nat, 0 < k -> k.+1 ^ (k * #|G|) <= k ^ (k * #|G|) * #|G| ^ #|S|)].

Theorem g286_e615_hyp_inhabited : g286_e615_hyp_claim.
Proof.
split; first by move=> N; rewrite card_ord; exact: g286_Kn_dense.
  exact: g286_dense_hyp.
move=> [m [n0 h]]; exists n0 => G nG d; exact: h nG (g286_dense_hyp m d).
Qed.

(** not_trivially_true: without the K_4 alternative the claim fails at K_N, N = max(n0, 2): it meets the edge
    hypothesis for every m, its stable sets have at most one vertex, and the bound at k = 1 asks 2^N <= N. *)
Definition g286_e615_no_K4 : Prop :=
  exists m n0 : nat, forall G : sgraph, n0 <= #|G| ->
    m * #|G| ^ 2 <= 8 * (m * #|E(G)| + #|G| ^ 2) ->
    exists2 S : {set G}, stable S &
      forall k : nat, 0 < k -> k.+1 ^ (k * #|G|) <= k ^ (k * #|G|) * #|G| ^ #|S|.

Definition g286_e615_ntt_claim : Prop :=
  ~ g286_e615_no_K4 /\ (g286_e615_no_K4 -> erdos_615_k4_or_large_independent_set_statement).

Theorem g286_e615_not_trivially_true : g286_e615_ntt_claim.
Proof.
split; last by move=> [m [n0 h]]; exists m, n0 => G nG hE; right; exact: h.
move=> [m [n0 h]]; pose N := maxn n0 2.
have N2 : 2 <= N := leq_maxr _ _.
have nN : n0 <= #|'K_N| by rewrite card_ord leq_maxl.
have dN : #|'K_N| ^ 2 <= 8 * #|E('K_N)| by rewrite card_ord; exact: g286_Kn_dense.
have [S st] := h ('K_N) nN (g286_dense_hyp m dN).
rewrite card_ord => le.
have := le 1 isT; rewrite mul1n exp1n mul1n => {}le.
have := leq_trans le (leq_pexp2l (leq_trans (isT : 0 < 2) N2) (g286_Kn_stable st)).
by rewrite expn1 leqNgt ltn_expl.
Qed.

(** ** Row 2: erdos:807 *)

(** The event of erdos:807 at order n: tau(G) = n - alpha(G). *)
Definition g286_e807_event (n : nat) (E : {set {set 'I_n}}) : bool :=
  x286_biclique_partition (fg_labelled_sgraph E) (n - α([set: fg_labelled_sgraph E]))
  && [forall k : 'I_(n - α([set: fg_labelled_sgraph E])), ~~ x286_biclique_partition (fg_labelled_sgraph E) k].

Lemma g286_e807E :
  erdos_807_bipartition_number_random_graph_statement =
  @fg_whp (fun n : nat => {set {set 'I_n}}) (fun n => @fg_gnp_weight 1 2 n) g286_e807_event.
Proof. by []. Qed.

Lemma g286_gnp_half_total_pos (n : nat) : 0 < fg_total_weight (@fg_gnp_weight 1 2 n).
Proof.
rewrite /fg_total_weight (bigD1 set0) //=.
apply: (leq_trans _ (leq_addr _ _)).
by rewrite /fg_gnp_weight /fg_valid_labelled_edges sub0set cards0 /= !exp1n.
Qed.

(** The edgeless graph meets the event: alpha = n and tau = 0. *)
Lemma g286_e807_edgeless (n : nat) : g286_e807_event (set0 : {set {set 'I_n}}).
Proof.
rewrite /g286_e807_event.
have noe (x y : fg_labelled_sgraph (set0 : {set {set 'I_n}})) : ~~ x -- y.
  by rewrite /edge_rel /= /fg_srel /fg_edge_set_rel !inE andbF.
have -> : n - α([set: fg_labelled_sgraph (set0 : {set {set 'I_n}})]) = 0.
  apply/eqP; rewrite subn_eq0.
  have st : [set: fg_labelled_sgraph (set0 : {set {set 'I_n}})] \in stabsets [set: fg_labelled_sgraph set0].
    by apply/stabsetsP; split=> //; apply/stableP => x y _ _; exact: noe.
  by apply: leq_trans (stabset_bound st); rewrite cardsT card_ord.
apply/andP; split; last by apply/forallP => -[].
apply/existsP; exists [ffun _ => (set0, set0)]; apply/and3P; split; try by apply/forallP => -[].
rewrite big_ord0; apply/subsetP => e; rewrite in_sg_edge_set => /existsP [x /existsP [y /andP [xy _]]].
by move: (noe x y); rewrite xy.
Qed.

Definition g286_e807_hyp_claim : Prop :=
  [/\ forall n : nat, 0 < fg_total_weight (@fg_gnp_weight 1 2 n),
      forall n : nat, g286_e807_event (set0 : {set {set 'I_n}}) &
      (erdos_807_bipartition_number_random_graph_statement ->
         eventually (fun n => 0 < fg_event_weight (@fg_gnp_weight 1 2 n) (@g286_e807_event n)))].

Theorem g286_e807_hyp_inhabited : g286_e807_hyp_claim.
Proof.
split; [exact: g286_gnp_half_total_pos | exact: g286_e807_edgeless |].
move=> /(_ 1 2 isT isT) [N hN]; exists N => n Nn; have [pos ge] := hN n Nn.
by rewrite lt0n; apply/negP => /eqP z; move: ge; rewrite z muln0 mul1n leqn0 => /eqP t; move: pos; rewrite t.
Qed.

(** not_trivially_true: the event for EVERY labelled graph (no probability) is false at C_4, where tau = 1 and
    n - alpha = 2, and it implies the statement. *)
Definition g286_e807_every_graph : Prop :=
  forall (n : nat) (E : {set {set 'I_n}}),
    x286_biclique_partition (fg_labelled_sgraph E) (n - α([set: fg_labelled_sgraph E]))
    && [forall k : 'I_(n - α([set: fg_labelled_sgraph E])), ~~ x286_biclique_partition (fg_labelled_sgraph E) k].

Definition g286_e807_ntt_claim : Prop :=
  ~ g286_e807_every_graph /\ (g286_e807_every_graph -> erdos_807_bipartition_number_random_graph_statement).

Theorem g286_e807_not_trivially_true : g286_e807_ntt_claim.
Proof.
split.
  move=> /(_ 4 g286_C4_edges) /andP [_ /forallP no].
  have lt : 1 < 4 - α([set: g286_C4]) by have := g286_C4_alpha; case: (α(_)) => [|[|[|]]].
  by move: (no (Ordinal lt)); rewrite g286_C4_partition1.
move=> V; rewrite g286_e807E => a b a0 ab; exists 0 => n _; split; first exact: g286_gnp_half_total_pos.
have -> : fg_event_weight (@fg_gnp_weight 1 2 n) (@g286_e807_event n) = fg_total_weight (@fg_gnp_weight 1 2 n).
  by apply: eq_bigl => E; exact: V.
by rewrite leq_mul2r leq_subr orbT.
Qed.

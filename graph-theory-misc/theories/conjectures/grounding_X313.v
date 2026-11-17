(** * GTMisc.conjectures.grounding_X313 -- grounding certificates of wave X313: the hyp_inhabited and
      not_trivially_true certificates of the row and the helper_sanity certificate of x313_noncomplete_blocks *)

From GTBase Require Import base.
From GTMisc.conjectures Require Import X156 X165 X313.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** General lemmas *)

(* If the whole vertex set has no cut vertex, it is the only block. *)
Lemma g313_whole_block (G : sgraph) : x156_no_cut_vertexb [set: G] -> x156_blockb [set: G].
Proof.
move=> hT; rewrite /x156_blockb hT /=; apply/forallP => B'; apply/implyP => /andP[hB' _].
by rewrite eqEsubset hB' subsetT.
Qed.

Lemma g313_block_whole (G : sgraph) (B : {set G}) :
  x156_no_cut_vertexb [set: G] -> x156_blockb B -> B = [set: G].
Proof.
move=> hT /andP[_ /forallP /(_ [set: G])]; rewrite subsetT hT /= => /eqP.
by [].
Qed.

Lemma g313_whole (G : sgraph) : x156_no_cut_vertexb [set: G] ->
  x313_noncomplete_blocks G = if cliqueb [set: G] then set0 else [set [set: G]].
Proof.
move=> hT; apply/setP => B; rewrite !inE.
case: (boolP (x156_blockb B)) => hB /=.
- rewrite (g313_block_whole hT hB); case: (cliqueb _); by rewrite !inE ?eqxx.
- case: (cliqueb _); rewrite ?inE //; apply/esym/negbTE/negP => /eqP hBT.
  by move: hB; rewrite hBT g313_whole_block.
Qed.

(* Connectivity from a centre reaching every member in at most two steps inside S. *)
Lemma g313_connected2 (G : sgraph) (S : {set G}) (c : G) :
  c \in S ->
  (forall y, y \in S -> [|| y == c, c -- y | [exists z in S, c -- z && z -- y]]) ->
  connectedb S.
Proof.
move=> cS hS; apply/connectedP; apply: (@connected_center G c S) => //.
move=> y yS; case/or3P: (hS y yS) => [/eqP -> | cy | /exists_inP [z zS /andP [cz zy]]].
- exact: connect0.
- by apply: connect1; rewrite /= cS yS cy.
- apply: (@connect_trans _ _ z); apply: connect1; by rewrite /= ?cS ?zS ?yS ?cz ?zy.
Qed.

(* A vertex without neighbours in S reaches only itself inside S. *)
Lemma g313_isolated (G : sgraph) (S : {set G}) (x y : G) :
  (forall z, z \in S -> ~~ x -- z) -> connect (preliminaries.restrict_mem (mem S) (--)) x y -> y = x.
Proof.
move=> hx /connectP [[|z p] /= hp hy]; first by [].
by move: hp => /andP [/andP [/andP [_ zS] xz] _]; move: (hx z zS); rewrite xz.
Qed.

Lemma g313_dist0 (G : sgraph) (x : G) : graph_dist x x = 0.
Proof.
rewrite /graph_dist; case: ex_minnP => m _ /(_ 0); rewrite /= inE eqxx /=.
by move=> /(_ isT); rewrite leqn0 => /eqP.
Qed.

(* Connectivity through an explicit centre c: every member of S is c, a neighbour of c, or a neighbour of a neighbour
   of c inside S; the check runs on an explicit vertex list. *)
Definition g313_conn_check (G : sgraph) (pv : seq G) (p : pred G) : bool :=
  has (fun c => p c && all (fun y => p y ==>
    [|| y == c, c -- y | has (fun z => [&& p z, c -- z & z -- y]) pv]) pv) pv.

Lemma g313_connP (G : sgraph) (pv : seq G) (S : {set G}) (p : pred G) :
  (forall x, x \in pv) -> (forall x, (x \in S) = p x) -> g313_conn_check pv p -> connectedb S.
Proof.
move=> hall hS /hasP [c _ /andP [pc /allP h]].
apply: (@g313_connected2 _ _ c); first by rewrite hS.
move=> y; rewrite hS => py; move/implyP: (h y (hall y)) => /(_ py).
case/or3P=> [/eqP -> | cy | /hasP [z _ /and3P [pz cz zy]]].
- by rewrite eqxx.
- by rewrite cy orbT.
- apply/or3P; apply: Or33; apply/exists_inP; exists z; by rewrite ?hS ?cz ?zy.
Qed.

(* A vertex x whose only neighbour is c makes c a cut vertex of any B holding c, x and a third vertex y. *)
Lemma g313_cut (G : sgraph) (B : {set G}) (c x y : G) :
  x \in B -> y \in B -> c \in B -> x != c -> y != c -> y != x ->
  (forall z, x -- z -> z = c) -> ~~ x156_no_cut_vertexb B.
Proof.
move=> xB yB cB xc yc yx hx; apply/negP => /and3P [_ _ /forall_inP /(_ c cB) /connectedP hc].
have hxz : forall z, z \in B :\ c -> ~~ x -- z.
  by move=> z; rewrite !inE => /andP [zc _]; apply/negP => /hx zeq; rewrite zeq eqxx in zc.
have hxS : x \in B :\ c by rewrite !inE xc xB.
have hyS : y \in B :\ c by rewrite !inE yc yB.
by move: yx; rewrite (g313_isolated hxz (hc x y hxS hyS)) eqxx.
Qed.

(** ** Complete graphs: every block is complete *)
Lemma g313_complete_clique (n : nat) (B : {set 'K_n}) : cliqueb B.
Proof. by apply/forall_inP => x _; apply/forall_inP => y _; apply/implyP. Qed.

Lemma g313_complete (n : nat) : x313_noncomplete_blocks 'K_n = set0.
Proof. by apply/setP => B; rewrite !inE g313_complete_clique andbF. Qed.

(** ** C_4 (GTBase cycle_graph 4): no cut vertex, not complete, so its one block is its vertex set *)
Local Notation C4 := (cycle_graph 4).
Local Notation O4 i := (@Ordinal 4 i isT : C4).

Definition g313_c4v : seq C4 := [:: O4 0; O4 1; O4 2; O4 3].

Lemma g313_c4v_all (x : C4) : x \in g313_c4v.
Proof. by case: x => -[|[|[|[|n]]]] Hx //=; apply/eqP. Qed.

Arguments g313_c4v : simpl never.

Lemma g313_c4_conn_ok :
  g313_conn_check g313_c4v predT && all (fun v => g313_conn_check g313_c4v (fun y => y != v)) g313_c4v.
Proof. by vm_compute. Qed.

Lemma g313_c4_nocut : x156_no_cut_vertexb [set: C4].
Proof.
case/andP: g313_c4_conn_ok => h1 /allP h2; apply/and3P; split.
- by apply/set0Pn; exists (O4 0); rewrite inE.
- by apply: (g313_connP (p := predT) g313_c4v_all) => // x; rewrite inE.
- apply/forall_inP => v _; apply: (g313_connP (p := fun y => y != v) g313_c4v_all); last exact: h2 _ (g313_c4v_all v).
  by move=> x; rewrite !inE andbT.
Qed.

Lemma g313_c4_nclique : ~~ cliqueb [set: C4].
Proof.
apply/forall_inPn; exists (O4 0); first by rewrite inE.
by apply/forall_inPn; exists (O4 2); [rewrite inE | vm_compute].
Qed.

Lemma g313_C4 : x313_noncomplete_blocks C4 = [set [set: C4]].
Proof. by rewrite (g313_whole g313_c4_nocut) (negbTE g313_c4_nclique). Qed.

(** ** C_4 with one pendant edge: vertices 0..3 the cycle, vertex 4 adjacent to 0 only *)
Definition g313_pend_edges : seq (nat * nat) := [:: (0, 1); (1, 2); (2, 3); (3, 0); (0, 4)].

Definition g313_pend_rel (i j : 'I_5) : bool :=
  ((val i, val j) \in g313_pend_edges) || ((val j, val i) \in g313_pend_edges).

Lemma g313_pend_sym : symmetric g313_pend_rel.
Proof. by move=> i j; rewrite /g313_pend_rel orbC. Qed.

Lemma g313_pend_irrefl : irreflexive g313_pend_rel.
Proof. by move=> i; rewrite /g313_pend_rel orbb; case: i => -[|[|[|[|[|n]]]]]. Qed.

Definition g313_pend : sgraph := SGraph g313_pend_sym g313_pend_irrefl.

Local Notation O5 i := (@Ordinal 5 i isT : g313_pend).

Definition g313_pv : seq g313_pend := [:: O5 0; O5 1; O5 2; O5 3; O5 4].

Lemma g313_pv_all (x : g313_pend) : x \in g313_pv.
Proof. by case: x => -[|[|[|[|[|n]]]]] Hx //=; apply/eqP. Qed.

Arguments g313_pv : simpl never.

(* The cycle's four vertices. *)
Definition g313_c4part : {set g313_pend} := [set O5 0; O5 1; O5 2; O5 3].

Lemma g313_c4partE (x : g313_pend) : (x \in g313_c4part) = (x != O5 4).
Proof. by rewrite !inE; case: x => -[|[|[|[|[|n]]]]] Hx. Qed.

Lemma g313_pend_conn_ok :
  g313_conn_check g313_pv (fun y => y != O5 4) &&
  all (fun v => (v != O5 4) ==> g313_conn_check g313_pv (fun y => (y != v) && (y != O5 4))) g313_pv.
Proof. by vm_compute. Qed.

Lemma g313_pend_only_ok : all (fun z => @edge_rel g313_pend (O5 4) z ==> (z == O5 0)) g313_pv.
Proof. by vm_compute. Qed.

Lemma g313_pend_only (z : g313_pend) : O5 4 -- z -> z = O5 0.
Proof. by move/allP: g313_pend_only_ok => /(_ z (g313_pv_all z)) /implyP h /h /eqP. Qed.

Lemma g313_c4part_nocut : x156_no_cut_vertexb g313_c4part.
Proof.
case/andP: g313_pend_conn_ok => h1 /allP h2; apply/and3P; split.
- by apply/set0Pn; exists (O5 0); rewrite g313_c4partE.
- by apply: (g313_connP (p := fun y => y != O5 4) g313_pv_all) => // x; rewrite g313_c4partE.
- apply/forall_inP => v; rewrite g313_c4partE => v4.
  apply: (g313_connP (p := fun y => (y != v) && (y != O5 4)) g313_pv_all).
  + by move=> x; rewrite in_setD1 g313_c4partE.
  + by move/implyP: (h2 v (g313_pv_all v)); apply.
Qed.

Lemma g313_c4part_nclique : ~~ cliqueb g313_c4part.
Proof.
apply/forall_inPn; exists (O5 1); first by rewrite g313_c4partE.
by apply/forall_inPn; exists (O5 3); [rewrite g313_c4partE | vm_compute].
Qed.

Lemma g313_c4part_block : x156_blockb g313_c4part.
Proof.
rewrite /x156_blockb g313_c4part_nocut /=; apply/forallP => B'; apply/implyP => /andP [hsub hB'].
case: (boolP (O5 4 \in B')) => h4.
- have hc : ~~ @x156_no_cut_vertexb g313_pend B'.
    apply: (@g313_cut g313_pend B' (O5 0) (O5 4) (O5 1) h4) => //.
    + by apply: (subsetP hsub); rewrite g313_c4partE.
    + by apply: (subsetP hsub); rewrite g313_c4partE.
    + exact: g313_pend_only.
  by rewrite hB' in hc.
- rewrite eqEsubset hsub andbT; apply/subsetP => x xB; rewrite g313_c4partE.
  by apply: (contraNneq _ h4) => x4; rewrite -x4.
Qed.

Lemma g313_pend_blocks : x313_noncomplete_blocks g313_pend = [set g313_c4part].
Proof.
apply/setP => B; rewrite !inE; apply/andP/eqP => [[hB hnc] | ->]; last first.
  by split; [exact: g313_c4part_block | exact: g313_c4part_nclique].
have hnB : x156_no_cut_vertexb B by case/andP: hB.
case/forall_inPn: hnc => x xB /forall_inPn [y yB]; rewrite negb_imply => /andP [xy nxy].
have h4 : O5 4 \notin B.
  apply/negP => h4; case: (boolP (O5 0 \in B)) => h0.
  - have hw : forall w, w \in B -> (w == O5 0) || (w == O5 4).
      move=> w wB; apply/negPn/negP; rewrite negb_or => /andP [w0 w4].
      have := @g313_cut _ B (O5 0) (O5 4) w h4 wB h0 isT w0 w4 g313_pend_only.
      by rewrite hnB.
    move: xy nxy; case/orP: (hw x xB) => /eqP ->; case/orP: (hw y yB) => /eqP ->; by vm_compute.
  - case/and3P: hnB => _ /connectedP hconn _.
    have hiso : forall z, z \in B -> ~~ O5 4 -- z.
      by move=> z zB; apply/negP => /g313_pend_only z0; rewrite -z0 zB in h0.
    have hx4 := g313_isolated hiso (hconn (O5 4) x h4 xB).
    have hy4 := g313_isolated hiso (hconn (O5 4) y h4 yB).
    by move: xy; rewrite hx4 hy4 eqxx.
have hsub : B \subset g313_c4part.
  by apply/subsetP => x' x'B; rewrite g313_c4partE; apply: (contraNneq _ h4) => x4; rewrite -x4.
case/andP: hB => _ /forallP /(_ g313_c4part); rewrite hsub g313_c4part_nocut /= => /eqP h.
by rewrite h.
Qed.

(** ** helper_sanity: x313_noncomplete_blocks on K_4 (empty), on C_4 (its vertex set) and on C_4 with a pendant edge
    (the cycle's four vertices: the bridge block, a K_2, is complete and excluded) *)
Definition g313_helper_claim : Prop :=
  [/\ x313_noncomplete_blocks ('K_4) = set0,
      x313_noncomplete_blocks C4 = [set [set: C4]]
    & x313_noncomplete_blocks g313_pend = [set [set O5 0; O5 1; O5 2; O5 3]]].

Theorem g313_helper_sanity : g313_helper_claim.
Proof. by split; [exact: g313_complete | exact: g313_C4 | exact: g313_pend_blocks]. Qed.

(** ** hyp_inhabited (C_4: connected, one non-complete block) and not_trivially_true (without the connectivity
    hypothesis the statement fails on two isolated vertices) *)
Definition g313_swb_at (G : sgraph) : Prop :=
  x165_wiener_index G + \sum_(B in x313_noncomplete_blocks G) (2 * #|B|)
    <= x165_szeged_index G + 6 * #|x313_noncomplete_blocks G|.

Definition g313_swb_hyp_claim : Prop :=
  [/\ connected [set: C4], x313_noncomplete_blocks C4 = [set [set: C4]] &
      (szeged_wiener_difference_noncomplete_blocks_statement -> g313_swb_at C4)].

Theorem g313_swb_hyp_inhabited : g313_swb_hyp_claim.
Proof.
have hc : connected [set: C4] by case/and3P: g313_c4_nocut => _ /connectedP.
split=> //; first exact: g313_C4.
by move=> S; exact: S _ hc.
Qed.

(* Two isolated vertices: graph_dist is #|G| = 2 between them (graph_metric.v), so the Wiener index is positive while
   the Szeged index and the block sum vanish. *)
Definition g313_e2_rel (i j : 'I_2) : bool := false.

Lemma g313_e2_sym : symmetric g313_e2_rel.
Proof. by []. Qed.

Lemma g313_e2_irrefl : irreflexive g313_e2_rel.
Proof. by []. Qed.

Definition g313_e2 : sgraph := SGraph g313_e2_sym g313_e2_irrefl.

Local Notation O2 i := (@Ordinal 2 i isT : g313_e2).

Lemma g313_dist_pos (G : sgraph) (x y : G) : x != y -> 0 < graph_dist x y.
Proof.
move=> xy; rewrite lt0n; apply/negP; rewrite /graph_dist; case: ex_minnP => m hm _ /eqP m0.
move: hm; rewrite m0 /= inE => /orP [/eqP yx | /eqP G0]; first by rewrite yx eqxx in xy.
have : 0 < #|G| by apply/card_gt0P; exists x.
by rewrite -G0.
Qed.

Lemma g313_wiener_pos (G : sgraph) (x y : G) : x != y -> 0 < x165_wiener_index G.
Proof.
move=> xy; rewrite /x165_wiener_index divn_gt0 //.
have hF : forall u v : G, graph_dist u v <= \sum_w graph_dist u w.
  by move=> u v; rewrite (bigD1 v) //= leq_addr.
rewrite (bigD1 x) //= [X in _ + X](bigD1 y); first by rewrite eq_sym.
have h1 := leq_trans (g313_dist_pos xy) (hF x y).
have h2 : 0 < \sum_w graph_dist y w.
  by apply: leq_trans (g313_dist_pos (y := x) _) (hF y x); rewrite eq_sym.
by apply: leq_trans (leq_add h1 h2) _; rewrite /= leq_add2l leq_addr.
Qed.

Lemma g313_e2_Sz : x165_szeged_index g313_e2 = 0.
Proof. by rewrite /x165_szeged_index big1 ?div0n // => u _; rewrite big_pred0. Qed.

Lemma g313_e2_blocks : x313_noncomplete_blocks g313_e2 = set0.
Proof.
apply/setP => B; rewrite !inE; apply/negbTE; rewrite negb_and negbK.
case: (boolP (x156_blockb B)) => //= /andP [/and3P [_ /connectedP hc _] _].
apply/forall_inP => x xB; apply/forall_inP => y yB.
by rewrite (g313_isolated (S := B) (x := x) _ (hc x y xB yB)) ?eqxx.
Qed.

Lemma g313_e2_disconnected : ~ connected [set: g313_e2].
Proof.
move=> hc; have := g313_isolated (S := [set: g313_e2]) (x := O2 0) _ (hc (O2 0) (O2 1) (in_setT _) (in_setT _)).
by move=> /(_ (fun z _ => isT)).
Qed.

(* not_trivially_true: dropping the connectivity hypothesis gives a variant that implies the row and fails on the
   two isolated vertices. *)
Definition g313_swb_unguarded : Prop := forall G : sgraph, g313_swb_at G.

Definition g313_swb_ntt_claim : Prop :=
  [/\ ~ connected [set: g313_e2], ~ g313_swb_at g313_e2, ~ g313_swb_unguarded &
      (g313_swb_unguarded -> szeged_wiener_difference_noncomplete_blocks_statement)].

Theorem g313_swb_not_trivially_true : g313_swb_ntt_claim.
Proof.
have hE : ~ g313_swb_at g313_e2.
  rewrite /g313_swb_at g313_e2_blocks big_set0 cards0 g313_e2_Sz muln0 !addn0 leqn0 => /eqP hW.
  by move: (@g313_wiener_pos g313_e2 (O2 0) (O2 1) isT); rewrite hW.
split; [exact: g313_e2_disconnected | exact: hE | by move=> V; exact: hE (V _) | by move=> V G _; exact: V G].
Qed.

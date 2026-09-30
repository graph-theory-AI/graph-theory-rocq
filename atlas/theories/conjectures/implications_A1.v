(** * Atlas.conjectures.implications_A1 -- cross-package implication edges

    The [atlas] package is the only package that imports every area package
    (and [digraph-theory], see [implications_A2.v]).  It hosts the theorems
    [<from-core>_implies_<to-core>] for the corpus relations whose two
    endpoints live in packages that cannot import each other.  Area packages
    keep importing only [GTBase] (plus the two sanctioned topological
    exceptions); the atlas depends on all of them and nothing depends on it.

    Conventions: every edge carries an EDGE annotation comment (see meta/build_edge_graph.py) read by
    [meta/build_edge_graph.py]; a verified edge's theorem sits in this file,
    right after its annotation; a [conditional] edge lists its registered
    external theorems ([meta/external_theorems.json]).  Proof obligations of
    this wave are recorded in [meta/edge_waves.json] (wave A1).  No lemma of
    [mathcomp-classical] may be used (axiom-free rule: every theorem must be
    closed under the global context). *)

From GTBase Require Import base.
From Extremal.conjectures Require Import D2chr D2tur.
From Minor.conjectures Require Import X5 U7 X214 X8 X228 X175.
From Chromatic.conjectures Require Import U4 X31 X219.
From GTMisc.conjectures Require Import U13 X217.
From Topological.conjectures Require Import U13 D6emb X158.
From Packing.conjectures Require Import X47 X48.
From Cycle.conjectures Require Import X212 U6 D1.
From Hypergraph.conjectures Require Import X217.
From Hom.conjectures Require Import U3.
From Spectral.conjectures Require Import D5.
From Hamilton.conjectures Require Import X211.
From Minor.foundations Require Import minor_dec width_params.
From GTMisc.foundations Require Import cops.
From GTBase Require Import common asymptotics.
From Atlas.foundations Require Import fractional degeneracy tree_decompositions
  cops_bridge complete_minors queue_layouts.
From GraphTheory Require Import minor.
From mathcomp Require Import all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Some imported rows open [ring_scope]; the proofs below are in [nat_scope]. *)
Local Open Scope nat_scope.

(** ** Wave A1 -- tier T2 edges: one theorem per verified edge, BLOCKED notes otherwise *)

(*@EDGE from=fractional_hadwiger_statement to=hadwiger_independence_minor_statement kind=implies status=verified proof=fractional_hadwiger_implies_hadwiger_independence_minor cite="gc:e003" note="Part (a) only. The source takes chi_f, had and had_f as attained optima, so all three are first shown to EXIST (fractional.frac_chromatic_exists, fractional.frac_hadwiger_exists: Fourier-Motzkin LP attainment, Extremal.foundations.lp_rational; hadwiger_exists: finite arg-max with minor_dec.minorP). Then n <= chi_f * alpha (fractional.frac_chi_n_alpha: the a colour classes of an (a:b)-colouring are stable and cover each vertex b times) and chi_f <= had (source part (a)) give n <= had * alpha; a K_(t+1)-minor-free G has had <= t (minor_dec.minor_K_le), so n <= t * alpha. Wave E10, after the D2chr guard repair (non-empty branch sets)." *)
Section E003.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** had(G) exists: the largest k with a K_k minor, [minor] being decidable
    ([minor_dec.minorP]) and bounded by [#|G|] ([minor_card]). *)
Lemma hadwiger_exists (G : sgraph) : exists h, is_hadwiger G h.
Proof.
have ex : exists k, minorb G 'K_k by exists 0%N; apply/minorP; exact: minor_K0.
have bd k : minorb G 'K_k -> (k <= #|G|)%N by move/minorP/minor_card; rewrite card_ord.
case: (ex_maxnP ex bd) => h /minorP hm hmax; exists h; split => // h' /minorP; exact: hmax.
Qed.

(** Part (a) of the fractional Hadwiger row, instantiated at the (existing) optima,
    with [n <= chi_f * alpha]: [n <= had * alpha]. *)
Lemma fractional_hadwiger_n_le_had_alpha (G : sgraph) (h : nat) :
  fractional_hadwiger_statement -> (0 < #|G|)%N -> is_hadwiger G h ->
  (#|G| <= h * α(G))%N.
Proof.
move=> H G0 hh.
have [xf hxf] := frac_chromatic_exists G.
have [hf hhf] := frac_hadwiger_exists G.
have [a _ _] := H G xf hf h G0 hxf hh hhf.
rewrite -(ler_nat rat) natrM.
apply: mathcomp.order.preorder.Order.PreorderTheory.le_trans (frac_chi_n_alpha hxf) _.
by rewrite ler_wpM2r ?ler0n // pmulrn.
Qed.

Theorem fractional_hadwiger_implies_hadwiger_independence_minor :
  fractional_hadwiger_statement -> hadwiger_independence_minor_statement.
Proof.
move=> H t n G t0 <- nK.
case: (posnP #|G|) => [->|G0]; first by [].
have [h hh] := hadwiger_exists G.
have ht : (h <= t)%N.
  by rewrite leqNgt; apply/negP => th; apply: nK; exact: minor_K_le th hh.1.
apply: leq_trans (fractional_hadwiger_n_le_had_alpha H G0 hh) _.
by rewrite leq_mul2r ht orbT.
Qed.

(*@EDGE from=fractional_hadwiger_statement to=seagull_statement kind=implies status=verified proof=fractional_hadwiger_implies_seagull cite="gc:e042" note="Part (a) only. As for e003, the attained optima exist (fractional.frac_chromatic_exists, fractional.frac_hadwiger_exists, hadwiger_exists) and n <= chi_f * alpha <= had * alpha (fractional.frac_chi_n_alpha + source part (a)); with alpha <= 2 this is n <= 2 * had, hence ceil_div n 2 <= had, and the K_had minor gives a K_(ceil_div n 2) minor (minor_dec.minor_K_le). Wave E10, after the D2chr guard repair." *)

Theorem fractional_hadwiger_implies_seagull :
  fractional_hadwiger_statement -> seagull_statement.
Proof.
move=> H G G0 a2.
have [h hh] := hadwiger_exists G.
have n2 : (#|G| <= h * 2)%N.
  apply: leq_trans (fractional_hadwiger_n_le_had_alpha H G0 hh) _.
  by rewrite leq_mul2l a2 orbT.
apply: minor_K_le hh.1.
rewrite /ceil_div -ltnS ltn_divLR // addn2 subn1 /= mulSn add2n !ltnS.
exact: n2.
Qed.
End E003.

(*@EDGE from=hadwiger_chromatic_clique_minor_statement to=fractional_hadwiger_statement kind=implies status=verified proof=hadwiger_chromatic_clique_minor_implies_fractional_hadwiger cite="gc:e223" note="Hadwiger at k = chi gives a K_chi minor, so chi <= h (maximality in is_hadwiger); chi_f <= chi (an optimal colouring is a (chi:1)-colouring, fractional.frac_chi_le_chi); chi <= had_f (the branch sets of the K_chi minor with weight 1 are LP-feasible, fractional.minor_K_le_frac_hadwiger); (a),(b),(c) follow. Re-verified in wave E10 against the REPAIRED target (D2chr branch sets now non-empty; the old vacuity witness is grounding_D2chr.old_is_fractional_hadwiger_unsat, and the repaired had_f exists for every graph, fractional.frac_hadwiger_exists), so the edge is no longer vacuous." *)
Section E223.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Theorem hadwiger_chromatic_clique_minor_implies_fractional_hadwiger :
  hadwiger_chromatic_clique_minor_statement -> fractional_hadwiger_statement.
Proof.
move=> Had G xf hf h _ Hxf [_ Hh] Hhf.
have m := Had _ G erefl.
have c1 := frac_chi_le_chi Hxf.
have c2 : (χ([set: G]))%:Q <= hf := minor_K_le_frac_hadwiger m Hhf.
have c3 : (χ([set: G]))%:Q <= h%:Q by rewrite ler_int lez_nat; exact: Hh.
by split; [exact: mathcomp.order.preorder.Order.PreorderTheory.le_trans c3 | exact: c2 | exact: mathcomp.order.preorder.Order.PreorderTheory.le_trans c2].
Qed.
End E223.
(*@EDGE from=kt_minor_free_two_s_plus_t_choosable_statement to=list_hadwiger_statement kind=implies status=verified proof=kt_minor_free_two_s_plus_t_choosable_implies_list_hadwiger cite="gc:e048" note="c := 3. t = 0: every graph has a K_0 minor (complete_minors.minor_K0). t >= 1: s := max 1 (t-1); K_{s,s} has a K_{s+1} minor (complete_minors.KB_diag_minor_K: contract s-1 edges of a perfect matching) and t <= s+1 (minor_dec.minor_K_le), so a K_t-minor-free G is K_{s,s}-minor-free and the source with (s, s) gives ch <= 3s <= 3t." *)
Theorem kt_minor_free_two_s_plus_t_choosable_implies_list_hadwiger :
  kt_minor_free_two_s_plus_t_choosable_statement -> list_hadwiger_statement.
Proof.
move=> H; exists 3; split => // G t ch nK hch.
case: t nK => [nK|t nK]; first by exfalso; exact: nK (minor_K0 G).
pose s := maxn 1 t.
have s1 : (1 <= s)%N by rewrite leq_maxl.
have st : (s <= t.+1)%N by rewrite geq_max ltnS leqnSn andbT.
have nKB : ~ minor G (KB s s).
  move=> m; apply: nK; apply: (minor_K_le (n := s.+1)); first by rewrite ltnS leq_maxr.
  case: s m s1 {st} => // s' m _; exact: minor_trans m (KB_diag_minor_K s').
apply: leq_trans (H s s ch G s1 (leqnn s) nKB hch) _.
by rewrite -mulSnr leq_mul2l st orbT.
Qed.
(*@EDGE from=subgraph_of_large_average_degree_and_large_average_d_statement to=chromatic_girth_average_degree_subgraph_statement kind=implies status=verified proof=subgraph_of_large_average_degree_and_large_average_d_implies_chromatic_girth_average_degree_subgraph cite="gc:e117" note="Given k, g >= 3, take d from the source at (g, k) and c := d+2. If chi(G) >= d+2 then G has a nonempty vertex set S with every inner degree >= d+1 (degeneracy.dense_core_of_chi: otherwise greedy colouring along the degeneracy order uses d+1 colours, degeneracy.degenerate_colouring, and chi_bounding.chi_le_palette bounds chi); induced S is nonempty with average degree >= d, so the source gives H in it with average degree >= k and girth > g; compose the injective homomorphisms with val; girth > g gives girth >= g. Both rows use GTBase average_degree_geq _ _ 1 and girth_geq." *)
Theorem subgraph_of_large_average_degree_and_large_average_d_implies_chromatic_girth_average_degree_subgraph :
  subgraph_of_large_average_degree_and_large_average_d_statement ->
  chromatic_girth_average_degree_subgraph_statement.
Proof.
move=> Th k g k0 g3.
have [d Hd] := Th g k (leq_trans (isT : 0 < 3) g3) k0.
exists d.+2; split => // G chiG.
have [S S0 degS] := @dense_core_of_chi G d.+1 isT chiG.
have [v0 v0S] := set0Pn _ S0.
pose H := induced S.
have nH : 0 < #|H| by apply/card_gt0P; exists (Sub v0 v0S).
have degH (x : H) : d.+1 <= #|N(x)|.
  apply: leq_trans (degS _ (valP x)) _.
  apply: leq_trans (leq_imset_card val _); apply: subset_leq_card.
  apply/subsetP => u; rewrite !inE => /andP [xu uS].
  by apply/imsetP; exists (Sub u uS); rewrite ?inE //.
have avH : avgdeg_geq H d.
  rewrite /avgdeg_geq /average_degree_geq mul1n mulnC.
  apply: (@leq_trans (\sum_(x in H) d)); first by rewrite sum_nat_const.
  by apply: leq_sum => x _; exact: ltnW.
have [K [nK [f [finj fhom]] avK girK]] := Hd H nH avH.
exists K; split; last split.
- exists (val \o f); split; first exact: inj_comp val_inj finj.
  by move=> x y xy; exact: (fhom x y xy).
- by move=> c cc c2; apply: ltnW; exact: girK.
- exact: avK.
Qed.
(*@EDGE from=planar_fractional_vertex_arboricity_two_statement to=large_induced_forest_in_a_planar_graph_statement kind=implies status=verified proof=planar_fractional_vertex_arboricity_two_implies_large_induced_forest_in_a_planar_graph cite="gc:e121" note="Pigeonhole (F35): both rows use the same wagner_planar and is_forest. The 2b forests F i cover every vertex at least b times, so by double counting sum_i |F i| = sum_v #{i | v in F i} >= b*|V|; the largest F i therefore has 2b*|F i| >= b*|V|, i.e. |V| <= 2*|F i| (the target's cross-multiplied ceiling form), cancelling b > 0." *)
Lemma frac_va2_large_forest (G : sgraph) :
  x219_frac_vertex_arboricity_le_two G ->
  exists S : {set G}, is_forest S /\ #|G| <= 2 * #|S|.
Proof.
case=> b [b0 [F [Ff Fc]]].
have n0 : 0 < 2 * b by rewrite muln_gt0 b0.
pose i0 : 'I_(2 * b) := Ordinal n0.
case: (@arg_maxnP _ i0 predT (fun i => #|F i|) isT) => im _ Hm.
exists (F im); split => //.
have dc : \sum_(i < 2 * b) #|F i| = \sum_(v : G) #|[set i : 'I_(2 * b) | v \in F i]|.
  transitivity (\sum_(i < 2 * b) \sum_(v : G) (v \in F i : nat)).
    by apply: eq_bigr => i _; rewrite -sum1_card big_mkcond.
  rewrite exchange_big; apply: eq_bigr => v _.
  by rewrite -sum1_card [RHS]big_mkcond; apply: eq_bigr => i _; rewrite inE.
have lo : b * #|G| <= \sum_(i < 2 * b) #|F i|.
  rewrite dc -sum1_card big_distrr /= muln1; apply: leq_sum => v _; exact: Fc.
have hi : \sum_(i < 2 * b) #|F i| <= 2 * b * #|F im|.
  rewrite -[2 * b in X in _ <= X]card_ord -sum_nat_const.
  by apply: leq_sum => i _; exact: Hm.
by rewrite -(leq_pmul2l b0) mulnA [b * 2]mulnC (leq_trans lo hi).
Qed.

Theorem planar_fractional_vertex_arboricity_two_implies_large_induced_forest_in_a_planar_graph :
  planar_fractional_vertex_arboricity_two_statement ->
  large_induced_forest_in_a_planar_graph_statement.
Proof. by move=> H G pG; apply: frac_va2_large_forest; exact: H. Qed.
(*@EDGE from=tree_decomposition_delta_edge_connected_statement to=barat_thomassen_tree_decomposition_statement kind=implies status=verified proof=tree_decomposition_delta_edge_connected_implies_barat_thomassen_tree_decomposition cite="gc:e208" note="k(T) := max (f Delta_T) (f |E T|). Vocabulary bridge (tree_decompositions.v): x47_edge_set = E(G); k_edge_connected G k (edge deletion) gives the cut form x47_edge_connected G k (a walk leaving S crosses a cut edge) and minimum degree >= k (cut of a singleton); an x47 decomposition (parts sharing an edge are equal, repetitions allowed) becomes an x212 exact-count decomposition after undup. The one-vertex tree (allowed by the target, excluded by the source's 0 < |E T|) is handled directly: 0 divides |E G| forces E(G) empty and the empty list decomposes it." *)
Theorem tree_decomposition_delta_edge_connected_implies_barat_thomassen_tree_decomposition :
  tree_decomposition_delta_edge_connected_statement ->
  barat_thomassen_tree_decomposition_statement.
Proof.
case=> f Hf T T0 Tt.
exists (maxn (f (Delta T)) (f #|x47_edge_set T|)) => G kc div.
case: (ltnP 1 #|T|) => T1.
- apply: x47_decomposition_x212; apply: Hf => //.
  + exact: tree_has_edge.
  + move=> S S0 ST; apply: leq_trans (k_edge_connected_cut kc S0 ST); exact: leq_maxl.
  + move=> v; apply: leq_trans (k_edge_connected_deg v kc); exact: leq_maxr.
  + by rewrite !x47_edge_setE.
- apply: trivial_tree_decomposition.
  have ET : #|E(T)| = 0.
    apply/eqP; rewrite cards_eq0; apply/eqP/setP => e; rewrite inE.
    apply/negP => /edgesP [x [y [_ xy]]].
    have := sg_edgeNeq xy; have -> : x = y by move/card_le1_eqP: T1; apply.
    by rewrite eqxx.
  by move: div; rewrite ET dvd0n => /eqP.
Qed.
(*@EDGE from=tree_decomposition_leaf_edge_connected_statement to=barat_thomassen_tree_decomposition_statement kind=implies status=verified proof=tree_decomposition_leaf_edge_connected_implies_barat_thomassen_tree_decomposition cite="gc:e237" note="k(T) := max (f (x48_leaf_count T)) (f |E T|); same bridge as e208 (tree_decompositions.v: cut form and minimum degree from k_edge_connected, undup of the x47 parts, the one-vertex tree handled directly)." *)
Theorem tree_decomposition_leaf_edge_connected_implies_barat_thomassen_tree_decomposition :
  tree_decomposition_leaf_edge_connected_statement ->
  barat_thomassen_tree_decomposition_statement.
Proof.
case=> f Hf T T0 Tt.
exists (maxn (f (x48_leaf_count T)) (f #|x47_edge_set T|)) => G kc div.
case: (ltnP 1 #|T|) => T1.
- apply: x47_decomposition_x212; apply: Hf => //.
  + exact: tree_has_edge.
  + move=> S S0 ST; apply: leq_trans (k_edge_connected_cut kc S0 ST); exact: leq_maxl.
  + move=> v; apply: leq_trans (k_edge_connected_deg v kc); exact: leq_maxr.
  + by rewrite !x47_edge_setE.
- apply: trivial_tree_decomposition.
  have ET : #|E(T)| = 0.
    apply/eqP; rewrite cards_eq0; apply/eqP/setP => e; rewrite inE.
    apply/negP => /edgesP [x [y [_ xy]]].
    have := sg_edgeNeq xy; have -> : x = y by move/card_le1_eqP: T1; apply.
    by rewrite eqxx.
  by move: div; rewrite ET dvd0n => /eqP.
Qed.
(*@EDGE from=asymmetric_bipartite_list_colouring_statement to=list_chromatic_number_and_maximum_degree_of_bipartit_statement kind=implies status=verified proof=asymmetric_bipartite_list_colouring_implies_list_chromatic_number_and_maximum_degree_of_bipartit cite="gc:e025" note="Case (ii) of the source with constants C, D0 > 1, applied with D_A = D_B = D := max(Delta, D0) (x219_max_degree_on is an upper bound) and k_A = k_B = k := C * trunc_log 2 D >= C > 0, gives choosable G k, so ch <= k. Target constant c := C * D0: if Delta >= D0 then 2^k = (2^(log Delta))^C <= Delta^C <= Delta^(C*D0); if Delta < D0 then k <= C*D0 (log D0 < D0) and 2^(C*D0) <= Delta^(C*D0) as Delta >= 2. The threshold D0 of the repaired source is absorbed by the existential c." *)
Lemma deg_le_Delta (G : sgraph) (v : G) : #|N(v)| <= Delta G.
Proof. exact: leq_bigmax. Qed.

Theorem asymmetric_bipartite_list_colouring_implies_list_chromatic_number_and_maximum_degree_of_bipartit :
  asymmetric_bipartite_list_colouring_statement ->
  list_chromatic_number_and_maximum_degree_of_bipartit_statement.
Proof.
case=> _ [[C [D0 [C1 D01 HC]]] _].
exists (C * D0) => G m [f Hf] D2 [_ Hmin].
pose D := maxn (Delta G) D0.
pose k := C * trunc_log 2 D.
have DD0 : D0 <= D by rewrite leq_maxr.
have D1 : 1 < D by apply: leq_trans DD0.
have k0 : 0 < k.
  rewrite muln_gt0 (ltn_trans _ C1) //=.
  by rewrite trunc_log_gt0 D1.
have chk : choosable G k.
  move=> P L HL.
  pose A := [set v : G | f v].
  apply: (HC G A D D k k) => //.
  - by move=> u v uv; rewrite !inE; exact: Hf.
  - by move=> v _; rewrite (leq_trans (deg_le_Delta v)) // leq_maxl.
  - by move=> v _; rewrite (leq_trans (deg_le_Delta v)) // leq_maxl.
have mk : m <= k by exact: Hmin.
have Dp : 0 < Delta G by apply: leq_trans D2.
apply: (@leq_trans (2 ^ k)); first by rewrite leq_pexp2l.
case: (leqP D0 (Delta G)) => hD.
- have eD : D = Delta G by apply/maxn_idPl.
  rewrite /k eD mulnC expnM.
  apply: (@leq_trans (Delta G ^ C)).
    by rewrite leq_exp2r ?(ltn_trans _ C1) // trunc_logP.
  by rewrite leq_pexp2l // leq_pmulr // (ltn_trans _ D01).
- have eD : D = D0 by apply/maxn_idPr; exact: ltnW.
  apply: (@leq_trans (2 ^ (C * D0))).
    rewrite leq_pexp2l // /k eD leq_mul2l; apply/orP; right.
    apply: ltnW; apply: (leq_trans (ltn_expl _ (isT : 1 < 2))).
    by rewrite trunc_logP // (ltn_trans _ D01).
  by rewrite leq_exp2r // muln_gt0 (ltn_trans _ C1) // (ltn_trans _ D01).
Qed.
(*@EDGE from=the_circular_embedding_statement to=cycle_double_cover_statement kind=implies status=candidate proved=false cite="gc:e087" note="BLOCKED: needs a bridge that is a large development. (1) Carrier reduction: the target quantifies over bridgeless loopy multigraphs (mgraph, connectivity.bridgeless), the source over 2-connected simple sgraphs; missing: subdivision of an mgraph into a simple sgraph preserving bridgelessness, the block decomposition of a bridgeless sgraph into 2-connected blocks (no K2 block) with gluing of the blocks' covers, and transport of circuits (connectivity.is_circuit on {set edge G}) back through the subdivision. (2) Face theory of signed_embedding.emap: each orbit of sface_perm (on dart * bool, so every face occurs twice, once per orientation, and must be quotiented by the mirror involution) of a circular_emap on a 2-connected graph traces a simple cycle, and every edge lies on exactly two face traversals counted with multiplicity. Neither layer exists in the repo." *)
(*@EDGE from=hypergraph_cop_number_sqrt_n_over_k_statement to=meyniel_cop_number_sqrt_statement kind=implies status=verified proof=hypergraph_cop_number_sqrt_n_over_k_implies_meyniel_cop_number_sqrt cite="gc:e243" note="Same constant C. A connected graph G with n >= 2 is the connected 2-uniform hypergraph E(G) with 2 <= n, on which hg_move = robber_move, hg_win = cops_capture and hg_cop_win = cops_win (cops_bridge.v). The source needs the cop number as a hypothesis: it exists constructively because cops_win is decided at horizon #positions (fixpoint stabilisation of the winning sets, cops_bridge.cops_win_bounded), so ex_minn applies. Then c^2 * 2 <= C^2 * n <= (C * sqrt_ceil n)^2 gives c <= C * sqrt_ceil n. n = 1: one cop suffices and C * sqrt_ceil 1 >= 1." *)
Theorem hypergraph_cop_number_sqrt_n_over_k_implies_meyniel_cop_number_sqrt :
  hypergraph_cop_number_sqrt_n_over_k_statement -> meyniel_cop_number_sqrt_statement.
Proof.
case=> C [C0 H]; exists C => G G0 con.
have sq0 : 0 < sqrt_ceil #|G|.
  rewrite lt0n; apply/eqP => e; have := sqrt_ceil_spec #|G|.
  by rewrite e exp0n // leqn0 => /eqP e'; rewrite e' in G0.
case: (ltnP 1 #|G|) => G1.
- have [c hc] := hg_is_cop_number_edges G.
  have unif : hg_uniform E(G) 2.
    by move=> e /edgesP [a [b [-> ab]]]; rewrite cards2 (sg_edgeNeq ab).
  have hcon : hg_connected E(G).
    move=> u v; apply: connect_sub (connectedTE con u v) => x y xy.
    by apply: connect1; rewrite hg_link_edges ?(sg_edgeNeq xy).
  have le := H G E(G) 2 c isT G1 unif hcon hc.
  exists c; split; last by apply/hg_cop_win_edges; case: hc.
  rewrite -(@leq_exp2r _ _ 2) // expnMn.
  apply: leq_trans (leq_trans _ le) _; first by rewrite leq_pmulr.
  by rewrite leq_mul2l sqrt_ceil_spec orbT.
- apply: cop_number_le_mono (cop_number_le_card G).
  by apply: leq_trans G1 _; rewrite muln_gt0 C0.
Qed.

(** ** Wave A1 -- conditional edge (tier T3) *)

(*@EDGE from=bounded_layered_treewidth_bounded_queue_number_statement to=planar_graphs_bounded_queue_number_statement kind=implies status=conditional external="external_layered_treewidth_planar_statement" proof=bounded_layered_treewidth_bounded_queue_number_implies_planar_graphs_bounded_queue_number cite="gc:e126; V. Dujmovic, P. Morin, D. R. Wood, Layered separators in minor-closed graph classes with applications, JCTB 127 (2017) 111-147 (planar graphs have layered treewidth at most 3)" note="q := f 3 + 1. The external theorem gives layered_tw_le G 3 for every wagner_planar G, the source a queue layout in the width_params form (injective key ord : G -> nat, queue map q e < f 3, no nested pair in one queue); sorting enum G by the key makes positions follow the key (queue_layouts.sort_index_lt), the colour inord (q e) in 'I_(f 3 + 1) is faithful on edges, and an X158-nested pair (a < b < c < d, e = {a,d}, g = {b,c}, queue_layouts.x158_edge_ends) is a width_params-nested pair." *)
(** External theorem: V. Dujmovic, P. Morin and D. R. Wood, "Layered separators in minor-closed graph classes with applications", J. Combin. Theory Ser. B 127 (2017) 111-147, arXiv:1306.1595; combined with K. Wagner, Math. Ann. 114 (1937) 570-590 (planar = no K5 and no K3,3 minor, the [wagner_planar] hypothesis).
    Claim: every planar graph has layered treewidth at most 3: there are a layering (adjacent
      vertices in the same or in consecutive layers, e.g. the BFS layering) and a tree
      decomposition every bag of which contains at most 3 vertices of each layer.  The Prop
      below states it on the [layered_tw_le] vocabulary of minor-theory width_params (a layering
      [L : G -> nat] and an [sdecomp] over a forest whose bags meet every layer in at most 3
      vertices, the width counted in vertices as in the source) for the [wagner_planar] graphs
      (no K5 and no K3,3 minor), which are exactly the planar graphs by Wagner's theorem.
      Not formalized here. *)
Definition external_layered_treewidth_planar_statement : Prop :=
  forall G : sgraph, wagner_planar G -> layered_tw_le G 3.

Theorem bounded_layered_treewidth_bounded_queue_number_implies_planar_graphs_bounded_queue_number :
  external_layered_treewidth_planar_statement ->
  bounded_layered_treewidth_bounded_queue_number_statement ->
  planar_graphs_bounded_queue_number_statement.
Proof.
move=> Ext [f Hf]; exists (f 3).+1 => G pG.
have [ord [q [oi qlt nest]]] := Hf 3 G (Ext G pG).
pose s := sort (fun x y => ord x <= ord y) (enum G).
have si a b : (index a s < index b s) = (ord a < ord b) := sort_index_lt a b oi.
exists s, (fun e => inord (q e)); split.
- by rewrite sort_uniq enum_uniq.
- by rewrite size_sort cardE.
move=> e g eE gE eg ceg [a [b [c [d [[ae [de [ad iad]]] [[bg [cg [bc ibc]]] [iab [ibc' icd]]]]]]]].
have [ee ead] := x158_edge_ends eE ae de ad.
have [ge gbc] := x158_edge_ends gE bg cg bc.
have qe : q e = q g.
  have eE' : e \in E(G) by rewrite ee in_edges.
  have gE' : g \in E(G) by rewrite ge in_edges.
  move/(congr1 val): ceg; rewrite /= !inordK //.
  - by rewrite ltnS ltnW // qlt.
  - by rewrite ltnS ltnW // qlt.
apply: (nest a d b c ead gbc); first by rewrite -ee -ge.
- by rewrite -si.
- by rewrite -si.
- by rewrite -si.
Qed.

(** ** Blocked / kept-candidate cross-package relations (recorded, not stated) *)

(*@EDGE from=jaegers_modular_orientation_statement to=mapping_planar_graphs_to_odd_cycles_statement kind=implies status=candidate cite="gc:e015" note="BLOCKED: planar duality (cycles of G correspond to minimal edge cuts of the planar dual) needs a real planarity/dual layer (F31)" *)
(*@EDGE from=kt_subdivision_clique_count_asymptotic_statement to=number_of_cliques_in_minor_closed_classes_statement kind=implies status=candidate cite="gc:e054" note="BLOCKED: the source is asymptotic (eventually in t) while the target is a uniform exists c forall t bound; small t not covered as encoded" *)
(*@EDGE from=fiftyseven_regular_moore_graph_statement to=triangle_free_strongly_regular_graphs_statement kind=implies status=candidate cite="gc:e147" note="BLOCKED: needs the seven known triangle-free strongly regular graphs constructed in the spectral layer" *)
(*@EDGE from=matthews_sumner_four_connected_claw_free_statement to=bondy_linear_cycle_cubic_statement kind=implies status=candidate cite="gc:e244" note="keep candidate: Fleischner-Jackson / Kochol equivalences (dominating cycles), not compactly statable as an external theorem" *)

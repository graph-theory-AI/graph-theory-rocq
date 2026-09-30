(** * Minor.conjectures.grounding_X220 — grounding lemmas for wave X220.

    Qed-closed, axiom-free sanity results for the ten X220 statements and for the
    primitives they introduce (walls, theta/prism, even wheels, twin-width,
    clique-width, small classes, shallow minors).

    Per statement: a NON-VACUITY witness (the hypotheses are satisfiable by a
    concrete graph or class, usually together with the conclusion) and a
    GUARD-HAS-TEETH lemma (the obvious degenerate witness fails the guard, or the
    conclusion is not automatic). *)

From GTBase Require Import base.
From GraphTheory Require Import minor.
From Minor.foundations Require Import containment width_params.
From Minor.conjectures Require Import X27 X42 X220.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Toolkit: the empty graph and small complete graphs ******************)

Lemma card0_absurd (T : finType) (x : T) : #|T| = 0 -> False.
Proof.
move=> T0; have hx : 0 < #|T| by apply/card_gt0P; exists x.
by rewrite T0 in hx.
Qed.

Lemma K0_void (x : 'K_0) : False.
Proof. by case: x => m; rewrite ltn0. Qed.

Lemma card_K0 : #|'K_0| = 0.
Proof. exact: card_ord. Qed.

Lemma K0_setT : [set: 'K_0] = set0.
Proof. by apply/setP => x; case: (K0_void x). Qed.

(** No sequence of more than three distinct vertices exists in ['K_0], so ['K_0]
    has no hole at all. *)
Lemma K0_no_hole (c : seq 'K_0) : x27_hole c -> False.
Proof.
case=> /andP[_ uc] [sz _].
by move: (leq_trans sz (uniq_size_card uc)); rewrite card_K0.
Qed.

(** A graph with no vertex has no edge. *)
Lemma empty_no_edges (H : sgraph) : #|H| = 0 -> #|E(H)| = 0.
Proof.
move=> H0; apply/eqP; rewrite cards_eq0; apply/eqP; apply/setP => e.
rewrite inE; apply/negbTE; apply/negP => /edgesP [x [y [_ _]]].
exact: (card0_absurd x H0).
Qed.

(** ['K_2] really has an edge. *)
Lemma K2_edge : (ord0 : 'K_2) -- (@Ordinal 2 1 isT).
Proof. by rewrite /edge_rel. Qed.

(** ** Row 1 — arxiv:2008.05504#01 (induced wall or line graph of a wall) ***)

Lemma card_wall (t : nat) : #|x220_wall t| = t * t.
Proof. by rewrite card_prod !card_ord. Qed.

(** NON-VACUITY: the 2-by-2 wall really has an edge, so the conclusion of the
    statement is about a graph with edges, and every wall contains an induced
    copy of itself. *)
Lemma X220_wall_has_edge :
  ((ord0, ord0) : x220_wall 2) -- ((ord0, @Ordinal 2 1 isT) : x220_wall 2).
Proof. by rewrite /edge_rel /= /x220_wall_rel /x220_wall_r0 /=. Qed.

Lemma X220_wall_nonvacuous (k : nat) :
  has_induced_copy (x220_wall k) (x220_wall k) \/
  has_induced_copy (x220_wall k) (sline_graph (x220_wall k)).
Proof. by left; exact: has_induced_copy_refl. Qed.

(** GUARD HAS TEETH: a smaller wall does NOT contain a larger wall, so the
    conclusion of the statement is not automatic. *)
Lemma X220_wall_guard_teeth : ~ has_induced_copy (x220_wall 1) (x220_wall 2).
Proof. by move/has_induced_copy_card; rewrite !card_wall. Qed.

(** ** Row 2 — arxiv:2109.01310#00 (four excluded families, log treewidth) **)

(** Every subdivision of a wall with an edge has an edge, hence its line graph
    has a vertex — used to discharge the fourth exclusion for ['K_0]. *)
Lemma X220_subdiv_wall2_edge (W : sgraph) :
  is_subdivision_of W (x220_wall 2) -> exists x y : W, x -- y.
Proof.
move=> /is_subdivision_ofW sub.
exact: (has_subdivision_edge sub X220_wall_has_edge).
Qed.

(** NON-VACUITY: at t = 2 the empty graph satisfies all four exclusions, and the
    conclusion holds for it with c = 0. *)
Lemma X220_four_family_nonvacuous :
  [/\ ~ has_induced_copy 'K_0 ('K_2),
      ~ has_induced_copy 'K_0 (KB 2 2),
      (forall W : sgraph, is_subdivision_of W (x220_wall 2) -> ~ has_induced_copy 'K_0 W),
      (forall W : sgraph, is_subdivision_of W (x220_wall 2) ->
         ~ has_induced_copy 'K_0 (sline_graph W)) &
      tw_le 'K_0 (0 * (trunc_log 2 #|'K_0|).+1)].
Proof.
split.
- by move/has_induced_copy_card; rewrite card_K0 card_ord.
- by move/has_induced_copy_card; rewrite card_K0 card_sum !card_ord.
- move=> W sub /has_induced_copy_card; rewrite card_K0 leqn0 => /eqP W0.
  by move: (is_subdivision_of_card sub); rewrite W0 card_wall.
- move=> W sub /has_induced_copy_card; rewrite card_K0 leqn0 => /eqP L0.
  have [x [y xy]] := X220_subdiv_wall2_edge sub.
  by move: (sline_graph_card_gt0 xy); rewrite L0.
- by rewrite mul0n; apply: tw_le_card; rewrite card_K0.
Qed.

(** GUARD HAS TEETH: the conclusion is not automatic — a graph with an edge does
    NOT have treewidth 0, which is what the bound becomes at c = 0. *)
Lemma X220_log_treewidth_guard_teeth : ~ tw_le 'K_2 0.
Proof. by move=> tw; move: (tw_le0_edgeless (ord0 : 'K_2) (@Ordinal 2 1 isT) tw); rewrite K2_edge. Qed.

(** ** Row 3 — arxiv:2203.06775#00 (C_4, diamond, theta, prism, even wheel) **)

Lemma card_diamond : #|x42_diamond| = 4.
Proof. by rewrite card_sum !card_bool. Qed.

Lemma card_prism3 : #|x220_prism3| = 6.
Proof. exact: card_ord. Qed.

Lemma card_S123 : #|x220_S123| = 7.
Proof. exact: card_ord. Qed.

(** Every theta has at least five vertices, and every prism at least six. *)
Lemma X220_theta_card (H : sgraph) : x220_theta H -> 5 <= #|H|.
Proof. by move/is_subdivision_of_card; rewrite card_sum !card_ord. Qed.

Lemma X220_prism_card (H : sgraph) : x220_prism H -> 6 <= #|H|.
Proof.
case=> m _; rewrite -card_prism3.
exact: (@leq_card _ _ (sdm_branch m) (@sdm_inj _ _ m)).
Qed.

(** NON-VACUITY: at t = 2 the empty graph satisfies the six hypotheses and has
    treewidth 0. *)
Lemma X220_cstar_nonvacuous :
  [/\ ~ has_induced_copy 'K_0 (cycle_graph 4),
      ~ has_induced_copy 'K_0 x42_diamond,
      (forall H : sgraph, x220_theta H -> ~ has_induced_copy 'K_0 H),
      (forall H : sgraph, x220_prism H -> ~ has_induced_copy 'K_0 H) &
      [/\ x220_even_wheel_free ('K_0), x220_clique_free 'K_0 2 & tw_le 'K_0 0]].
Proof.
split.
- by move/has_induced_copy_card; rewrite card_K0 card_ord.
- by move/has_induced_copy_card; rewrite card_K0 card_diamond.
- move=> H th /has_induced_copy_card; rewrite card_K0 leqn0 => /eqP H0.
  by move: (X220_theta_card th); rewrite H0.
- move=> H pr /has_induced_copy_card; rewrite card_K0 leqn0 => /eqP H0.
  by move: (X220_prism_card pr); rewrite H0.
- split.
  + by move=> v c h _ _; case: (K0_no_hole h).
  + by move=> S _; move: (max_card (mem S)); rewrite card_K0 leqn0 => /eqP->.
  + by apply: tw_le_card; rewrite card_K0.
Qed.

(** GUARD HAS TEETH: the ['K_t]-free guard is load-bearing — ['K_3] is NOT
    ['K_3]-free, so it is excluded from the class at t = 3. *)
Lemma X220_clique_free_guard_teeth : ~ x220_clique_free 'K_3 3.
Proof. by move/(_ [set: 'K_3] (@Kn_clique 3)); rewrite cardsT card_ord. Qed.

(** ** Row 4 — arxiv:2305.16258#01 (even hole, K_t : logarithmic treewidth) **)

Lemma K0_even_hole_free : x27_even_hole_free 'K_0.
Proof. by move=> c h _; case: (K0_no_hole h). Qed.

(** NON-VACUITY: at t = 2 the empty graph is even-hole-free and ['K_2]-free, and
    the conclusion holds for it with c = 0. *)
Lemma X220_even_hole_kt_nonvacuous :
  [/\ x27_even_hole_free ('K_0), x220_clique_free 'K_0 2 &
      tw_le 'K_0 (0 * (trunc_log 2 #|'K_0|).+1)].
Proof.
split; [exact: K0_even_hole_free | | ].
- by move=> S _; move: (max_card (mem S)); rewrite card_K0 leqn0 => /eqP->.
- by rewrite mul0n; apply: tw_le_card; rewrite card_K0.
Qed.

(** GUARD HAS TEETH: reuse of [X220_clique_free_guard_teeth] — the ['K_t]-free
    hypothesis really excludes graphs, and the treewidth bound really excludes
    graphs with edges ([X220_log_treewidth_guard_teeth]). *)

(** ** Row 5 — arxiv:2305.16258#00 (even hole, diamond : bounded tree-alpha) **)

Lemma K0_alpha0 : α([set: 'K_0]) = 0.
Proof. by apply/eqP; rewrite alpha_eq0 K0_setT. Qed.

(** NON-VACUITY: the empty graph is even-hole-free and diamond-free, and has
    tree-independence number 0. *)
Lemma X220_tree_alpha_nonvacuous :
  [/\ x27_even_hole_free ('K_0), ~ has_induced_copy 'K_0 x42_diamond &
      tree_alpha_le 'K_0 0].
Proof.
split; [exact: K0_even_hole_free | | ].
- by move/has_induced_copy_card; rewrite card_K0 card_diamond.
- by apply: tree_alpha_le_all; rewrite K0_alpha0.
Qed.

(** GUARD HAS TEETH: the diamond-free guard really excludes a graph — the
    diamond itself is not diamond-free — and tree-alpha 0 forces emptiness. *)
Lemma X220_diamond_guard_teeth : has_induced_copy x42_diamond x42_diamond.
Proof. exact: has_induced_copy_refl. Qed.

Lemma X220_tree_alpha_guard_teeth : ~ tree_alpha_le 'K_1 0.
Proof. by move/tree_alpha_le0_empty; rewrite card_ord. Qed.

(** ** Rows 6 and 7 — arxiv:2511.03864#00 / #01 (tree-mu and tree-alpha) ****)

Lemma K0_edge_set : E('K_0) = set0.
Proof. by apply/eqP; rewrite -cards_eq0 (empty_no_edges card_K0). Qed.

Lemma K0_tree_mu : tree_mu_le 'K_0 1.
Proof.
exists tunit, (fun _ => [set: 'K_0]); split; first exact: triv_sdecomp.
move=> M [Msub _] _.
have -> : M = set0.
  apply/setP => e; rewrite inE; apply/negbTE; apply/negP => eM.
  by move: (Msub e eM); rewrite K0_edge_set inE.
by rewrite cards0.
Qed.

Lemma X220_tree_mu_nonvacuous :
  [/\ ~ has_induced_copy 'K_0 (KB 1 1), tree_mu_le 'K_0 1 &
      tree_alpha_le 'K_0 (x220_poly_eval [:: 1] 1)].
Proof.
split; [ | exact: K0_tree_mu | ].
- by move/has_induced_copy_card; rewrite card_K0 card_sum !card_ord.
- by apply: tree_alpha_le_all; rewrite K0_alpha0.
Qed.

(** GUARD HAS TEETH: the tree-mu parameter is load-bearing — a graph with an
    edge does NOT have induced matching treewidth 0. *)
Lemma X220_tree_mu_guard_teeth : ~ tree_mu_le 'K_2 0.
Proof.
by move=> t; move: (tree_mu_le0_edgeless (ord0 : 'K_2) (@Ordinal 2 1 isT) t); rewrite K2_edge.
Qed.

(** NON-VACUITY (row 7): the induced biclique number of the empty graph is 0. *)
Lemma X220_ibn_nonvacuous :
  [/\ x220_ibn 'K_0 0, tree_mu_le 'K_0 1 &
      tree_alpha_le 'K_0 (x220_poly_eval [:: 1] 0)].
Proof.
split; [ | exact: K0_tree_mu | ].
- split; first by apply: has_induced_copy_empty; rewrite card_sum !card_ord.
  move=> s /has_induced_copy_card; rewrite card_K0 card_sum !card_ord leqn0.
  by rewrite addn_eq0 => /andP[/eqP-> _].
- by apply: tree_alpha_le_all; rewrite K0_alpha0.
Qed.

(** GUARD HAS TEETH (row 7): the induced biclique number is not an arbitrary
    number — the empty graph does NOT have induced biclique number 1. *)
Lemma X220_ibn_guard_teeth : ~ x220_ibn 'K_0 1.
Proof.
by case=> /has_induced_copy_card; rewrite card_K0 card_sum !card_ord.
Qed.

(** ** Rows 8 and 9 — arxiv:2006.09877#00 / #01 (twin-width) ***************)

(** The class of graphs with no vertex, used as the concrete witness class. *)
Definition X220_Cnull (G : sgraph) : Prop := #|G| = 0.

Lemma X220_tww_empty (G : sgraph) : #|G| = 0 -> x220_twin_width_le G 0.
Proof.
move=> G0; exists [::]; split => //=.
- by apply: (leq_trans (leq_imset_card _ _)); rewrite G0.
- move=> P; rewrite inE => /eqP-> X /imsetP[x _ _].
  by case: (card0_absurd x G0).
Qed.

Lemma X220_Cnull_hereditary : x220_hereditary_class X220_Cnull.
Proof.
split=> [G H|G S]; rewrite /X220_Cnull.
- by move=> G0 /diso_card <-.
- by move=> G0; rewrite card_induced; apply/eqP; rewrite -leqn0 -G0 max_card.
Qed.

Lemma X220_Cnull_small : x220_small_class X220_Cnull.
Proof.
exists 1 => n F HF; case: (set_0Vmem F) => [->|[f fF]]; first by rewrite cards0.
have [G CG [h [hbij _]]] := HF f fF.
have n0 : n = 0.
  apply/eqP; rewrite -leqn0 -CG -[X in X <= _]card_ord.
  by case: hbij => g hg _; exact: (@leq_card _ _ h (can_inj hg)).
rewrite exp1n muln1.
have -> : n`! = 1 by rewrite n0 fact0.
apply: (leq_trans (max_card _)).
by rewrite card_ffun card_prod !card_ord n0 expn0.
Qed.

(** NON-VACUITY (row 8): the class of graphs with no vertex is hereditary and
    small, and its twin-width is bounded (by 0). *)
Lemma X220_small_conjecture_nonvacuous :
  [/\ x220_hereditary_class X220_Cnull, x220_small_class X220_Cnull &
      exists d : nat, forall G : sgraph, X220_Cnull G -> x220_twin_width_le G d].
Proof.
split; [exact: X220_Cnull_hereditary | exact: X220_Cnull_small | ].
by exists 0 => G; exact: X220_tww_empty.
Qed.

(** GUARD HAS TEETH (row 8): the hereditary hypothesis really excludes classes —
    "exactly two vertices" is not closed under induced subgraphs. *)
Lemma X220_hereditary_guard_teeth :
  ~ x220_hereditary_class (fun G : sgraph => #|G| = 2).
Proof.
case=> _ /(_ 'K_2 set0 (card_ord 2)).
by rewrite card_induced cards0.
Qed.

(** NON-VACUITY (row 9): the class of graphs with no vertex has polynomial
    expansion (witnessed by the zero polynomial). *)
Lemma X220_poly_expansion_nonvacuous : x220_polynomial_expansion X220_Cnull.
Proof.
exists [::] => G G0 r H [B [ctr [ctrB _ _ _]]].
have H0 : #|H| = 0.
  apply/eqP; rewrite -leqn0 leqNgt; apply/negP => /card_gt0P[x _].
  exact: (card0_absurd (ctr x) G0).
by rewrite empty_no_edges.
Qed.

(** NON-VACUITY of the shallow-minor primitive: every graph is its own 0-shallow
    minor (singleton branch sets). *)
Lemma X220_shallow_minor_refl (G : sgraph) : x220_shallow_minor G G 0.
Proof.
exists (fun x => [set x]), id; split.
- by move=> x; rewrite inE.
- move=> x v; rewrite inE => /eqP->; exists [::]; split=> //=.
  by rewrite andbT inE.
- by move=> x y xy; rewrite disjoints1 inE.
- by move=> x y xy; exists x, y; split=> //; rewrite inE.
Qed.

(** GUARD HAS TEETH (row 9): the expansion bound is not automatic — the zero
    polynomial fails already for ['K_3], which is its own 0-shallow minor. *)
Lemma X220_poly_expansion_guard_teeth :
  ~ (#|E('K_3)| <= x220_poly_eval [::] 0 * #|'K_3|).
Proof. by rewrite card_edge_Kn. Qed.

(** ** Row 10 — arxiv:2001.01607#02 (triangle, S(1,2,3) : clique-width) ****)

Lemma triangle_free_card2 (G : sgraph) : #|G| <= 2 -> triangle_free G.
Proof.
move=> le x y z xy yz zx.
have xy' : x != y by rewrite (sg_edgeNeq xy).
have c2 : #|[set x; y]| = 2 by rewrite cards2 xy'.
have full : [set x; y] = [set: G].
  by apply/eqP; rewrite eqEcard subsetT /= cardsT c2; exact: le.
have zin : z \in [set x; y] by rewrite full inE.
move: zin; rewrite !inE => /orP[/eqP e|/eqP e].
- by rewrite e sg_irrefl in zx.
- by rewrite e sg_irrefl in yz.
Qed.

(** NON-VACUITY: ['K_2] is triangle-free, has no induced S(1,2,3), and has
    clique-width at most 2 (one join of two labelled vertices). *)
Lemma X220_K2_cw2 : x220_clique_width_le 'K_2 2.
Proof.
exists (CwJoin 0 1 (CwUnion (CwLeaf 0) (CwLeaf 1))); split=> //.
exists (fun v : 'K_2 => val v); split.
- by move=> u v /val_inj.
- by move=> v /=; exact: ltn_ord.
- move=> i; rewrite /= ltnS leq_eqVlt ltnS leqn0.
  case/orP => [/eqP->|/eqP->]; [by exists (@Ordinal 2 1 isT) | by exists ord0].
- by move=> u v; case: u => -[|[|u]] pu; case: v => -[|[|v]] pv.
Qed.

Lemma X220_cw_nonvacuous :
  [/\ triangle_free ('K_2), ~ has_induced_copy 'K_2 x220_S123 &
      x220_clique_width_le 'K_2 2].
Proof.
split; [by apply: triangle_free_card2; rewrite card_ord | | exact: X220_K2_cw2].
by move/has_induced_copy_card; rewrite !card_ord.
Qed.

(** GUARD HAS TEETH: no graph has clique-width 0 — every expression has a leaf,
    whose label would have to be below 0. *)
Lemma X220_cw_wf0 (e : x220_cw_expr) : ~~ x220_cw_wf 0 e.
Proof.
elim: e => [i|a IHa b _|i j a _|i j a _] //=.
by rewrite (negbTE IHa).
Qed.

Lemma X220_cw_guard_teeth (G : sgraph) : ~ x220_clique_width_le G 0.
Proof. by case=> e [wf _]; move: (X220_cw_wf0 e); rewrite wf. Qed.

Print Assumptions bounded_degree_induced_wall_or_line_wall_statement.
Print Assumptions four_family_free_logarithmic_treewidth_statement.
Print Assumptions theta_prism_even_wheel_free_bounded_treewidth_statement.
Print Assumptions even_hole_kt_free_logarithmic_treewidth_statement.
Print Assumptions even_hole_diamond_free_bounded_tree_alpha_statement.
Print Assumptions tree_mu_ktt_free_polynomial_tree_alpha_statement.
Print Assumptions bounded_tree_mu_polynomial_biclique_tree_alpha_statement.
Print Assumptions small_hereditary_class_bounded_twin_width_statement.
Print Assumptions polynomial_expansion_bounded_twin_width_statement.
Print Assumptions triangle_s123_free_bounded_clique_width_statement.
Print Assumptions X220_wall_nonvacuous.
Print Assumptions X220_wall_guard_teeth.
Print Assumptions X220_four_family_nonvacuous.
Print Assumptions X220_log_treewidth_guard_teeth.
Print Assumptions X220_cstar_nonvacuous.
Print Assumptions X220_clique_free_guard_teeth.
Print Assumptions X220_even_hole_kt_nonvacuous.
Print Assumptions X220_tree_alpha_nonvacuous.
Print Assumptions X220_tree_alpha_guard_teeth.
Print Assumptions X220_tree_mu_nonvacuous.
Print Assumptions X220_tree_mu_guard_teeth.
Print Assumptions X220_ibn_nonvacuous.
Print Assumptions X220_ibn_guard_teeth.
Print Assumptions X220_small_conjecture_nonvacuous.
Print Assumptions X220_hereditary_guard_teeth.
Print Assumptions X220_poly_expansion_nonvacuous.
Print Assumptions X220_shallow_minor_refl.
Print Assumptions X220_poly_expansion_guard_teeth.
Print Assumptions X220_cw_nonvacuous.
Print Assumptions X220_cw_guard_teeth.

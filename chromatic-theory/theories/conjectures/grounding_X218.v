(** * Chromatic.conjectures.grounding_X218 -- grounding lemmas for wave X218.

    Qed-closed, axiom-free sanity results for the primitives of [X218.v] and for
    the hypothesis blocks of its six statements: a SATISFIABLE witness for every
    guard and a GUARD-HAS-TEETH lemma for every notion that could collapse.
    They validate the statements; they do not prove them.  The [poly_chi_bounded]
    wrapper itself is grounded where it lives, in
    [chromatic-theory/theories/foundations/chi_bounding.v].  The odd-minor row,
    re-encoded on 2026-11-02, has certificates in X271's claim shape
    (hyp_inhabited, not_trivially_true, helper_sanity). *)

From GraphTheory Require Import bij.
From GTBase Require Import base.
From Chromatic.foundations Require Import chi_bounding.
From Chromatic.conjectures Require Import U8 X130 X194 X218.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The forest / tree guard shared by three statements *****************)

(** Non-vacuity: the one-vertex graph is a forest and a tree. *)
Lemma x218_is_tree_sunit : is_tree [set: sunit].
Proof.
split; first exact: unit_forest.
have -> : [set: sunit] = [set (tt : sunit)]
  by apply/setP => x; case: x; rewrite !inE eqxx.
exact: connected1.
Qed.

(** Guard has teeth: the triangle is not a forest, so "H is a forest" really
    restricts the statements' universe. *)
Lemma x218_not_forest_K3 : ~ is_forest [set: 'K_3].
Proof.
move=> Hf; have card3 : (3 <= #|'K_3|)%N by rewrite card_ord.
by have [x [y [xy nadj]]] := forest3 Hf card3; rewrite /edge_rel /= xy in nadj.
Qed.

(** ** [x218_path_induced_copy] ******************************************)

(** Non-vacuity: every nonempty graph contains a path-induced copy of the
    one-vertex rooted tree. *)
Lemma x218_path_induced_copy_K1 (G : sgraph) (x : G) :
  x218_path_induced_copy (ord0 : 'K_1) G.
Proof.
have nthc : forall (l : seq ('K_1)) (i : nat),
    nth x (map (fun _ : 'K_1 => x) l) i = x.
  move=> l i; case: (ltnP i (size l)) => [lt|ge].
    by rewrite (nth_map ord0) // size_map.
  by rewrite nth_default // size_map.
exists (fun _ => x); split.
- by move=> a b _; rewrite (ord1 a) (ord1 b).
- by move=> u v; rewrite /edge_rel /= (ord1 u) (ord1 v) eqxx.
- by move=> p _ _ i j _ _; rewrite !nthc sg_irrefl.
Qed.

(** Guard has teeth: a graph smaller than [T] has no path-induced copy of
    [(T,r)], because the copy is injective. *)
Lemma x218_no_path_induced_copy_card (T G : sgraph) (r : T) :
  #|G| < #|T| -> ~ x218_path_induced_copy r G.
Proof. by move=> lt [phi [inj _ _]]; move: (leq_card phi inj); rewrite leqNgt lt. Qed.

(** ** [x218_complete_multipartite] **************************************)

(** Identity: [K_d(t)] has exactly [d*t] vertices. *)
Lemma x218_multipartite_card d t : #|x218_complete_multipartite d t| = d * t.
Proof. by rewrite card_prod !card_ord. Qed.

(** Guard has teeth at the boundary: [K_1(t)] is EDGELESS, so the [d >= 1]
    guard of [x218_multibounding] is the degenerate end of the family and the
    content of the definition lies at [d >= 2]. *)
Lemma x218_multipartite_1_edgeless t (x y : x218_complete_multipartite 1 t) :
  ~~ (x -- y).
Proof.
by rewrite /edge_rel /= /x218_multipartite_rel /GTBase.complete_multipartite_graphs.complete_multipartite_rel (ord1 x.1) (ord1 y.1) eqxx.
Qed.

(** Structural law: multiboundedness is used at a fixed [d], and then bounds
    every [H]-free graph with no [K_d(t)] subgraph.  After the 2026-09-24
    re-encoding the coefficients come from the two bounding FUNCTIONS, read at
    that [d]. *)
Lemma x218_multibounding_at (H : sgraph) :
  x218_multibounding H ->
  exists c e : nat,
    forall (t : nat) (G : sgraph),
      1 <= t -> ~ has_induced H G ->
      ~ has_subgraph G (x218_complete_multipartite 2 t) ->
      χ([set: G]) <= c * t ^ e.
Proof. by move=> [c [e Hce]]; exists (c 2), (e 2); exact: (Hce 2 isT). Qed.

(** The OLD, un-Skolemised reading of multiboundedness -- the body of
    [x218_multibounding] BEFORE the 2026-09-24 re-encoding: for every [d >= 1]
    SOME pair of coefficients works, with no function of [d] produced. *)
Definition x218_multibounding_pointwise (H : sgraph) : Prop :=
  forall d : nat, 1 <= d ->
    exists c e : nat,
      forall (t : nat) (G : sgraph),
        1 <= t ->
        ~ has_induced H G ->
        ~ has_subgraph G (x218_complete_multipartite d t) ->
        χ([set: G]) <= c * t ^ e.

(** The re-encoded form IMPLIES the old one: read the two coefficient functions
    at [d].  So the re-encoding is (at least) as strong as the body it replaces.
    The converse needs countable choice -- a choice of one coefficient pair per
    [d] -- which is exactly why the old body could not produce the single
    chi-bounding function that corpus edge e035 asks for. *)
Lemma x218_multibounding_pointwiseP (H : sgraph) :
  x218_multibounding H -> x218_multibounding_pointwise H.
Proof. by move=> [c [e Hce]] d dpos; exists (c d), (e d); exact: (Hce d dpos). Qed.

(** Non-vacuity: every NONEMPTY graph contains an induced copy of ['K_1] (the
    image of the one-vertex isubgraph picking that vertex). *)
Lemma x218_has_induced_K1 (G : sgraph) (x : G) : has_induced 'K_1 G.
Proof.
have inj1 : injective (fun _ : 'K_1 => x).
  by move=> a b _; rewrite (ord1 a) (ord1 b).
have mono1 : {mono (fun _ : 'K_1 => x) : a b / a -- b}.
  by move=> a b; rewrite (ord1 a) (ord1 b) !sg_irrefl.
by exists [set y in codom (ISubgraph inj1 mono1)]; constructor; exact: isubgraph_induced.
Qed.

(** Non-vacuity of the RE-ENCODED [x218_multibounding]: ['K_1] is multibounding,
    with both coefficient functions constantly zero.  A ['K_1]-free graph has no
    vertex at all, so its chromatic number is zero and every bound holds.  This
    shows the new existential form is satisfiable (and ['K_1] is a forest, so the
    conclusion of [every_forest_is_multibounding_statement] is satisfiable at one
    of its instances). *)
Lemma x218_multibounding_K1 : x218_multibounding 'K_1.
Proof.
exists (fun _ => 0), (fun _ => 0) => d _ t G _ nind _.
apply: leq_trans (leq_chi _) _; rewrite mul0n leqn0 cards_eq0.
apply/eqP/setP => y.
by case: (nind (x218_has_induced_K1 y)).
Qed.

(** ** [x218_odd_minor] **************************************************)

(** Non-vacuity: every graph is an odd minor of itself (singleton branch sets,
    constant 2-colouring; the inside-branch condition is vacuous). *)
Lemma x218_odd_minor_refl (G : sgraph) : x218_odd_minor G G.
Proof.
exists (fun x : G => [set x]), (fun _ => true); split.
- by move=> x; apply/set0Pn; exists x; rewrite inE.
- by move=> x; exact: connected1.
- by move=> x y xy; rewrite disjoints1 inE.
- by move=> x u v; rewrite !inE => /eqP-> /eqP->; rewrite sg_irrefl.
- by move=> x y xy; exists x, y; rewrite !inE !eqxx.
Qed.

(** Guard has teeth: [K_2] is not an odd minor of [K_1] -- two nonempty
    disjoint branch sets do not fit in a one-vertex graph. *)
Lemma x218_no_odd_minor_K2_in_K1 : ~ x218_odd_minor 'K_1 'K_2.
Proof.
case=> B [sigma] [ne _ disj _ _].
pose a : 'K_2 := ord0.
pose b : 'K_2 := @Ordinal 2 1 isT.
have ab : a != b by [].
have [u uA] : exists u, u \in B a by apply/set0Pn; exact: ne a.
have [v vB] : exists v, v \in B b by apply/set0Pn; exact: ne b.
have uv : u = v by rewrite (ord1 u) (ord1 v).
have uB : u \in B b by rewrite uv.
by move: (disj a b ab); rewrite -setI_eq0 => /eqP/setP/(_ u); rewrite !inE uA uB.
Qed.

(** ** [x218_connected_treedepth_at_most] ********************************)

(** Non-vacuity: the one-vertex graph has connected tree-depth at most one. *)
Lemma x218_connected_treedepth_sunit : x218_connected_treedepth_at_most sunit 1.
Proof.
exists sunit; split.
- have -> : [set: sunit] = [set (tt : sunit)].
    by apply/setP => x; case: x; rewrite !inE eqxx.
  exact: connected1.
- exact: has_subgraph_refl.
- by exists (fun _ => ord0) => x y p; case: x; case: y; rewrite eqxx.
Qed.

(** ** [x218_defective_chromatic_class_le] / [x218_clustered_...] ********)

(** Non-vacuity: the empty class has defective and clustered chromatic number
    at most zero. *)
Lemma x218_defective_class_empty :
  x218_defective_chromatic_class_le (fun _ : sgraph => False) 0.
Proof. by exists 0 => G. Qed.

Lemma x218_clustered_class_empty :
  x218_clustered_chromatic_class_le (fun _ : sgraph => False) 0.
Proof. by exists 0 => G. Qed.

(** Guard has teeth: zero colours do not colour a nonempty graph, so the
    number of colours in both class parameters really bites. *)
Lemma x218_not_defective_class_all :
  ~ x218_defective_chromatic_class_le (fun _ : sgraph => True) 0.
Proof. by case=> m /(_ 'K_1 I) [col _]; case: (col ord0) => k; rewrite ltn0. Qed.

Lemma x218_not_clustered_class_all :
  ~ x218_clustered_chromatic_class_le (fun _ : sgraph => True) 0.
Proof. by case=> c /(_ 'K_1 I) [col _]; case: (col ord0) => k; rewrite ltn0. Qed.

(** ** The re-encoded odd-minor row, arxiv:2308.15721#00 (2026-11-02) *****

    X271's claim shape: helper_sanity for [x218_odd_minor_tree_model] and
    [x218_ctd_at_most], hyp_inhabited (the hypotheses hold together at H = K_2,
    k = 2, and the statement gives the defective bound) and not_trivially_true
    (without "no odd H-minor" in the clustered clause the statement is false at
    H = K_1, k = 1, and that variant implies it; a second one drops "k is exactly
    ctd(H)"). *)

Definition g218_o1 : 'I_2 := @Ordinal 2 1 isT.

(** helper sanity: K_n has an odd K_n minor (singleton branch sets, one colour). *)
Lemma g218_Kn_odd_tree (n : nat) : x218_odd_minor_tree_model 'K_n 'K_n.
Proof.
exists (fun x => [set x]), (fun _ => true); split.
- by move=> x; apply/set0Pn; exists x; rewrite inE.
- by move=> x u v; rewrite !inE => /eqP -> /eqP ->; exact: connect0.
- by move=> x y xy; rewrite disjoints1 in_set1 (negbTE xy).
- by move=> x y xy; exists x, y; rewrite !inE !eqxx.
Qed.

(** helper sanity: K_1 has no odd K_2 minor. *)
Lemma g218_K1_no_odd_tree_K2 : ~ x218_odd_minor_tree_model 'K_1 'K_2.
Proof.
case=> B [sigma [ne _ dis _]].
have [u uB0] := set0Pn _ (ne ord0).
have [v vB1] := set0Pn _ (ne g218_o1).
have uv : u = v by rewrite (ord1 u) (ord1 v).
move: (dis ord0 g218_o1 isT); rewrite disjoint_subset => /subsetP/(_ u uB0).
by rewrite inE uv vB1.
Qed.

(** helper sanity: ctd(K_1) <= 1, and nothing has ctd <= 0. *)
Lemma g218_ctd_K1 : x218_ctd_at_most 'K_1 1.
Proof.
split=> //; exists ord0.
have F (v : induced (~: [set (ord0 : 'K_1)])) : False.
  by case: v => x; rewrite !inE (ord1 x) eqxx.
by exists (fun v => False_rect _ (F v)) => x; case: (F x).
Qed.

Lemma g218_not_ctd_0 (H : sgraph) : ~ x218_ctd_at_most H 0.
Proof. by case. Qed.

Lemma g218_one (v : induced (~: [set (ord0 : 'K_2)])) : val v = g218_o1.
Proof.
move: (valP v); rewrite !inE => vn0; apply: val_inj; move: (val v) vn0 => w.
by case: w => [[|[|m]] p].
Qed.

(** helper sanity: ctd(K_2) = 2 (a rooted tree on two vertices has vertex-height 2: the convention's off-by-one). *)
Lemma g218_ctd_K2 : x218_ctd_at_most 'K_2 2 /\ ~ x218_ctd_at_most 'K_2 1.
Proof.
split.
- split=> //; exists ord0; exists (fun _ => ord0) => x y p xy.
  by move: xy; rewrite -(inj_eq val_inj) (g218_one x) (g218_one y) eqxx.
- case=> _ [r [rank _]].
  have [w wr] : exists (w : 'K_2), w \in ~: [set r].
    case: (eqVneq r ord0) => [->|rn0]; first by exists g218_o1; rewrite !inE.
    by exists ord0; rewrite !inE eq_sym.
  by case: (rank (Sub w wr)).
Qed.

(** helper sanity: the graph with no vertex has no connected tree-depth (no rooted tree on an empty vertex set), so
    the body is vacuous there. *)
Lemma g218_no_ctd_empty (k : nat) : ~ x218_ctd_at_most 'K_0 k.
Proof. by case=> _ [[]]. Qed.

(** hyp_inhabited: H = K_2 has connected tree-depth exactly 2, and the statement gives defective chromatic number at
    most 1 for the graphs with no odd K_2 minor. *)
Definition g218_ominf_hyp_claim : Prop :=
  [/\ x218_ctd_at_most 'K_2 2, ~ x218_ctd_at_most 'K_2 1 &
      (odd_minor_free_defective_clustered_treedepth_statement ->
         x218_defective_chromatic_class_le (fun G : sgraph => ~ x218_odd_minor_tree_model G 'K_2) 1)].

Theorem g218_ominf_hyp_inhabited : g218_ominf_hyp_claim.
Proof.
have [c2 nc1] := g218_ctd_K2.
by split=> // S; case: (S 'K_2 2 c2 nc1) => _ [].
Qed.

(** not_trivially_true: without "no odd H-minor" in the clustered clause the statement is false at H = K_1, k = 1 (no
    0-colouring of a nonempty graph), and that variant implies the statement. *)
Definition g218_ominf_no_free : Prop :=
  forall (H : sgraph) (k : nat),
    x218_ctd_at_most H k ->
    ~ x218_ctd_at_most H k.-1 ->
    x218_clustered_chromatic_class_le (fun _ : sgraph => True) (2 * k - 2) /\
    x218_defective_chromatic_class_le (fun G : sgraph => ~ x218_odd_minor_tree_model G H) (k - 1) /\
    (forall j : nat, j.+1 < k ->
       ~ x218_defective_chromatic_class_le (fun G : sgraph => ~ x218_odd_minor_tree_model G H) j).

Definition g218_ominf_ntt_claim : Prop :=
  ~ g218_ominf_no_free /\ (g218_ominf_no_free -> odd_minor_free_defective_clustered_treedepth_statement).

Theorem g218_ominf_not_trivially_true : g218_ominf_ntt_claim.
Proof.
split.
- move=> h; apply: x218_not_clustered_class_all.
  by case: (h 'K_1 1 g218_ctd_K1 (@g218_not_ctd_0 'K_1)).
- move=> h H k c nc; have [[c0 cl] rest] := h H k c nc.
  by split=> //; exists c0 => G _; exact: cl G I.
Qed.

(** helper_sanity: connected tree-depth is monotone in the bound (X194's ranking into a wider ordinal). *)
Lemma g218_ctd_mono (H : sgraph) (k : nat) : x218_ctd_at_most H k -> x218_ctd_at_most H k.+1.
Proof.
case=> k0 [r [rank rk]]; split=> //; exists r.
move: rank rk; case: k k0 => [//|k _] rank rk /=.
exists (fun v => widen_ord (leqnSn k) (rank v)) => x y p xy pth lst e.
have e' : rank x = rank y by apply: val_inj; move/(congr1 val): e.
by have [z [zp lt]] := rk x y p xy pth lst e'; exists z.
Qed.

(** helper_sanity: two isolated vertices, X218's edgeless [K_1(2)], have tree-depth 1 but connected tree-depth 2,
    the case that separates ctd from td (arXiv.tex l.153, footnote: two components of tree-depth td). *)
Lemma g218_td_2K1 : x194_treedepth_at_most (x218_complete_multipartite 1 2) 1.
Proof.
exists (fun _ => ord0) => x y [|z p] xy /=.
- by move=> _ e; rewrite e eqxx in xy.
- by case/andP=> xz _; move: (x218_multipartite_1_edgeless x z); rewrite xz.
Qed.

Lemma g218_ctd_2K1 :
  x218_ctd_at_most (x218_complete_multipartite 1 2) 2 /\ ~ x218_ctd_at_most (x218_complete_multipartite 1 2) 1.
Proof.
split.
- split=> //; exists (ord0, ord0); exists (fun _ => ord0) => x y [|z p] xy /=.
  + by move=> _ e; rewrite e eqxx in xy.
  + by case/andP=> xz _; case: (negP (x218_multipartite_1_edgeless (val x) (val z)) xz).
- case=> _ [r [rank _]].
  have [w wr] : exists (w : x218_complete_multipartite 1 2), w \in ~: [set r].
    case: (eqVneq r (ord0, ord0)) => [->|rn0]; first by exists (ord0, g218_o1); rewrite !inE.
    by exists (ord0, ord0); rewrite !inE eq_sym.
  by case: (rank (Sub w wr)).
Qed.

(** every graph with a vertex has an odd K_1-minor (one vertex as its branch set). *)
Lemma g218_K1_odd_tree (G : sgraph) (w : G) : x218_odd_minor_tree_model G 'K_1.
Proof.
exists (fun _ => [set w]), (fun _ => true); split.
- by move=> x; apply/set0Pn; exists w; rewrite inE.
- by move=> x u v; rewrite !inE => /eqP -> /eqP ->; exact: connect0.
- by move=> x y; rewrite (ord1 x) (ord1 y) eqxx.
- by move=> x y; rewrite (ord1 x) (ord1 y) sg_irrefl.
Qed.

(** so the graphs with no odd K_1-minor (only the graph with no vertex) have defective chromatic number 0. *)
Lemma g218_defective_no_odd_K1 :
  x218_defective_chromatic_class_le (fun G : sgraph => ~ x218_odd_minor_tree_model G 'K_1) 0.
Proof.
exists 0 => G noK1.
have F (v : G) : False by exact: noK1 (g218_K1_odd_tree v).
by exists (fun v => False_rect _ (F v)) => v; case: (F v).
Qed.

(** not_trivially_true: without "~ x218_ctd_at_most H k.-1" (k is exactly ctd(H)) the statement is false at H = K_1,
    k = 2: its lower clause at j = 0 denies the 0-colouring of the graph with no vertex; and that variant implies the
    statement. *)
Definition g218_ominf_no_exact : Prop :=
  forall (H : sgraph) (k : nat),
    x218_ctd_at_most H k ->
    x218_clustered_chromatic_class_le (fun G : sgraph => ~ x218_odd_minor_tree_model G H) (2 * k - 2) /\
    x218_defective_chromatic_class_le (fun G : sgraph => ~ x218_odd_minor_tree_model G H) (k - 1) /\
    (forall j : nat, j.+1 < k ->
       ~ x218_defective_chromatic_class_le (fun G : sgraph => ~ x218_odd_minor_tree_model G H) j).

Definition g218_ominf_exact_ntt_claim : Prop :=
  ~ g218_ominf_no_exact /\ (g218_ominf_no_exact -> odd_minor_free_defective_clustered_treedepth_statement).

Theorem g218_ominf_exact_not_trivially_true : g218_ominf_exact_ntt_claim.
Proof.
split.
- move=> h; have [_ [_ low]] := h 'K_1 2 (g218_ctd_mono g218_ctd_K1).
  exact: low 0 isT g218_defective_no_odd_K1.
- by move=> h H k c _; exact: h H k c.
Qed.

(** ** [x130_frac_chi_le] at the X218 instance ***************************)

(** Non-vacuity: the one-vertex graph has fractional chromatic number at most
    1/1, so the conclusion of the sublinearity statement is satisfiable. *)
Lemma x218_frac_chi_K1 : x130_frac_chi_le 'K_1 1 1.
Proof.
exists 1, 1, (fun _ => [set: 'I_1]); split => //.
split; first by move=> v; rewrite cardsT card_ord.
by move=> x y; rewrite /edge_rel /= (ord1 x) (ord1 y) eqxx.
Qed.

(** Guard has teeth: a graph with an edge does not have fractional chromatic
    number at most 0. *)
Lemma x218_not_frac_chi_K2_zero : ~ x130_frac_chi_le 'K_2 0 1.
Proof.
case=> a [b] [f] [bpos [card _] le].
have a0 : a = 0 by move: le; rewrite muln1 mul0n leqn0 => /eqP.
have ba : b <= a.
  by move: (max_card (mem (f ord0))); rewrite card_ord (card ord0).
rewrite a0 leqn0 in ba.
by move: bpos; move/eqP: ba => ->.
Qed.

Print Assumptions every_forest_is_good_statement.
Print Assumptions path_induced_rooted_tree_polynomial_chi_bound_statement.
Print Assumptions polynomial_gyarfas_sumner_tree_statement.
Print Assumptions every_forest_is_multibounding_statement.
Print Assumptions odd_minor_free_defective_clustered_treedepth_statement.
Print Assumptions kr_free_degenerate_fractional_chromatic_sublinear_statement.
Print Assumptions x218_multibounding_pointwiseP.
Print Assumptions x218_multibounding_K1.
Print Assumptions x218_path_induced_copy_K1.
Print Assumptions x218_odd_minor_refl.
Print Assumptions x218_no_odd_minor_K2_in_K1.
Print Assumptions x218_frac_chi_K1.
Print Assumptions g218_ominf_hyp_inhabited.
Print Assumptions g218_ominf_not_trivially_true.
Print Assumptions g218_Kn_odd_tree.
Print Assumptions g218_K1_no_odd_tree_K2.
Print Assumptions g218_ctd_K2.
Print Assumptions g218_no_ctd_empty.
Print Assumptions g218_ominf_exact_not_trivially_true.
Print Assumptions g218_ctd_mono.
Print Assumptions g218_ctd_2K1.
Print Assumptions g218_td_2K1.

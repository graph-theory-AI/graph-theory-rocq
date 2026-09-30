(** * Chromatic.conjectures.grounding_X218 -- grounding lemmas for wave X218.

    Qed-closed, axiom-free sanity results for the primitives of [X218.v] and for
    the hypothesis blocks of its six statements: a SATISFIABLE witness for every
    guard and a GUARD-HAS-TEETH lemma for every notion that could collapse.
    They validate the statements; they do not prove them.  The [poly_chi_bounded]
    wrapper itself is grounded where it lives, in
    [chromatic-theory/theories/foundations/chi_bounding.v]. *)

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
by rewrite /edge_rel /= /x218_multipartite_rel (ord1 x.1) (ord1 y.1) eqxx.
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

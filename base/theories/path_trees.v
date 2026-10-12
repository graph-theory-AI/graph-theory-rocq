(** * GTBase.path_trees — graphs that are paths, as trees of maximum degree two

    Batch B of the library migration, family [path-tree]
    (meta/library_primitives/path-tree.json).  [path_tree T] holds when the whole
    graph [T] is a tree in the sense of coq-graph-theory ([is_tree [set: T]]:
    unique irredundant paths and connected) and every vertex has at most two
    neighbours ([Delta T <= 2]).  It is the index-graph condition of path
    decompositions and the "path" of tree inducibility.

    This module imports [GTBase.base], which owns [Delta], and is not re-exported
    by it: [base] already imports [walks_paths], so the predicate lives here, and
    its users import [GTBase.path_trees] explicitly.

    Upstream audit (2026-10-03; coq-graph-theory 0.9.7).  [sgraph.v] has
    [is_forest], [is_tree S := is_forest S /\ connected S], the [forest] record,
    [sunit], ['K_n] and ['K_n,m]; it has no path-graph or pathwidth predicate.
    Concrete path constructions on ordinals (Hom U3 [path_graph], Packing
    [x18_path_graph] / [x226_path_graph]) and the sequence and multigraph path
    contracts of [GTBase.walks_paths] / [Cycle.foundations.path_subgraphs] are
    different representations and stay separate.  Linear forests (forests of maximum
    degree two, not necessarily connected) are [linear_forest] at the end of this file.

    Specification, every clause proved below:
    - a path tree is a tree, hence a forest and connected, and every vertex has at
      most two neighbours; conversely a tree whose degrees are at most two is one;
    - the EMPTY graph ['K_0] is a path tree ([is_tree] of the empty vertex set holds
      vacuously), as are ['K_1] and the single edge ['K_2];
    - a cycle is excluded: the triangle ['K_3] is not a forest;
    - a branching vertex is excluded: the claw ['K_1,3] has a vertex of degree 3.
    No nonemptiness or size premise is added. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph.
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** [T] is a path: a tree whose vertices have at most two neighbours. *)
Definition path_tree (T : sgraph) : Prop := is_tree [set: T] /\ Delta T <= 2.

Section PathTree.
Variable T : sgraph.
Implicit Types (v : T).

Lemma path_tree_tree : path_tree T -> is_tree [set: T].
Proof. by case. Qed.

Lemma path_tree_forest : path_tree T -> is_forest [set: T].
Proof. by case=> -[]. Qed.

Lemma path_tree_connected : path_tree T -> connected [set: T].
Proof. by case=> -[]. Qed.

Lemma path_tree_Delta : path_tree T -> Delta T <= 2.
Proof. by case. Qed.

(** The degree form of the bound. *)
Lemma Delta_le2P : reflect (forall v, #|N(v)| <= 2) (Delta T <= 2).
Proof.
apply: (iffP idP) => [h v|h].
- exact: leq_trans (leq_bigmax v) h.
- by apply/bigmax_leqP => v _; apply: h.
Qed.

Lemma path_tree_degree v : path_tree T -> #|N(v)| <= 2.
Proof. by move/path_tree_Delta/Delta_le2P. Qed.

Lemma path_treeI : is_tree [set: T] -> (forall v, #|N(v)| <= 2) -> path_tree T.
Proof. by move=> tT dT; split=> //; apply/Delta_le2P. Qed.

(** Graphs on at most two vertices satisfy the degree bound. *)
Lemma Delta_le_card : Delta T <= #|T|.
Proof. by apply/bigmax_leqP => v _; apply: max_card. Qed.

End PathTree.

(** ** Grounding: empty, singleton, edge, cycle and branch *)

Lemma path_tree_K0 : path_tree 'K_0.
Proof.
split; last by apply: leq_trans (Delta_le_card _) _; rewrite card_ord.
by split; [move=> [] | move=> []].
Qed.

Lemma path_tree_K1 : path_tree 'K_1.
Proof.
split; last by apply: leq_trans (Delta_le_card _) _; rewrite card_ord.
split.
- move=> x y p q [ip _] [iq _].
  have xy : x = y by rewrite !ord1.
  move: p q ip iq; rewrite -xy => p q ip iq.
  by rewrite (irredxx ip) (irredxx iq).
- have -> : [set: 'K_1] = [set ord0] by apply/setP => z; rewrite !inE ord1.
  exact: connected1.
Qed.

Lemma path_tree_K2 : path_tree 'K_2.
Proof.
split; last by apply: leq_trans (Delta_le_card _) _; rewrite card_ord.
split.
- have key : forall (x y : 'K_2) (p q : Path x y), irred p -> irred q -> p = q.
    move=> x y; case: (eqVneq x y) => [<-|xy] p q ip iq.
      by rewrite (irredxx ip) (irredxx iq).
    have E2 : [set x; y] = [set: 'K_2].
      by apply/eqP; rewrite eqEcard subsetT /= cards2 xy cardsT card_ord.
    have sub (r : Path x y) : {subset r <= [set x; y]} by move=> z _; rewrite E2 inE.
    have [e1 ->] := irred_is_edge p ip xy (sub p).
    have [e2 ->] := irred_is_edge q iq xy (sub q).
    by rewrite (bool_irrelevance e2 e1).
  apply: forestI => -[x [y [p1 [p2 [[i1 i2 ne] _]]]]].
  by rewrite (key _ _ p1 p2 i1 i2) eqxx in ne.
- move=> x y _ _; case: (eqVneq x y) => [->|xy]; first exact: connect0.
  have xy' : x -- y := xy.
  by apply: connect1; rewrite /= !inE.
Qed.

(** A cycle: the triangle is not a forest. *)
Lemma not_path_tree_K3 : ~ path_tree 'K_3.
Proof.
move=> /path_tree_forest Hf; have card3 : 3 <= #|'K_3| by rewrite card_ord.
by have [x [y [xy nadj]]] := forest3 Hf card3; rewrite /edge_rel /= xy in nadj.
Qed.

(** A branch: the centre of the claw has three neighbours. *)
Lemma not_path_tree_claw : ~ path_tree 'K_1,3.
Proof.
move=> /(path_tree_degree (inl ord0 : 'K_1,3)) le2.
have sub : [set inr i | i in [set: 'I_3]] \subset N(inl ord0 : 'K_1,3).
  by apply/subsetP => _ /imsetP[i _ ->]; rewrite inE.
have deg3 : 2 < #|N(inl ord0 : 'K_1,3)|.
  apply: leq_trans (subset_leq_card sub).
  by rewrite card_imset ?cardsT ?card_ord //; exact: inr_inj.
by move: (leq_trans deg3 le2).
Qed.

(** ** Linear forests

    Library migration D14, family [linear-forest]
    (meta/library_primitives/linear-forest.json).  [linear_forest G] holds when the
    whole graph [G] is a forest ([is_forest [set: G]]: unique irredundant paths) and
    every vertex has at most two neighbours ([Delta G <= 2]), i.e. [G] is a disjoint
    union of paths.  It is the forest analogue of [path_tree] and stays distinct from
    it: a path tree is a CONNECTED linear forest ([path_treeP]).  No connectedness,
    nonemptiness or size premise is added.

    Specification, every clause proved below:
    - a linear forest is a forest whose vertices have at most two neighbours, and
      conversely (the degree form, through [Delta_le2P]);
    - [path_tree G <-> linear_forest G /\ connected [set: G]];
    - every edgeless graph is a linear forest, in particular the EMPTY graph
      ['K_0]; ['K_1] and the single edge ['K_2] are linear forests;
    - a cycle is excluded: the triangle ['K_3] is not a forest;
    - a branching vertex is excluded: the claw ['K_1,3] has a vertex of degree 3. *)
Definition linear_forest (G : sgraph) : Prop := is_forest [set: G] /\ Delta G <= 2.

Section LinearForest.
Variable G : sgraph.
Implicit Types (v : G).

Lemma linear_forest_forest : linear_forest G -> is_forest [set: G].
Proof. by case. Qed.

Lemma linear_forest_Delta : linear_forest G -> Delta G <= 2.
Proof. by case. Qed.

Lemma linear_forest_degree v : linear_forest G -> #|N(v)| <= 2.
Proof. by move/linear_forest_Delta/Delta_le2P. Qed.

Lemma linear_forestI : is_forest [set: G] -> (forall v, #|N(v)| <= 2) -> linear_forest G.
Proof. by move=> fG dG; split=> //; apply/Delta_le2P. Qed.

(** The degree equivalence. *)
Lemma linear_forestP :
  linear_forest G <-> is_forest [set: G] /\ (forall v, #|N(v)| <= 2).
Proof.
split=> [lG|[fG dG]]; last exact: linear_forestI.
by split=> [|v]; [exact: linear_forest_forest | exact: linear_forest_degree].
Qed.

(** A path tree is a linear forest; a linear forest is a path tree exactly when it
    is connected. *)
Lemma path_tree_linear_forest : path_tree G -> linear_forest G.
Proof. by move=> pG; split; [exact: path_tree_forest | exact: path_tree_Delta]. Qed.

Lemma path_treeP : path_tree G <-> linear_forest G /\ connected [set: G].
Proof.
split=> [pG|[[fG dG] cG]].
  by split; [exact: path_tree_linear_forest | exact: path_tree_connected].
by split=> //; split.
Qed.

(** An edgeless graph is a linear forest: every path is trivial and every
    neighbourhood is empty. *)
Lemma linear_forest_edgeless : (forall x y : G, ~~ (x -- y)) -> linear_forest G.
Proof.
move=> noE; split.
- move=> x y p q [ip _] [iq _].
  have xy : x = y.
    case/connectP: (Path_connect p) => -[_ -> //|z s] /= /andP[xz _].
    by case/negP: (noE x z).
  move: p q ip iq; rewrite -xy => p q ip iq.
  by rewrite (irredxx ip) (irredxx iq).
- apply/Delta_le2P => v; rewrite (_ : N(v) = set0) ?cards0 //.
  by apply/setP => w; rewrite !inE (negbTE (noE v w)).
Qed.

End LinearForest.

(** ** Linear-forest grounding: empty, singleton, edge, cycle and branch *)

Lemma linear_forest_K0 : linear_forest 'K_0.
Proof. exact: path_tree_linear_forest path_tree_K0. Qed.

Lemma linear_forest_K1 : linear_forest 'K_1.
Proof. exact: path_tree_linear_forest path_tree_K1. Qed.

Lemma linear_forest_K2 : linear_forest 'K_2.
Proof. exact: path_tree_linear_forest path_tree_K2. Qed.

(** A cycle: the triangle is not a forest. *)
Lemma not_linear_forest_K3 : ~ linear_forest 'K_3.
Proof.
move=> /linear_forest_forest Hf; have card3 : 3 <= #|'K_3| by rewrite card_ord.
by have [x [y [xy nadj]]] := forest3 Hf card3; rewrite /edge_rel /= xy in nadj.
Qed.

(** A branch: the centre of the claw has three neighbours. *)
Lemma not_linear_forest_claw : ~ linear_forest 'K_1,3.
Proof.
move=> /(linear_forest_degree (inl ord0 : 'K_1,3)) le2.
have sub : [set inr i | i in [set: 'I_3]] \subset N(inl ord0 : 'K_1,3).
  by apply/subsetP => _ /imsetP[i _ ->]; rewrite inE.
have deg3 : 2 < #|N(inl ord0 : 'K_1,3)|.
  apply: leq_trans (subset_leq_card sub).
  by rewrite card_imset ?cardsT ?card_ord //; exact: inr_inj.
by move: (leq_trans deg3 le2).
Qed.

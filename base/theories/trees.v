(** * GTBase.trees — whole simple-graph trees: support API over upstream [is_tree]

    Library migration B20, family [whole-tree] (meta/library_primitives/whole-tree.json).  The
    canonical predicate is coq-graph-theory's [is_tree S := is_forest S /\ connected S]
    ([GraphTheory.core.sgraph]), taken at the WHOLE carrier [[set: T]]: the migrated wrappers
    [Extremal.conjectures.XE1.xe1_tree] and [Packing.conjectures.XE1.xe1_tree] are definitionally
    [is_tree [set: T]], and this module adds no second tree predicate and no nonempty guard.  It
    provides the whole-carrier projections and introduction, the Boolean form over upstream
    [is_forestb] and [connectedb] with its reflection, and groundings: the empty graph ['K_0]
    (vacuously), ['K_1], the single edge ['K_2] (B9's path-tree proofs) and the claw ['K_1,3] (a tree
    that B9's [path_tree] excludes) are trees; the triangle ['K_3] (two irredundant paths between any
    two vertices) and two isolated vertices ([compl 'K_2], disconnected) are not.

    Distinct, untouched: B18's labelled spanning trees [fg_spanning_tree], B19's multigraph edge
    carriers, D2tur's ordered-pair trees, U9's terminal trees, the directed trees of X2 and P9, and
    B9's degree-bounded [path_tree].  This module imports [GTBase.base] and [GTBase.path_trees] and
    is not re-exported by [base]. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph.
From GTBase Require Import base path_trees.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section WholeTree.
Variable G : sgraph.
Implicit Types (S : {set G}).

(** The Boolean form of upstream [is_tree] on any vertex set. *)
Definition is_treeb S : bool := is_forestb S && connectedb S.

Lemma is_treeP S : reflect (is_tree S) (is_treeb S).
Proof.
apply: (iffP andP) => [[/is_forestP f /connectedP c] | [f c]]; first by split.
by split; [apply/is_forestP | apply/connectedP].
Qed.

(** The whole-carrier projections and introduction. *)
Lemma is_treeT_forest : is_tree [set: G] -> is_forest [set: G].
Proof. by case. Qed.

Lemma is_treeT_connected : is_tree [set: G] -> connected [set: G].
Proof. by case. Qed.

Lemma is_treeTI : is_forest [set: G] -> connected [set: G] -> is_tree [set: G].
Proof. by []. Qed.

Lemma is_treeT_connect : is_tree [set: G] -> forall x y : G, connect (--) x y.
Proof. by move=> /is_treeT_connected/connectedTE. Qed.

Lemma is_treeTI_connect :
  is_forest [set: G] -> (forall x y : G, connect (--) x y) -> is_tree [set: G].
Proof. by move=> f c; split=> //; exact: connectedTI. Qed.

(** Unique irredundant paths, the forest half spelled out. *)
Lemma is_treeT_unique : is_tree [set: G] -> forall x y : G, unique (fun p : Path x y => irred p).
Proof. by move=> /is_treeT_forest; exact: forestT_unique. Qed.

End WholeTree.

(** ** Groundings *)

(** The empty graph, one vertex and one edge are trees (B9's path-tree proofs). *)
Lemma is_tree_K0 : is_tree [set: 'K_0].
Proof. exact: path_tree_tree path_tree_K0. Qed.

Lemma is_tree_K1 : is_tree [set: 'K_1].
Proof. exact: path_tree_tree path_tree_K1. Qed.

Lemma is_tree_K2 : is_tree [set: 'K_2].
Proof. exact: path_tree_tree path_tree_K2. Qed.

(** The triangle is not a forest (two irredundant paths join any two of its vertices). *)
Lemma not_is_tree_K3 : ~ is_tree [set: 'K_3].
Proof.
move=> /is_treeT_forest Hf; have card3 : 3 <= #|'K_3| by rewrite card_ord.
by have [x [y [xy nadj]]] := forest3 Hf card3; rewrite /edge_rel /= xy in nadj.
Qed.

(** Two isolated vertices are a forest but not connected. *)
Lemma not_is_tree_two_isolated : ~ is_tree [set: compl 'K_2].
Proof.
move=> /is_treeT_connected conn.
have ne : (ord0 : compl 'K_2) != ord_max by [].
have [z _] := connected_card_gt1 conn (in_setT (ord0 : compl 'K_2)) (in_setT ord_max) ne.
by rewrite /edge_rel /= /compl_rel /= /edge_rel /= => /andP[zne]; rewrite zne.
Qed.

(** ** The claw ['K_1,3]: a tree with a vertex of degree three, excluded by B9's path trees.
    Its irredundant paths are unique: from the centre to a leaf the single edge, between two leaves
    the two edges through the centre, since a leaf's only neighbour is the centre. *)
Section Claw.
Local Notation K13 := ('K_1,3).
Let c : K13 := inl ord0.

Lemma claw_centre (o : 'I_1) : (inl o : K13) = c.
Proof. by rewrite /c (fintype.ord1 o). Qed.

Lemma claw_adj_cl (i : 'I_3) : c -- inr i.
Proof. by []. Qed.

Lemma claw_adj_lc (i : 'I_3) : (inr i : K13) -- c.
Proof. by []. Qed.

Lemma claw_adj_cc_false (o o' : 'I_1) : ((inl o : K13) -- inl o') = false.
Proof. by []. Qed.

Lemma claw_adj_ll_false (i j : 'I_3) : ((inr i : K13) -- inr j) = false.
Proof. by []. Qed.

Lemma claw_path_cl (i : 'I_3) (p : Path c (inr i)) : irred p -> p = edgep (claw_adj_cl i).
Proof.
move=> ip; have cl : c != inr i by [].
case: (splitL p cl) => [[o|j] [cz [p' [E _]]]]; first by have := cz; rewrite claw_adj_cc_false.
rewrite E irred_edgeL in ip; case/andP: ip => cNp' ip'.
case: (eqVneq j i) => [ji|ji].
- by subst j; rewrite E (irredxx ip') pcat_idR (bool_irrelevance cz (claw_adj_cl i)).
- have ne : (inr j : K13) != inr i by rewrite (inj_eq inr_inj).
  case: (splitL p' ne) => [[o|k] [jz2 [p'' [E' _]]]]; last by have := jz2; rewrite claw_adj_ll_false.
  have : (inl o : K13) \in p' by rewrite E' mem_pcat mem_edgep eqxx orbT.
  by rewrite claw_centre (negbTE cNp').
Qed.

Lemma claw_path_lc (i : 'I_3) (p : Path (inr i : K13) c) : irred p -> p = edgep (claw_adj_lc i).
Proof.
move=> ip; have lc : (inr i : K13) != c by [].
case: (splitL p lc) => [[o|k] [lz [p' [E _]]]]; last by have := lz; rewrite claw_adj_ll_false.
rewrite E irred_edgeL in ip; case/andP: ip => _ ip'.
move: E; move: ip'; move: p'; move: lz; rewrite (claw_centre o) => lz p' ip' E.
by rewrite E (irredxx ip') pcat_idR (bool_irrelevance lz (claw_adj_lc i)).
Qed.

Lemma claw_path_ll (i j : 'I_3) (p : Path (inr i : K13) (inr j)) :
  i != j -> irred p -> p = pcat (edgep (claw_adj_lc i)) (edgep (claw_adj_cl j)).
Proof.
move=> ij ip; have ne : (inr i : K13) != inr j by rewrite (inj_eq inr_inj).
case: (splitL p ne) => [[o|k] [lz [p' [E _]]]]; last by have := lz; rewrite claw_adj_ll_false.
rewrite E irred_edgeL in ip; case/andP: ip => _ ip'.
move: E; move: ip'; move: p'; move: lz; rewrite (claw_centre o) => lz p' ip' E.
by rewrite E (claw_path_cl ip') (bool_irrelevance lz (claw_adj_lc i)).
Qed.

Lemma claw_unique (x y : K13) (p q : Path x y) : irred p -> irred q -> p = q.
Proof.
move: p q; case: x => [o|i]; case: y => [o'|j] p q ip iq.
- move: ip; move: iq; move: p; move: q; rewrite (claw_centre o) (claw_centre o') => q p iq ip.
  by rewrite (irredxx ip) (irredxx iq).
- move: ip; move: iq; move: p; move: q; rewrite (claw_centre o) => q p iq ip.
  by rewrite (claw_path_cl ip) (claw_path_cl iq).
- move: ip; move: iq; move: p; move: q; rewrite (claw_centre o') => q p iq ip.
  by rewrite (claw_path_lc ip) (claw_path_lc iq).
- move: ip; move: iq; move: p; move: q; case: (eqVneq i j) => [<-|ij] q p iq ip.
  + by rewrite (irredxx ip) (irredxx iq).
  + by rewrite (claw_path_ll ij ip) (claw_path_ll ij iq).
Qed.

Lemma is_tree_claw : is_tree [set: 'K_1,3].
Proof.
split; last exact: (@Knm_connected 0 2).
by apply: unique_forestT => x y p q ip iq; exact: claw_unique ip iq.
Qed.

End Claw.

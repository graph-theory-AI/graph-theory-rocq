(** * GTBase.spanning_trees — labelled spanning trees of finite simple graphs

    Library migration B18, family [spanning-tree] (meta/library_primitives/spanning-tree.json).
    [fg_spanning_tree G T] holds when the labelled edge set [T] (2-subsets of the vertex carrier
    of [G], the encoding of [GTBase.finite_graph]) consists of edges of [G] ([T \subset fg_edges G])
    and the labelled graph [fg_labelled_sgraph T] on the WHOLE carrier of [G] is a tree in the sense
    of coq-graph-theory ([is_tree [set: _]]: unique irredundant paths and connected).  The subset
    guard is part of the contract: the labelled-graph constructor ignores invalid members (loops,
    non-edges, sets that are not pairs), so validity cannot be read off the graph.  Every vertex of
    [G] is a vertex of that graph, isolated ones included, so a graph with two or more vertices one
    of which is isolated has no spanning tree, and no disconnected graph has one.

    Conventions, DERIVED from upstream [is_tree] rather than added as guards:
      - the empty edge set is the spanning tree of the empty graph ['K_0] (vacuously) and of the
        single vertex ['K_1];
      - the single edge of ['K_2] is its spanning tree;
      - the full edge set of the triangle ['K_3] is not (two irredundant paths join any two of
        its vertices), two isolated vertices admit none, one edge of ['K_3] misses a vertex, and
        a set containing a singleton is never a spanning tree (edge validity).
    No nonempty guard, edge-count characterisation or validity repair is introduced.

    Upstream audit (2026-10-03; coq-graph-theory 0.9.7): [sgraph.v] has [is_forest], [is_tree],
    [is_forestb], [connectedb], [forestI], [forest3], [connected_card_gt1] and the complete graphs
    ['K_n], but no spanning-tree predicate; [GTBase.finite_graph] has [fg_edges],
    [fg_labelled_sgraph] and the bridge [fg_edgesE : fg_edges G = E(G)].  The multigraph spanning
    tree of [Cycle.conjectures.U6] (an edge carrier that is spanning-connected and acyclic), the
    whole-graph tree wrappers of XE1 (definitionally [is_tree]), [D2tur.tree_on] and the directed
    trees of P9/X2 are different representations and stay separate.

    This module imports [GTBase.finite_graph] and is not re-exported by [GTBase.base]; its users
    import [GTBase.spanning_trees] explicitly. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph.
From GTBase Require Import finite_graph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SpanningTree.
Variable G : sgraph.
Implicit Types (T : {set {set G}}).

(** [T] is a set of edges of [G] whose labelled graph, on the whole carrier of [G], is a tree. *)
Definition fg_spanning_tree T : Prop :=
  T \subset fg_edges G /\ is_tree [set: fg_labelled_sgraph T].

(** The Boolean form over the finite carrier (upstream [is_forestb] and [connectedb]). *)
Definition fg_spanning_treeb T : bool :=
  (T \subset fg_edges G) && is_forestb [set: fg_labelled_sgraph T]
  && connectedb [set: fg_labelled_sgraph T].

Lemma fg_spanning_treeP T : reflect (fg_spanning_tree T) (fg_spanning_treeb T).
Proof.
apply: (iffP andP) => [[/andP[sub /is_forestP forest] /connectedP conn] | [sub [forest conn]]].
- by split=> //; split.
- by split; [apply/andP; split => //; apply/is_forestP | apply/connectedP].
Qed.

Lemma fg_spanning_treeI T :
  T \subset fg_edges G -> is_tree [set: fg_labelled_sgraph T] -> fg_spanning_tree T.
Proof. by []. Qed.

Lemma fg_spanning_tree_sub T : fg_spanning_tree T -> T \subset fg_edges G.
Proof. by case. Qed.

Lemma fg_spanning_tree_tree T : fg_spanning_tree T -> is_tree [set: fg_labelled_sgraph T].
Proof. by case. Qed.

Lemma fg_spanning_tree_forest T : fg_spanning_tree T -> is_forest [set: fg_labelled_sgraph T].
Proof. by case=> _ []. Qed.

Lemma fg_spanning_tree_connected T : fg_spanning_tree T -> connected [set: fg_labelled_sgraph T].
Proof. by case=> _ []. Qed.

(** The upstream edge-set form of the validity guard ([fg_edgesE]). *)
Lemma fg_spanning_treeE T :
  fg_spanning_tree T <-> T \subset E(G) /\ is_tree [set: fg_labelled_sgraph T].
Proof. by rewrite /fg_spanning_tree fg_edgesE. Qed.

(** Members of [fg_edges G] are pairs of adjacent vertices. *)
Lemma fg_edges_edge (x y : G) : [set x; y] \in fg_edges G -> x -- y.
Proof.
rewrite inE => /existsP[x' /existsP[y' /andP[/andP[_ xy'] /eqP /doubleton_eq_iff]]].
by case=> -[-> ->]; [exact: xy' | rewrite sg_sym].
Qed.

(** Edge validity: every member of a spanning tree is a pair ... *)
Lemma fg_spanning_tree_valid T : fg_spanning_tree T -> fg_valid_edge_set T.
Proof.
case=> /subsetP sub _; apply/forallP => e; apply/implyP => /sub.
by rewrite inE => /existsP[x /existsP[y /andP[/andP[xy _] /eqP ->]]]; rewrite cards2 xy.
Qed.

(** ... of adjacent vertices of [G]. *)
Lemma fg_spanning_tree_edge T (x y : G) : fg_spanning_tree T -> [set x; y] \in T -> x -- y.
Proof. by case=> /subsetP sub _ /sub/fg_edges_edge. Qed.

(** Whole carrier: with at least two vertices, every vertex, isolated in [G] or not, must carry
    an edge of the tree. *)
Lemma fg_spanning_tree_cover T (x : G) :
  fg_spanning_tree T -> 1 < #|G| -> exists y : G, [set x; y] \in T.
Proof.
case=> _ [_ conn] /card_gt1P[a [b [_ _ ab]]].
have [y xy] : exists y : G, x != y.
  by case: (eqVneq a x) => [ax|ax]; [exists b; rewrite -ax | exists a; rewrite eq_sym].
have [z _ /andP[_ /orP[h|h]]] := connected_card_gt1 conn (in_setT x) (in_setT y) xy.
- by exists z.
- by exists z; rewrite setUC.
Qed.

(** A spanning tree connects the whole host graph. *)
Lemma fg_spanning_tree_connectedG T : fg_spanning_tree T -> connected [set: G].
Proof.
move=> sT; apply: connectedTI => x y.
move: (connectedTE (fg_spanning_tree_connected sT) x y).
apply: connect_sub => a b /andP[_ /orP[h|h]]; apply: connect1.
- exact: fg_spanning_tree_edge sT h.
- by rewrite sg_sym; exact: fg_spanning_tree_edge sT h.
Qed.

End SpanningTree.

(** ** Groundings: the conventions derived from upstream [is_tree] *)

(** In a complete graph every pair of distinct vertices is an edge. *)
Lemma fg_edges_Kn (n : nat) (x y : 'K_n) : x != y -> [set x; y] \in fg_edges 'K_n.
Proof.
move=> xy; rewrite inE; apply/existsP; exists x; apply/existsP; exists y.
by apply/andP; split; [apply/andP; split => //; exact: xy | exact: eqxx].
Qed.

(** The empty graph: the empty edge set is its spanning tree, vacuously. *)
Lemma fg_spanning_tree_K0 : fg_spanning_tree (@set0 {set 'K_0}).
Proof. by split; [exact: sub0set | split; [move=> [] | move=> []]]. Qed.

(** One vertex: the empty edge set is its spanning tree. *)
Lemma fg_spanning_tree_K1 : fg_spanning_tree (@set0 {set 'K_1}).
Proof.
split; first exact: sub0set.
split.
- move=> x y p q [ip _] [iq _].
  have xy : x = y by rewrite !fintype.ord1.
  move: p q ip iq; rewrite -xy => p q ip iq.
  by rewrite (irredxx ip) (irredxx iq).
- have -> : [set: fg_labelled_sgraph (@set0 {set 'K_1})] = [set (ord0 : 'K_1)].
    by apply/setP => z; rewrite !inE fintype.ord1 eqxx.
  exact: connected1.
Qed.

(** Two vertices: the single edge is the spanning tree of ['K_2]. *)
Lemma fg_spanning_tree_K2 : fg_spanning_tree (fg_edges 'K_2).
Proof.
split; first exact: subxx.
pose H2 := fg_labelled_sgraph (fg_edges 'K_2).
have adj : forall x y : H2, x != y -> x -- y.
  by move=> x y xy; rewrite /edge_rel/= /fg_srel /fg_edge_set_rel xy (fg_edges_Kn xy).
split.
- have key : forall (x y : H2) (p q : Path x y), irred p -> irred q -> p = q.
    move=> x y; case: (eqVneq x y) => [<-|xy] p q ip iq.
      by rewrite (irredxx ip) (irredxx iq).
    have E2 : [set x; y] = [set: H2].
      by apply/eqP; rewrite eqEcard subsetT /= cards2 xy cardsT card_ord.
    have sub (r : Path x y) : {subset r <= [set x; y]} by move=> z _; rewrite E2 inE.
    have [e1 ->] := irred_is_edge p ip xy (sub p).
    have [e2 ->] := irred_is_edge q iq xy (sub q).
    by rewrite (bool_irrelevance e2 e1).
  apply: forestI => -[x [y [p1 [p2 [[i1 i2 ne] _]]]]].
  by rewrite (key _ _ p1 p2 i1 i2) eqxx in ne.
- move=> x y _ _; case: (eqVneq x y) => [->|xy]; first exact: connect0.
  have xy' : x -- y := adj _ _ xy.
  by apply: connect1; rewrite /= !inE.
Qed.

(** The triangle: its full edge set is not a tree (two irredundant paths join any two vertices). *)
Lemma not_fg_spanning_tree_K3 : ~ fg_spanning_tree (fg_edges 'K_3).
Proof.
case=> _ [forest _].
have card3 : 3 <= #|fg_labelled_sgraph (fg_edges 'K_3)| by rewrite card_ord.
have [x [y [xy nadj]]] := forest3 forest card3.
by move: nadj; rewrite /edge_rel/= /fg_srel /fg_edge_set_rel xy (fg_edges_Kn xy).
Qed.

(** One edge of the triangle misses its third vertex (whole carrier). *)
Definition k3_o1 : 'K_3 := Ordinal (n := 3) (m := 1) isT.
Definition k3_o2 : 'K_3 := Ordinal (n := 3) (m := 2) isT.

Lemma not_fg_spanning_tree_K3_edge : ~ fg_spanning_tree [set [set (ord0 : 'K_3); k3_o1]].
Proof.
move=> sT; have card3 : 1 < #|'K_3| by rewrite card_ord.
have [y /set1P/doubleton_eq_iff] := fg_spanning_tree_cover k3_o2 sT card3.
by case=> -[/(congr1 val)].
Qed.

(** Two isolated vertices: no edge set is a spanning tree (the graph is disconnected). *)
Definition two_isolated : sgraph := fg_labelled_sgraph (@set0 {set 'I_2}).

Lemma not_fg_spanning_tree_two_isolated (T : {set {set two_isolated}}) : ~ fg_spanning_tree T.
Proof.
move=> sT; have card2 : 1 < #|two_isolated| by rewrite card_ord.
have [y h] := fg_spanning_tree_cover (ord0 : two_isolated) sT card2.
by have := fg_spanning_tree_edge sT h; rewrite /edge_rel/= /fg_srel /fg_edge_set_rel !in_set0 orbF andbF.
Qed.

(** Edge validity: a set containing a singleton is never a spanning tree. *)
Lemma not_fg_spanning_tree_singleton (G : sgraph) (x : G) (T : {set {set G}}) :
  [set x] \in T -> ~ fg_spanning_tree T.
Proof.
move=> xT [/subsetP sub _]; have := sub _ xT.
rewrite inE => /existsP[a /existsP[b /andP[/andP[ab _] /eqP e]]].
by have := congr1 (fun S : {set G} => #|S|) e; rewrite cards1 cards2 ab.
Qed.

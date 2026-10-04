(** * Whole-graph view of the upstream matching

    [matching_graph G] says that the WHOLE edge set E(G) of the finite simple graph G is
    an upstream [GraphTheory.connectivity.matching]: its members are edges of G (here
    trivially) and two edges sharing a vertex are equal.  This is a specialization of the
    upstream primitive to E(G), not a second matching definition.

    Equivalently, every vertex has at most one neighbour ([matching_graph_degP]), and such
    a graph is a forest, so [matching_graph G] is also exactly "a forest of maximum degree
    at most one" ([matching_graph_forestP]).  Isolated vertices, the empty graph and K1 are
    allowed; nothing asks for connectedness, perfectness, a nonempty graph or a positive
    degree.  It is a predicate on the entire graph, not on a selected edge family.
    Import explicitly; [GTBase.base] does not re-export this module. *)
From GTBase Require Import base.
From GraphTheory Require Import preliminaries.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition matching_graph (G : sgraph) : Prop := @matching G E(G).

Section MatchingGraph.
Variable G : sgraph.
Implicit Types (x y z : G) (e : {set G}).

Lemma matching_graphE : matching_graph G <-> @matching G E(G).
Proof. exact: iff_refl. Qed.

(** Every edge through x is [x; a] for a neighbour a of x. *)
Lemma edge_at_vertex e x : e \in E(G) -> x \in e -> exists2 a : G, x -- a & e = [set x; a].
Proof.
case/edgesP=> u [v [-> uv]]; rewrite !inE => /orP[] /eqP ->.
- by exists v.
- by exists u; rewrite 1?sg_sym // setUC.
Qed.

Lemma matching_graph_uniq_nb x y z : matching_graph G -> x -- y -> x -- z -> y = z.
Proof.
move=> [_ M] xy xz.
have e1 : [set x; y] \in E(G) by rewrite in_edges.
have e2 : [set x; z] \in E(G) by rewrite in_edges.
by have := M _ _ e1 e2 x; rewrite !inE !eqxx /= => /(_ isT isT) /doubleton_eq_left.
Qed.

Lemma matching_graph_deg x : matching_graph G -> #|N(x)| <= 1.
Proof.
move=> M; apply/card_le1_eqP => y z; rewrite !in_opn => xy xz.
exact: (@matching_graph_uniq_nb x z y M xz xy).
Qed.

Lemma deg_matching_graph : (forall x : G, #|N(x)| <= 1) -> matching_graph G.
Proof.
move=> deg; split=> // e1 e2 E1 E2 x xe1 xe2.
have [a xa ->] := edge_at_vertex E1 xe1.
have [b xb ->] := edge_at_vertex E2 xe2.
have -> // : a = b.
by apply: (card_le1_eqP (deg x)); rewrite in_opn.
Qed.

Lemma matching_graph_degP : matching_graph G <-> (forall x : G, #|N(x)| <= 1).
Proof.
split=> [M x|]; [exact: matching_graph_deg | exact: deg_matching_graph].
Qed.

(** In a graph of maximum degree at most one an irredundant path between distinct
    vertices is a single edge: after its first edge x -- z, the only neighbour of z is x,
    already used, so the path stops at z = y. *)
Lemma deg_le1_irred (deg : forall x : G, #|N(x)| <= 1) (x y : G) (p : Path x y) :
  x != y -> irred p -> exists e : x -- y, p = edgep e.
Proof.
move=> xy Ip.
case: (splitL p xy) => z [xz] [p'] [defp _].
move: Ip; rewrite defp irred_edgeL => /andP[xNp' Ip'].
have [zy|zNy] := eqVneq z y.
  by subst z; exists xz; rewrite (irredxx Ip') pcat_idR.
exfalso.
case: (splitL p' zNy) => w [zw] [p''] [defp' _].
move: (xz); rewrite sg_sym => zx.
have xw : x = w by apply: (card_le1_eqP (deg z)); rewrite in_opn.
move/negP: xNp'; apply.
by rewrite defp' mem_pcat mem_edgep xw eqxx !orbT.
Qed.

Lemma deg_le1_forest : (forall x : G, #|N(x)| <= 1) -> is_forest [set: G].
Proof.
move=> deg; apply: unique_forestT => x y p q Ip Iq.
have [xy|xy] := eqVneq x y.
  by subst y; rewrite (irredxx Ip) (irredxx Iq).
have [e ->] := deg_le1_irred deg xy Ip.
have [e' ->] := deg_le1_irred deg xy Iq.
by rewrite (bool_irrelevance e e').
Qed.

Lemma matching_graph_forest : matching_graph G -> is_forest [set: G].
Proof. by move/matching_graph_degP; exact: deg_le1_forest. Qed.

Lemma matching_graph_forestP :
  matching_graph G <-> is_forest [set: G] /\ (forall x : G, #|N(x)| <= 1).
Proof.
split=> [M|[_ deg]]; last exact: deg_matching_graph.
by split; [exact: matching_graph_forest | exact/matching_graph_degP].
Qed.

End MatchingGraph.

(** * GTBase.triangles -- triangle vertex sets and raw two-element subsets

    [triangle_set T] (Boolean, cardinality first) and [triangle T] (Prop, clique first) say that the supplied vertex
    set [T] has exactly three vertices and is a clique; [triangleP] reflects one into the other and
    [triangle_card_firstE] gives the cardinality-first Prop order.  [raw_pairs T] is the set of ALL two-element
    subsets of [T], defined on every vertex set: a nonadjacent pair still contributes one raw pair, so raw pairs are
    graph edges only under an explicit clique guard ([raw_pairs_cliqueE]).  No clique predicate is added: these are
    thin names over upstream [clique]/[cliqueb] and MathComp finite sets.  The graph-level absence of triangles is
    A15's [triangle_free]; a triangle-set predicate is not a whole-graph property.
    Registry: meta/library_primitives/triangle-set.json (A19). *)
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Triangles.
Variable G : sgraph.
Implicit Types T e : {set G}.

(** Three-vertex cliques, Boolean (cardinality first). *)
Definition triangle_set T : bool := (#|T| == 3) && cliqueb T.

(** Three-vertex cliques, Prop (clique first). *)
Definition triangle T : Prop := clique T /\ #|T| = 3.

(** All two-element subsets of [T], adjacent or not. *)
Definition raw_pairs T : {set {set G}} := [set e : {set G} | (e \subset T) && (#|e| == 2)].

Lemma triangleP T : reflect (triangle T) (triangle_set T).
Proof.
apply: (iffP andP) => [[/eqP T3 /cliqueP cT]|[cT T3]]; first by split.
by split; [apply/eqP | apply/cliqueP].
Qed.

(** The cardinality-first Prop order. *)
Lemma triangle_card_firstE T : triangle T <-> #|T| = 3 /\ clique T.
Proof. exact: and_comm. Qed.

Lemma in_raw_pairs T e : (e \in raw_pairs T) = (e \subset T) && (#|e| == 2).
Proof. by rewrite inE. Qed.

Lemma card_raw_pairs T : #|raw_pairs T| = 'C(#|T|, 2).
Proof. exact: cards_draws. Qed.

Lemma raw_pairs_small T : #|T| <= 1 -> raw_pairs T = set0.
Proof. by move=> T1; apply/eqP; rewrite -cards_eq0 card_raw_pairs; case: #|T| T1 => [|[|]]. Qed.

(** Raw pairs are graph edges exactly under a clique guard. *)
Lemma raw_pairs_cliqueE T : clique T -> raw_pairs T = [set e in E(G) | e \subset T].
Proof.
move=> cT; apply/setP => e; rewrite !inE sg_edge_set_cliqueE !inE.
case eT: (e \subset T); rewrite ?andbF ?andbT //=.
suff -> : cliqueb e by rewrite andbT.
by apply/cliqueP; exact: sub_clique eT cT.
Qed.

(** A triangle has three raw pairs, and three distinct, pairwise adjacent vertices. *)
Lemma triangle_raw_pairs T : triangle T -> #|raw_pairs T| = 3.
Proof. by case=> _ T3; rewrite card_raw_pairs T3. Qed.

Lemma triangle_vertices T : triangle T ->
  exists x y z : G, [/\ T = [set x; y; z], x -- y, y -- z & x -- z].
Proof.
case=> cT T3; have : 2 < #|T| by rewrite T3.
case/card_gt2P => x [y [z [[xT yT zT] [xy yz zx]]]].
have sub : [set x; y; z] \subset T.
  by apply/subsetP => w; rewrite !inE => /orP[/orP[]|] /eqP ->.
exists x, y, z; split; [|by apply: cT|by apply: cT|by apply: cT; rewrite // eq_sym].
apply/esym/eqP; rewrite eqEcard sub T3 /=; apply/card_gt2P.
by exists x, y, z; rewrite !inE !eqxx /= ?orbT; split.
Qed.

End Triangles.

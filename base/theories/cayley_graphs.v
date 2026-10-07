(** * GTBase.cayley_graphs -- the undirected Cayley graph of a finite group and an arbitrary connection set

    [undirected_cayley_graph S], for a finite group [gT] and ANY [S : {set gT}], has the group elements as vertices,
    [x] and [y] adjacent iff [x != y] and [x^-1 * y \in S] or [y^-1 * x \in S].  The disjunction symmetrises the
    adjacency and [x != y] suppresses loops (also when [1 \in S]), so it is a simple graph for every [S]: no inverse
    closure, generation, abelianity or order condition is imposed, and nonabelian groups are allowed.  When [S] is
    closed under inverses the two disjuncts coincide and this is the usual Cayley graph
    ([undirected_cayley_edge_inv]).  It is not the directed Digraph.constructions.cayley.cayley (arcs
    [x^-1 * y \in A], loops kept, no symmetrisation).
    API: the adjacency view and #|gT| vertices, edges along right multiplication by [S] and by its inverses, the
    inverse-closed specialisation, and the empty, identity and full connection sets (edgeless, edgeless, complete).
    Registry: meta/library_primitives/cayley-graph.json (A26). *)
From mathcomp Require Import all_boot fingroup.
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section UndirectedCayleyGraph.
Variables (gT : finGroupType) (S : {set gT}).

(** Distinct elements whose quotient, in either order, lies in [S]. *)
Definition undirected_cayley_rel : rel gT :=
  fun x y => (x != y) && (((x^-1 * y)%g \in S) || ((y^-1 * x)%g \in S)).

Lemma undirected_cayley_sym : symmetric undirected_cayley_rel.
Proof. by move=> x y; rewrite /undirected_cayley_rel eq_sym orbC. Qed.

Lemma undirected_cayley_irrefl : irreflexive undirected_cayley_rel.
Proof. by move=> x; rewrite /undirected_cayley_rel eqxx. Qed.

Definition undirected_cayley_graph : sgraph := SGraph undirected_cayley_sym undirected_cayley_irrefl.

Lemma undirected_cayley_edgeE (x y : gT) :
  @edge_rel undirected_cayley_graph x y = (x != y) && (((x^-1 * y)%g \in S) || ((y^-1 * x)%g \in S)).
Proof. by []. Qed.

Lemma card_undirected_cayley_graph : #|undirected_cayley_graph| = #|gT|.
Proof. by []. Qed.

(** Right multiplication by a non-identity element of [S], or by its inverse, is an edge: the inverse need not lie in
    [S]. *)
Lemma undirected_cayley_edge_mul (x s : gT) :
  s \in S -> s != 1%g -> @edge_rel undirected_cayley_graph x (x * s)%g && @edge_rel undirected_cayley_graph x (x * s^-1)%g.
Proof.
move=> sS s1.
have ne (t : gT) : t != 1%g -> x != (x * t)%g.
  by move=> t1; apply: contra t1 => /eqP xt; rewrite -(mulKg x t) -xt mulVg.
rewrite !undirected_cayley_edgeE !mulKg !invMg invgK !mulgKV sS orTb orbT !andbT.
by rewrite !ne // eq_invg1.
Qed.

(** When [S] is closed under inverses the two disjuncts coincide. *)
Lemma undirected_cayley_edge_inv (x y : gT) :
  (forall z : gT, (z \in S) = ((z^-1)%g \in S)) ->
  @edge_rel undirected_cayley_graph x y = (x != y) && ((x^-1 * y)%g \in S).
Proof. by move=> invS; rewrite undirected_cayley_edgeE [(y^-1 * x)%g \in S]invS invMg invgK orbb. Qed.

End UndirectedCayleyGraph.

(** ** The empty, identity and full connection sets *)

Section ConnectionSets.
Variable gT : finGroupType.

Lemma undirected_cayley_set0 (x y : gT) : @undirected_cayley_rel gT set0 x y = false.
Proof. by rewrite /undirected_cayley_rel !in_set0 orbF andbF. Qed.

Lemma undirected_cayley_set1 (x y : gT) : @undirected_cayley_rel gT [set 1%g] x y = false.
Proof. by rewrite /undirected_cayley_rel !in_set1 -!eq_mulVg1 [y == x]eq_sym orbb andNb. Qed.

Lemma undirected_cayley_setT (x y : gT) : @undirected_cayley_rel gT setT x y = (x != y).
Proof. by rewrite /undirected_cayley_rel !in_setT orbT andbT. Qed.

(** With every element as connection set the graph is complete. *)
Lemma undirected_cayley_setT_diso : undirected_cayley_graph [set: gT] ≃ 'K_#|gT|.
Proof. by apply: diso_Kn => x y xy; rewrite undirected_cayley_edgeE !in_setT orbT andbT. Qed.

End ConnectionSets.

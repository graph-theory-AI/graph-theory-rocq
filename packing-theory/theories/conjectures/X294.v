(** * Packing.conjectures.X294 -- v2 row: Gruslys' conjecture on perfect induced H-packings of Cartesian powers of
      vertex-transitive graphs *)

From GTBase Require Import base common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X294 vocabulary *****************************************************)

(** Local copies of hamiltonicity-theory's graph-symmetry pair (U2.v l.76-80, also copied in X211), bodies verbatim:
    packing-theory does not import Hamilton.  An automorphism is an adjacency-preserving and -reflecting bijection;
    G is vertex-transitive iff its automorphisms act transitively on the vertices. *)
Definition x294_graph_automorphism (G : sgraph) (f : G -> G) : Prop :=
  bijective f /\ forall u v : G, (f u -- f v) = (u -- v).

Definition x294_vertex_transitive (G : sgraph) : Prop :=
  forall x y : G, exists f : G -> G, x294_graph_automorphism f /\ f x = y.

(** The t-th Cartesian (box) power of G: homomorphism-theory's x227_box_power (X227.v l.42-43), body verbatim, since
    packing-theory does not import Hom.  The empty power is the one-vertex graph 'K_1, the unit of
    [cartesian_product], so [x294_box_power G 1] is [cartesian_product 'K_1 G], a copy of G. *)
Fixpoint x294_box_power (G : sgraph) (t : nat) : sgraph :=
  if t is t'.+1 then cartesian_product (x294_box_power G t') G else 'K_1.

(** ** X294 statement ******************************************************)

(** Corpus row: studies:std_gruslys_conjecture_perfect_induced_h_packings_of
    Site: none
    Review: none
    English statement: (Gruslys; studies slice of the corpus, record arXiv:1710.07255)
      Let G be a finite vertex-transitive graph and let H be an induced subgraph of G.  If |V(H)| divides |V(G)|,
      then there exists a positive integer n such that G^n admits a perfect induced H-packing.
    Definitions: [x294_vertex_transitive G] - for any two vertices x, y some automorphism maps x to y (this file;
      U2's vertex_transitive); [x294_graph_automorphism f] - f is a bijection with f u -- f v = u -- v (this file;
      U2's graph_automorphism); [x294_box_power G n] - G^n, the n-th Cartesian power (this file; X227's
      x227_box_power, over GTBase's [cartesian_product]); [induced S] and [≃] - coq-graph-theory's induced
      subgraph on a vertex set S and graph isomorphism (a bijection that preserves and reflects adjacency);
      [partition P D] - MathComp's: the blocks of P are pairwise disjoint, nonempty, and cover D.
    Notes: encoded as stated.  "H is an induced subgraph of G" is that some vertex set S of G induces a graph
      isomorphic to H, written positively (as X268 writes induced copies), not as GTBase's [~ induced_free G H],
      which is its double negation.  A perfect induced H-packing of G^n (Bonamy, Morrison and Scott,
      arXiv:1710.07255v3, torus-final.tex l.80: vertex-disjoint copies of H covering every vertex, each copy an
      induced subgraph) is a partition of the vertices of G^n into sets that each induce a copy of H; G^n is the
      n-th Cartesian power (l.85-86).  The positive integer n is the guard 0 < n.  Degenerate instances: if H has
      no vertex, |V(H)| = 0 divides |V(G)| only when G has no vertex; then G^n, n >= 1, has no vertex and the
      empty partition packs it.  The conjecture is l.104-106 of the same paper, word for word.  Pinned status
      open, but FALSE at the pin: Theorem th:unpackabletori (l.115-119; v3 of 14 June 2020) gives, for every odd k
      that is not a prime power, some m >= 1 and an induced subgraph H of C_k^m with |V(H)| dividing k^m such that
      no C_k^n has a perfect H-packing; C_k^m is vertex-transitive.  The status correction is a separate corpus
      item. *)
Definition gruslys_perfect_induced_packing_statement : Prop :=
  forall (G : sgraph) (H : sgraph),
    x294_vertex_transitive G ->
    (exists S : {set G}, inhabited (induced S ≃ H)) ->
    (#|H| %| #|G|)%N ->
    exists n : nat, (0 < n)%N /\
      exists P : {set {set x294_box_power G n}},
        partition P [set: x294_box_power G n] /\
        forall S, S \in P -> inhabited (induced S ≃ H).

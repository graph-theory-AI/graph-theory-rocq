(** * Chromatic.conjectures.X68 -- v2 distant precolouring extension row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X68 vocabulary ************************************************)

Definition x68_proper_three_colouring (G : sgraph) (col : G -> 'I_3) : Prop :=
  forall x y : G, x -- y -> col x != col y.

Definition x68_pairwise_distance_at_least
    (G : sgraph) (d : nat) (S : {set G}) : Prop :=
  forall x y : G,
    x \in S -> y \in S -> x != y -> y \notin ball d.-1 x.

(** ** X68 statements ******************************************************)

(** Corpus row: arxiv:0911.0885#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/0911.0885__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/0911.0885__00.json
    English statement: (Dvorak, Kral and Thomas 2020, Conjecture 1.4, arXiv:0911.0885)
      There is an absolute constant d >= 2 such that for every planar triangle-free finite simple
      graph G, every vertex set S whose elements are pairwise at distance at least d, and every
      assignment of one of three colours to each vertex of S, there is a proper 3-colouring of G
      agreeing with that assignment on S.
    Definitions: [x68_pairwise_distance_at_least G d S] - no two distinct vertices of S lie within
      distance d-1 of each other, expressed with base's [ball] (this file);
      [x68_proper_three_colouring] (this file); [wagner_planar], [triangle_free], [ball] (GTBase
      base/theories/base.v).
    Notes: The precolouring is given as a total function psi on the vertices, only its restriction
      to S being constrained, which is equivalent to a partial precolouring of S. Planarity is the
      combinatorial Wagner predicate, so the source's "plane graph", i.e. a graph with a fixed
      embedding, is weakened to "planar graph"; this is harmless because the conclusion does not
      refer to the embedding. *)
Definition triangle_free_planar_distant_precolouring_extension_statement : Prop :=
  exists d : nat,
    2 <= d /\
    forall (G : sgraph) (S : {set G}) (psi : G -> 'I_3),
      wagner_planar G ->
      triangle_free G ->
      x68_pairwise_distance_at_least d S ->
      exists col : G -> 'I_3,
        x68_proper_three_colouring col /\
        forall v : G, v \in S -> col v = psi v.

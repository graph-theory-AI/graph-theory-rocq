(** * GTMisc.conjectures.X299 -- v2 row: Reed and Seymour's chordal partition question (record arXiv:1707.04964) *)

From GTBase Require Import base chordal.
From GraphTheory Require Import minor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X299 statement ******************************************************)

(** Reused vocabulary: coq-graph-theory's [minor_rmap] (a model of a minor by branch sets: non-empty, connected,
    pairwise disjoint vertex sets with an edge between the images of adjacent vertices) and [neighbor], GTBase.chordal
    [chordal_by_cycles] (the chordal family's canonical), GTBase base [bipartite], and [induced].  The partition and
    its quotient are written out in the statement.  X299 declares no helper of its own. *)

(** Corpus row: studies:std_reed_seymour_chordal_partition_question
    Site: none
    Review: none
    English statement: (Reed and Seymour; studies slice of the corpus, record arXiv:1707.04964)
      Does every graph have a chordal partition such that each part is bipartite?
    Definitions: [minor_rmap phi] - the sets [phi h] (h a vertex of H) are non-empty, induce connected subgraphs,
      are pairwise disjoint, and [phi x], [phi y] are joined by an edge whenever x -- y in H (coq-graph-theory);
      [neighbor A B] - some vertex of A is adjacent to some vertex of B; [chordal_by_cycles H] - every chordless
      genuine cycle of H has at most three vertices, that is H has no induced cycle of length at least four
      (GTBase.chordal); [bipartite G] - some 2-colouring of V(G) gives the ends of every edge distinct colours
      (GTBase base); [induced S] - the subgraph induced on the vertex set S.
    Notes: encoded as the question's affirmative answer, with Scott, Seymour and Wood's definitions
      (arXiv:1707.04964v2, BadNews.tex l.98): a partition is a set of non-empty induced subgraphs with each vertex
      in exactly one part; the quotient has the parts as vertices, distinct parts adjacent iff some vertex of one is
      adjacent to some vertex of the other; a partition is chordal if every part is connected and the quotient is
      chordal ("contains no induced cycle of length at least four").  Here the parts are the branch sets [phi h] of
      a [minor_rmap] (non-empty, connected, pairwise disjoint) that cover V(G), and the supplied graph H is the
      quotient: [minor_rmap]'s edge clause gives one direction of the adjacency and the third clause the
      other, so H is isomorphic to the quotient.  "Each part is bipartite": the subgraph induced
      on [phi h].  Degenerate instances: the graph with no vertex has the empty partition (an H with no vertex).
      The question (Question 1 there, l.100-103) is Reed and Seymour's (1998); a positive answer would make every
      graph with no K_(t+1) minor 2t-colourable (l.105).  Pinned status open, but answered NO at the pin in its own
      record: Theorem NoChordal (l.107-112) gives, for every k >= 1, a graph G such that every chordal partition of
      G has a part containing K_k (as an induced subgraph, the convention of l.96); at k = 3 that part has a
      triangle, so it is not bipartite.  The construction is recursive (Lemma ChordalWork); no kernel disproof.
      The status correction is a separate corpus item. *)
Definition reed_seymour_chordal_partition_statement : Prop :=
  forall G : sgraph,
    exists (H : sgraph) (phi : H -> {set G}),
      [/\ minor_rmap phi,
          forall v : G, exists h : H, v \in phi h,
          forall x y : H, x != y -> neighbor (phi x) (phi y) -> x -- y,
          chordal_by_cycles H &
          forall h : H, bipartite (induced (phi h))].

(** * Chromatic.conjectures.X32 -- v2 planar induced degeneracy row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X32 statements ******************************************************)

(** Corpus row: arxiv:1709.04036#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1709.04036__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1709.04036__00.json
    English statement: (Dvorak and Kelly 2018, Conjecture 1.1, arXiv:1709.04036)
      Every triangle-free planar finite simple graph has a vertex set S with 8*|S| >= 7*|V(G)|, i.e.
      at least seven eighths of its vertices, whose induced subgraph is 2-degenerate.
    Definitions: [k_degenerate H 2] - every nonempty vertex subset of H contains a vertex with at
      most 2 neighbours inside it (GTBase base/theories/base.v); [triangle_free], [wagner_planar]
      (base.v); [induced S] (coq-graph-theory sgraph.v).
    Notes: The fraction 7/8 is cross-multiplied to avoid nat division. The conjecture is tight for
      the cube, the unique 3-regular triangle-free planar graph on 8 vertices. Corpus status: open,
      with the weaker bound 4/5 proved in the source paper. *)
Definition triangle_free_planar_large_induced_two_degenerate_statement : Prop :=
  forall G : sgraph,
    wagner_planar G ->
    triangle_free G ->
    exists S : {set G},
      (8 * #|S| >= 7 * #|G|)%N /\
      k_degenerate (induced S) 2.

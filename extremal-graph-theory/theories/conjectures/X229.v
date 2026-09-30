(** * Extremal.conjectures.X229 -- new corpus row arxiv:2309.04460#01 (wave X229, 2026-09-23) *)

From GTBase Require Export base.
From Extremal.foundations Require Import edge_colourings.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x229 vocabulary ***********************************************

    The paper-local notion of arXiv:2309.04460 (Alon, Bucic, Sauermann,
    Zakharov, Zamir, "Essentially tight bounds for rainbow cycles in proper
    edge-colourings"), Definition 3.1, fetched from the source at authoring time
    (the 2026-09-23 triage did not recover it):

      "A graph G on n >= 1 vertices is called a robust sublinear expander if for
       every 0 <= eps <= 1 and every non-empty subset U of V(G) of size
       |U| <= n^{1-eps} the following holds.  For every subset F of E(G) of
       |F| <= (eps/3) * d(G) * |U| edges, we have |N_{G-F}(U)| >= (eps/3) * |U|."

    Here d(G) = 2|E(G)|/n is the average degree and, by the paper's Notation
    paragraph, the neighbourhood N(U) of a vertex set U is the set of vertices
    OUTSIDE U having a neighbour in U.  The paper notes that no one-vertex graph
    is a robust sublinear expander (take eps = 1 and U = V(G)); [grounding_X229.v]
    reproduces that observation. *)

(** The EXTERNAL neighbourhood of [U]: vertices outside [U] adjacent to it. *)
Definition x229_ext_neigh (G : sgraph) (U : {set G}) : {set G} := NS(U) :\: U.

(** Definition 3.1, with the real parameter eps = a/b in [0,1] and every
    division cleared:
      |U| <= n^{1-eps}            becomes  |U|^b <= n^(b-a),
      |F| <= (eps/3) * d(G) * |U| becomes  3*b*(n*|F|) <= 2*a*(|E(G)|*|U|),
      |N_{G-F}(U)| >= (eps/3)*|U| becomes  a*|U| <= 3*b*|N_{G-F}(U)|. *)
Definition x229_robust_sublinear_expander (G : sgraph) : Prop :=
  forall (a b : nat) (U : {set G}) (F : {set {set G}}),
    0 < b -> a <= b ->
    0 < #|U| ->
    #|U| ^ b <= #|G| ^ (b - a) ->
    F \subset E(G) ->
    3 * b * (#|G| * #|F|) <= 2 * a * (#|E(G)| * #|U|) ->
    a * #|U| <= 3 * b * #|@x229_ext_neigh (del_edge_set G F) U|.

(** Corpus row: arxiv:2309.04460#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2309.04460__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2309.04460__01.json
    English statement: (Alon, Bucic, Sauermann, Zakharov, Zamir 2023,
      arXiv:2309.04460 Question 10.2)
      There is a positive constant C such that for every finite graph G on n vertices that
      is a robust sublinear expander and whose average degree is at least C * log n, and
      every proper colouring of the edges of G by a palette Col, the palette can be split
      into two parts P and its complement so that both spanning subgraphs of G carrying,
      respectively, the P-coloured edges and the remaining edges are connected.  Equivalently:
      the edges of G decompose into two spanning connected subgraphs in such a way that every
      colour appears on only one of them.
    Definitions: [x229_robust_sublinear_expander G] - Definition 3.1 of the source, with
      eps = a/b rational and all divisions cleared (this file); [x229_ext_neigh G U] - the
      external neighbourhood NS(U) \ U (this file); [proper_ecolouring col] - adjacent edges
      get distinct colours (Extremal.foundations.edge_colourings);
      [colour_class col P] - the spanning subgraph of G keeping exactly the edges whose colour
      satisfies P (Extremal.foundations.edge_colourings); [del_edge_set G F] (GTBase.common);
      [NS(_)], [E(_)], [connected] - coq-graph-theory.
    Notes: three modelling choices.  (1) The colour palette is an arbitrary finite type Col
      and the split is a predicate P on it; [colour_class col P] and
      [colour_class col (predC P)] are automatically SPANNING (same vertex set) and their
      edge sets partition E(G), which is exactly "every colour appears on only one of them".
      (2) "average degree at least C * log n" is rendered as
      "for every L with 2^L <= n, C * (n * L) <= 2 * |E(G)|", i.e. d(G) >= C * floor(log2 n);
      since C is EXISTENTIALLY quantified and changing the base of the logarithm only
      rescales C by a constant, this is equivalent to the source's natural logarithm form.
      (3) The subset F of deleted edges is required to satisfy F \subset E(G) as in the
      source; dropping that requirement would give an equivalent statement, since a set with
      non-edges deletes the same edges while having a larger cardinality.
      SECOND-READER READBACK (2026-09-23): Definition 3.1 was re-fetched from the source and
      matches the quotation above word for word; the Notation paragraph confirms both that
      N(U) is the EXTERNAL neighbourhood ("the set of vertices in V(G) \ U that are adjacent
      to a vertex in U") and that d(G) denotes the AVERAGE degree, so d(G) = 2|E(G)|/n is the
      right reading of the |F| guard.  Restricting eps to the rationals a/b loses nothing:
      for fixed U and F the admissible eps form an interval whose lower endpoint 3|F|/(d|U|)
      is rational and whose conclusion |N| >= (eps/3)|U| is a closed inequality between
      integers, so the rational instances already force the real supremum.  Question 10.2
      itself could NOT be re-fetched (Section 10 is truncated in every HTML rendering of the
      paper reachable from here); it was checked only against the corpus review quotation. *)
Definition expander_proper_colouring_two_connected_palettes_statement : Prop :=
  exists C : nat,
    0 < C /\
    forall (G : sgraph) (Col : finType) (col : {set G} -> Col),
      x229_robust_sublinear_expander G ->
      proper_ecolouring col ->
      (forall L : nat, 2 ^ L <= #|G| -> C * (#|G| * L) <= 2 * #|E(G)|) ->
      exists P : pred Col,
        connected [set: colour_class col P] /\
        connected [set: colour_class col (predC P)].

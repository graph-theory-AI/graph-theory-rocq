(** * Extremal.conjectures.X309 -- v2 row: the Fraughnaugh-Locke conjecture (a triangle-free subcubic graph with none
      of six graphs as a subgraph has independence number at least 3n/8) *)

From GTBase Require Import base common.
From Extremal.conjectures Require Import X287.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X309 statement ********************************************************* *)

(** Corpus row: studies:std_fraughnaugh_locke_conjectures_independence_in_tr
    Site: none
    Review: none
    English statement: (Fraughnaugh and Locke's conjecture; studies slice of the corpus, record arXiv:1911.12471)
      If G is a triangle-free subcubic n-vertex graph containing none of F_11, F_14^(1), F_14^(2), F_19^(1), F_19^(2),
      F_22 as a subgraph, then alpha(G) >= 3/8 n.
    Definitions: [x287_bb_graph i] (X287.v) - the six graphs F_11, F_14^(1), F_14^(2), F_19^(1), F_19^(2), F_22 of
      the source's Figure 1, from wave X287; [has_subgraph G H] - G contains H as a (not necessarily
      induced) subgraph: an injective map from H to G sending edges to edges (GTBase common.v, host first);
      [triangle_free G] - no three pairwise adjacent vertices; [subcubic G] - every vertex has at most three
      neighbours (GTBase base.v); α([set: G]) - the independence number of G (coq-graph-theory).
    Notes: encoded as stated.  "n-vertex" is #|G|, and alpha(G) >= 3n/8 is 3 * #|G| <= 8 * α([set: G]), with no
      division.  "Containing none of ... as a subgraph" is ordinary (not induced) containment, as l.226 says ("as a
      subgraph"); has_subgraph asks for an injective edge-preserving map, so it does not depend on how the six
      graphs' vertices are labelled.  Source: Cames van Batenburg,
      Goedgebeur and Joret, "Large independent sets in triangle-free cubic graphs: beyond planarity",
      arXiv:1911.12471v2 (8 July 2020, the last version before the pin), Revision_IndependenceRatio8over3.tex l.158
      (finite simple graphs), l.161 (subcubic = maximum degree at most 3), l.225-227 (Conjecture 5, Fraughnaugh and
      Locke, as the row states it) and l.183-191 (Figure 1, the six graphs, X287's tables).  The forbidden-subgraph
      hypothesis is needed: without it the statement fails at F_11 ([g309_not_trivially_true] in grounding_X309.v).
      l.229-230: the conjecture implies Bajnok and Brinkmann's (X287's first clause).  Status: solved in its own
      record (Theorem 7, l.243-247; v2 of 8 July 2020, before the pin); the pinned status is open; a literature item
      after integration records it.  Theorem 7 is the paper's main theorem, Conjecture 5 verbatim (statement read,
      proof not verified). *)
Definition fraughnaugh_locke_forbidden_subgraph_independence_statement : Prop :=
  forall G : sgraph, triangle_free G -> subcubic G ->
    (forall i : 'I_6, ~ has_subgraph G (x287_bb_graph i)) ->
    3 * #|G| <= 8 * α([set: G]).

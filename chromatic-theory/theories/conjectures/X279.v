(** * Chromatic.conjectures.X279 -- wave X279: Question 6.1 of "List-avoiding orientations", the spanning
    Alon-Tarsi orientation with out-degree at least (deg(v) - 1) / 2 (2026-11-02)

    A one-row wave under the prospective contract of meta/faithfulness_policy.json: the rebind of
    arxiv:2209.09107#00 (CORPUS_FEEDBACK item 50), whose statement and kernel disproof lived only in
    applications/alon_tarsi_triangle.v.  Shared vocabulary: Chromatic.foundations.alon_tarsi ([at_alon_tarsi],
    [at_outdegree]) and coq-graph-theory's open neighbourhood N(v).  No local helper.
    Pinned status open; this repository records it `disproved` (Marc's decision of 2026-10-31, an ERRATA entry of
    meta/build_v2_manifest.py): the triangle refutes the question as printed.  The source is the Mac's deposit
    coordination/sources/x268-source-mac-20261030 (2209.09107v2, main.tex line numbers below).  The grounding
    certificates and the disproof of the formal resolution (record 2209.09107__00) are in grounding_X279.v. *)

From GTBase Require Import base.
From Chromatic.foundations Require Import alon_tarsi.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X279 statement ********************************************************** *)

(** Corpus row: arxiv:2209.09107#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2209.09107__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2209.09107__00.json
    English statement: (Bradshaw, Chen, Ma, Mohar and Wu, List-avoiding orientations, arXiv:2209.09107, Question 6.1)
      Every finite simple graph G has a spanning subgraph with an Alon-Tarsi orientation in which every vertex v has
      out-degree at least (deg_G(v) - 1) / 2.
    Definitions: [at_alon_tarsi A] - the even and odd Eulerian sub-arc-sets of A (the empty one included) differ in
      number (Chromatic.foundations.alon_tarsi); [at_outdegree A v] - the number of arcs of A leaving v (same file);
      N(v) - the open neighbourhood of v in G (coq-graph-theory).
    Notes: encoded as printed in arXiv:2209.09107v2 (main.tex l.1004-1009), with no floor: the arc set A is an
      orientation of a spanning subgraph (every arc an edge of G, no edge used in both directions, every vertex
      kept, edges of G may stay unused), the Alon-Tarsi orientation is the paper's EE(D) != EO(D) (l.215-222), and
      out-degree at least (deg_G(v) - 1) / 2 is written over the naturals as deg_G(v) <= 2 out(v) + 1, with the
      degree taken in G.  The graphs are finite and simple, as in the source, and the refuting triangle is simple.
      The body is kernel-equivalent to applications/alon_tarsi_triangle.v's [question_6_1_statement]
      ([g279_statement_iff] in grounding_X279.v), the encoding reviewed with the formal resolution on 2026-09-05.
      Status: disproved, recorded through ERRATA (Marc's decision of 2026-10-31): on the triangle every vertex needs
      out-degree at least 1, which forces the cyclic orientation of all three edges, whose even and odd Eulerian
      sub-arc-sets are equal in number (the empty one and the whole cycle).  Kernel-checked:
      grounding_X279.v's [alon_tarsi_spanning_orientation_half_degree_disproved], the theorem of the formal
      resolution 2209.09107__00 (meta/formal_resolutions.json), through applications/alon_tarsi_triangle.v's
      [question_6_1_disproved].  The paper (l.1011) also asks the variant with -C for a constant C, which is not
      encoded here. *)
Definition alon_tarsi_spanning_orientation_half_degree_statement : Prop :=
  forall G : sgraph, exists A : {set G * G},
    [/\ forall x y : G, (x, y) \in A -> x -- y /\ (y, x) \notin A,
        at_alon_tarsi A &
        forall v : G, #|N(v)| <= (2 * at_outdegree A v).+1].

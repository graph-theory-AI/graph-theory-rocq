(** * GTMisc.conjectures.X295 -- v2 row: the Strong Normal Graph Conjecture of De Simone and Korner *)

From GTBase Require Import base.
From GTMisc.conjectures Require Import X29.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X295 statement ******************************************************)

(** Reused vocabulary: X29's normal graphs and induced cycles (GTMisc conjectures/X29.v, the companion Normal Graph
    Conjecture of the same record) and coq-graph-theory's complement [compl] (the complement family's canonical,
    the term X29's x29_complement unfolds to).  X295 declares no helper of its own. *)

(** Corpus row: studies:std_strong_normal_graph_conjecture_de_simone_k_rner
    Site: none
    Review: none
    English statement: (De Simone and Korner; studies slice of the corpus, record arXiv:1508.05487)
      A graph G is strongly normal if and only if neither G nor its complement contain a C_5 or a C_7 as an
      induced subgraph.
    Definitions: [x29_normal_graph G] - there are a list of cliques covering every vertex and a list of stable sets
      covering every vertex such that every chosen clique meets every chosen stable set (GTMisc conjectures/X29.v);
      [x29_has_induced_cycle G n] - some n-element vertex set induces a subgraph isomorphic to the n-cycle
      [cycle_graph n] (same file); [compl G] - the complement graph (coq-graph-theory); [induced T] - the subgraph
      induced on the vertex set T.
    Notes: encoded as stated.  "Strongly normal" is written out: every induced subgraph is normal (1508.05487v8
      source.tex l.182-183).  The four clauses are the source's ("neither G nor its complement contain a C_5 or a
      C_7"); the complement's C_5 clause is implied by G's, since C_5 is self-complementary, and it is kept as
      written.  Degenerate instances: the graph with no vertex satisfies both sides (empty covers; no induced
      cycle).  The "if" direction implies the companion row X29 (no_c5_c7_complement_c7_normal_graph_statement): no
      induced C_5, C_7 or complement of C_7 gives the four clauses, and a strongly normal graph is normal (T = all
      vertices).  The conjecture is Conjecture 1.2 of Harutyunyan, Pastor and Thomasse (arXiv:1508.05487v8,
      l.188-191), attributed to De Simone and Korner.  Pinned status open, but FALSE at the pin: their Theorem 1.3
      (l.198-200) gives a graph of girth at least 8 that is not normal, hence not strongly normal, while it has no
      induced C_5 or C_7 and its complement has none either (the complement of C_5 is C_5, and the complement of C_7
      has triangles); the construction is probabilistic.  The status correction is a separate corpus item. *)
Definition strong_normal_graph_statement : Prop :=
  forall G : sgraph,
    (forall T : {set G}, x29_normal_graph (induced T)) <->
    [/\ ~ x29_has_induced_cycle G 5, ~ x29_has_induced_cycle G 7,
        ~ x29_has_induced_cycle (compl G) 5 & ~ x29_has_induced_cycle (compl G) 7].

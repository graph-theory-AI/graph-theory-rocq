(** * Chromatic.conjectures.X238 -- wave X238: the two tau_d questions of Scott and Seymour (2026-10-27)

    A two-row wave under the prospective contract of meta/faithfulness_policy.json (hard lint,
    classified local helpers, grounding certificates, an independent verifier).  Rows:
    arxiv:2202.05557#01 (paths) and arxiv:2202.05557#02 (hereditary classes), the two referee
    questions after Theorem 1.6 of Scott and Seymour, "Polynomial bounds for chromatic number. V.
    Excluding a tree of radius two and a complete multipartite graph"; the sibling row #00 is X65.
    Shared vocabulary is reused: [has_subgraph] and [induced_free] (GTBase.common),
    [complete_multipartite_graph] (GTBase.complete_multipartite_graphs), [ordinal_path]
    (GTBase.path_graphs), [hereditary_class] (GTBase.graph_classes), [horner_nat] (GTBase.poly_nat)
    and the library chromatic number.  The one local helper is tau_d as an attained maximum.  The
    grounding certificates are in grounding_X238.v. *)

From GTBase Require Export base.
From GTBase Require Import common graph_classes complete_multipartite_graphs path_graphs poly_nat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x238 vocabulary ************************************************* *)

(** tau_d(G) = t: G contains the complete d-partite graph K_d(t), with d parts of t vertices, as a
    (not necessarily induced) subgraph, and no K_d(s) with s > t (arXiv:2202.05557 l.113-114).  For
    d >= 1 exactly one t satisfies it (K_d(0) is empty, and K_d(s) has d s vertices); for d = 0 none
    does, since K_0(s) is empty for every s. *)
Definition x238_tau (G : sgraph) (d t : nat) : Prop :=
  has_subgraph G (complete_multipartite_graph d t) /\
  forall s : nat, has_subgraph G (complete_multipartite_graph d s) -> s <= t.

(** ** X238 statements ******************************************************* *)

(** Corpus row: arxiv:2202.05557#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2202.05557__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2202.05557__01.json
    English statement: (arXiv:2202.05557, Scott and Seymour, "Polynomial bounds for chromatic number.
      V. Excluding a tree of radius two and a complete multipartite graph", the first referee
      question after Theorem 1.6, affirmative form)
      If H is a path, then for every integer d >= 1 there is a polynomial f such that
      chi(G) <= f(tau_d(G)) for every H-free graph G, where tau_d(G) is the largest t such that G
      has a (not necessarily induced) subgraph isomorphic to the complete d-partite graph with each
      part of cardinality t.
    Definitions: [x238_tau G d t] - tau_d(G) = t (this file); [induced_free G H] - no induced
      subgraph of G is isomorphic to H (GTBase.common); [ordinal_path k] - the path P_k on k
      vertices (GTBase.path_graphs); [horner_nat p x] - the polynomial with natural coefficient list
      p at x (GTBase.poly_nat).
    Notes: the source is the e-print main.tex of 2202.05557v2 (the pinned version): H-free l.78,
      tau_d l.113-114, Theorem 1.6 (mainthm, trees of radius two) l.130-134, the question
      l.138-140.  Every path is some P_k; k = 0 and k = 1 are vacuous or degenerate (no graph is
      P_0-free, and P_1-free graphs are empty).  The polynomial p is chosen before G.  A polynomial
      with real coefficients is dominated on N by one with natural coefficients, so natural
      coefficient lists lose nothing for an upper bound.  This is "every path is multibounding" in
      the tau_d form: G never contains K_d(tau_d(G) + 1), and a G with no K_d(t) has
      tau_d(G) <= t - 1, so the K_d(t)-free form of Chromatic X218 ([x218_multibounding]) and this
      form differ by a polynomial shift; X218's row arxiv:2303.11766#00 (every forest is
      multibounding) therefore implies this row.  Literature status: SOLVED since the pin, by
      Nguyen, Scott and Seymour, "Polynomial bounds for chromatic number VIII. Excluding a path and
      a complete multipartite graph" (arXiv:2303.11766v1, J. Graph Theory 2024), Theorem 1.5
      (paththm, x/main.tex l.124-127): for every path H and all d >= 1 a polynomial f bounds
      chi(G) by f(t) for every H-free G with no K_d(t) subgraph, for all t >= 1.  The row is
      encoded as stated; no formal resolution is recorded. *)
Definition path_free_polynomial_tau_bound_statement : Prop :=
  forall k d : nat, 1 <= d ->
    exists p : seq nat, forall (G : sgraph) (t : nat),
      induced_free G (ordinal_path k) -> x238_tau G d t -> χ([set: G]) <= horner_nat p t.

(** Corpus row: arxiv:2202.05557#02
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2202.05557__02/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2202.05557__02.json
    English statement: (arXiv:2202.05557, Scott and Seymour, the second referee question after
      Theorem 1.6, an analogue of Esperet's (false) conjecture for tau_d, affirmative form of the
      main question)
      Let C be a hereditary class of graphs and d >= 1.  If some function f has
      chi(G) <= f(tau_d(G)) for every G in C, then f can be chosen to be a polynomial.  (The row
      also asks: what if d = 2?)
    Definitions: [hereditary_class C] - C is closed under isomorphism and induced subgraphs
      (GTBase.graph_classes); [x238_tau G d t] - tau_d(G) = t (this file); [horner_nat p x] - the
      polynomial with natural coefficient list p at x (GTBase.poly_nat).
    Notes: the source is the e-print main.tex of 2202.05557v2: hereditary l.87-88, tau_d
      l.113-114, Esperet's conjecture and its refutation l.96, the question l.141-143.  The
      hypothesis function f : nat -> nat is arbitrary (a real f is replaced by its ceiling).  For
      d = 1 the row holds trivially, since tau_1(G) = |G| >= chi(G).  The row asks a main question
      and a fallback; the main one is encoded in its affirmative form, and the fallback "What if
      d = 2?" is its d = 2 instance, implied by it (the convention for Question rows, as for
      arxiv:1612.08698#00 in X183).  Literature status: open at the paper and the pinned review;
      Esperet's omega-version was refuted by Brianski, Davies and Walczak (l.96). *)
Definition tau_bounded_hereditary_polynomial_statement : Prop :=
  forall (C : sgraph -> Prop) (d : nat), hereditary_class C -> 1 <= d ->
    (exists f : nat -> nat, forall (G : sgraph) (t : nat), C G -> x238_tau G d t -> χ([set: G]) <= f t) ->
    exists p : seq nat, forall (G : sgraph) (t : nat),
      C G -> x238_tau G d t -> χ([set: G]) <= horner_nat p t.

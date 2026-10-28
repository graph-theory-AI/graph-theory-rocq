(** * Chromatic.conjectures.X249 -- v2 duplicate polynomial Gyarfas-Sumner row *)

From Chromatic.conjectures Require Import X218.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Corpus row: arxiv:2202.09118#02
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2202.09118__02/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2202.09118__02.json
    English statement: (Chudnovsky, Scott, Seymour and Spirkl 2022, informal conjecture "polynomial Gyarfas-Sumner", arXiv:2202.09118)
      It might be true that every forest H is good, i.e. the class of H-free graphs is
      polynomially chi-bounded. The Rocq body is literally the X218 statement for the same
      wording in arXiv:2202.10412, reused as a synonym so that this duplicate corpus row cannot
      drift from it: for every finite simple graph H that is a forest there are naturals c and d
      such that every graph with no induced subgraph isomorphic to H has chromatic number at most
      c times the d-th power of its clique number.
    Definitions: [every_forest_is_good_statement] - the X218 encoding (X218.v), over
      [poly_chi_bounded F] (naturals c and d, chosen before the graphs of the class, with
      chi(G) <= c * omega(G)^d for every G in the class; Chromatic.foundations chi_bounding.v),
      [has_induced H G] (some vertex set of G induces a copy of H; U8.v) and
      [is_forest [set: H]] (coq-graph-theory sgraph.v via GTBase).
    Notes: "H is good" is the source's name for "the class of H-free graphs is polynomially
      chi-bounded"; X218's Notes explain why the normal form c * t^d loses nothing over the
      naturals. The corpus relation e006 (same_conjecture, confirmed) identifies this row with
      arxiv:2202.05557#00 (X65.v, forest_free_polynomial_chi_bound_statement), and the verified
      equiv edge forest_free_polynomial_chi_bound_equiv_every_forest_is_good (implications_X218.v)
      proves the X65 and X218 encodings equivalent, with the same forest hypothesis on both sides.
      Corpus status: partial (pinned review: open for general H; partial results include
      arXiv:2202.10412, H good implies H + P4 good, and arXiv:2407.16882, graphs of bounded
      boxicity). *)
Definition every_forest_is_good_duplicate_statement : Prop :=
  every_forest_is_good_statement.

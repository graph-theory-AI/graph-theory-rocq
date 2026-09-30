(** * Chromatic.conjectures.X65 -- v2 polynomial Gyarfas-Sumner row *)

From GTBase Require Export base.
From Chromatic.conjectures Require Import U8 X3.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X65 statements ******************************************************)

(** Corpus row: arxiv:2202.05557#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2202.05557__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2202.05557__00.json
    English statement: (Scott and Seymour 2023, Conjecture 1.3, arXiv:2202.05557)
      For every finite simple graph H that is a forest, the class of graphs with no induced subgraph
      isomorphic to H is polynomially chi-bounded: some polynomial with natural coefficients p
      satisfies chi(G) <= p(omega(G)) for every H-free graph G.
    Definitions: [x3_polynomially_chi_bounded F] - some coefficient list p bounds chi by its
      Horner evaluation at omega over the class (X3.v); [has_induced H G] - some vertex set of G
      induces a copy of H (U8.v); [is_forest] (coq-graph-theory sgraph.v via GTBase).
    Notes: Polynomials are coefficient lists with NATURAL coefficients, which is no restriction
      for an upper bound of this shape. This row differs from X3's
      [polynomial_gyarfas_sumner_statement], which states the same kind of bound in the form chi <=
      omega^c; the present one allows an arbitrary polynomial, hence is formally weaker. Corpus
      status: partial, proved for several tree families and for H = P5. *)
Definition forest_free_polynomial_chi_bound_statement : Prop :=
  forall H : sgraph,
    is_forest [set: H] ->
    x3_polynomially_chi_bounded (fun G : sgraph => ~ has_induced H G).

(** * Extremal.conjectures.X59 -- v2 C4-free dense subgraph row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X59 vocabulary ************************************************)

Fixpoint x59_poly_eval (p : seq nat) (x : nat) : nat :=
  if p is a :: q then a + x * x59_poly_eval q x else 0.

Definition x59_subgraph_of (H G : sgraph) : Prop :=
  exists f : H -> G,
    injective f /\
    forall x y : H, x -- y -> f x -- f y.

Definition x59_has_cycle_length (G : sgraph) (n : nat) : Prop :=
  exists c : seq G, ucycle (--) c /\ size c = n.

(** Corpus row: arxiv:2307.08361#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2307.08361__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2307.08361__01.json
    English statement: (Du, Girao, Hunter, McCarty, Scott 2023, arXiv:2307.08361, polynomial bound in k for C_4-free subgraphs)
      There is a polynomial p with natural coefficients such that for every k and every graph G
      of average degree at least p(k), some subgraph of G contains no 4-cycle and has average
      degree at least k.
    Definitions: [x59_poly_eval p x] - Horner evaluation of the coefficient list p at x (X59.v);
      [x59_subgraph_of H G] - an injective adjacency-preserving map H -> G (X59.v);
      [x59_has_cycle_length G n] - some uniform cycle of G has exactly n vertices, so its
      negation is C_4-freeness at n = 4 (X59.v); [average_degree_geq G d 1] - the average degree
      is at least d (GTBase).
    Notes: the polynomial is represented by its coefficient list, so only polynomials with
      non-negative integer coefficients are available; this is enough for a threshold bound.
      C_4-freeness is the absence of a cycle of length 4 as a subgraph, not as an induced
      subgraph, matching the source. *)
Definition c4_free_subgraph_polynomial_average_degree_statement : Prop :=
  exists p : seq nat,
    forall (k : nat) (G : sgraph),
      average_degree_geq G (x59_poly_eval p k) 1 ->
      exists H : sgraph,
        x59_subgraph_of H G /\
        ~ x59_has_cycle_length H 4 /\
        average_degree_geq H k 1.

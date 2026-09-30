(** * Chromatic.conjectures.X206 -- v2 list-chromatic Delta/c row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X206 vocabulary ***********************************************)

(** [omega(G) <= Delta(G)^(1/q)] without real exponents, equivalently
    [omega(G)^q <= Delta(G)] for positive integer [q]. *)
Definition x206_subpower_clique_bound (G : sgraph) (q : nat) : Prop :=
  (ω([set: G])) ^ q <= Delta G.

(** ** X206 statements *****************************************************)

(** Corpus row: arxiv:1803.01051#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1803.01051__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1803.01051__00.json
    English statement: (Bonamy, Kelly, Nelson and Postle 2018, Question 1.5, arXiv:1803.01051)
      There is a function f of two naturals such that for every rational a/b > 1, given by naturals
      with 0 < b < a, the value f(a,b) is positive and every finite simple graph G whose clique
      number raised to the power f(a,b) is at most Delta(G) has choice number m satisfying a * m <=
      b * Delta(G), i.e. ch(G) <= Delta(G) / (a/b).
    Definitions: [x206_subpower_clique_bound G q] - omega(G)^q <= Delta(G), the integer-exponent
      form of omega(G) <= Delta(G)^(1/q) (this file); [is_choice_number G m] (GTBase
      base/theories/base.v); [Delta] (base.v).
    Notes: The real parameter c > 1 of the source is represented by a rational a/b > 1, and the
      real-valued function f by a function on the numerator and denominator; this is faithful
      because increasing f(c) only strengthens the clique-size hypothesis. The conclusion is cross-
      multiplied to avoid division. Corpus status: solved affirmatively by the source paper's own
      Theorem 1.1. *)
Definition list_chromatic_delta_over_c_subpower_clique_statement : Prop :=
  exists f : nat -> nat -> nat,
    forall a b : nat,
      0 < b ->
      b < a ->
      0 < f a b /\
      forall (G : sgraph) (m : nat),
        is_choice_number G m ->
        x206_subpower_clique_bound G (f a b) ->
        a * m <= b * Delta G.

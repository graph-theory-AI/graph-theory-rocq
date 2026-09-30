(** * Chromatic.conjectures.X187 -- v2 planar request-graph colouring row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X187 vocabulary ***********************************************)

Definition x187_triangle_free (G : sgraph) : Prop := girth_geq G 4.

Definition x187_proper_3_colouring (G : sgraph) (col : G -> 'I_3) : Prop :=
  forall x y : G, x -- y -> col x != col y.

Definition x187_request_pair (G : sgraph) (r x y : G) : bool :=
  (x != y) && (N(r) == [set x; y]).

Definition x187_request_graph
    (G : sgraph) (ReqEq ReqNeq : {set G}) (w : G -> nat) : Prop :=
  [disjoint ReqEq & ReqNeq] /\
  forall r : G,
    r \in ReqEq :|: ReqNeq -> #|N(r)| = 2 /\ 0 < w r.

Definition x187_eq_request_satisfied
    (G : sgraph) (col : G -> 'I_3) (r : G) : bool :=
  [exists x : G, [exists y : G,
      x187_request_pair r x y && (col x == col y)]].

Definition x187_neq_request_satisfied
    (G : sgraph) (col : G -> 'I_3) (r : G) : bool :=
  [exists x : G, [exists y : G,
      x187_request_pair r x y && (col x != col y)]].

Definition x187_total_request_weight
    (G : sgraph) (ReqEq ReqNeq : {set G}) (w : G -> nat) : nat :=
  \sum_(r in ReqEq) w r + \sum_(r in ReqNeq) w r.

Definition x187_satisfied_request_weight
    (G : sgraph) (ReqEq ReqNeq : {set G}) (w : G -> nat)
    (col : G -> 'I_3) : nat :=
  \sum_(r in ReqEq | x187_eq_request_satisfied col r) w r +
  \sum_(r in ReqNeq | x187_neq_request_satisfied col r) w r.

Definition x187_satisfies_fraction
    (G : sgraph) (ReqEq ReqNeq : {set G}) (w : G -> nat)
    (p q : nat) (col : G -> 'I_3) : Prop :=
  p * x187_total_request_weight ReqEq ReqNeq w <=
  q * x187_satisfied_request_weight ReqEq ReqNeq w col.

(** ** X187 statements *****************************************************)

(** Corpus row: arxiv:1702.00588#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1702.00588__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1702.00588__00.json
    English statement: (Dvorak and Sereni 2017, Problem 1, arXiv:1702.00588)
      There is a positive rational p/q with p <= q such that every planar triangle-free request
      graph has a proper 3-colouring satisfying at least the fraction p/q of the total request
      weight, where a request graph carries two disjoint sets of degree-two request vertices with
      positive weights, an equality request being satisfied when the two neighbours get the same
      colour and an inequality request when they get different colours.
    Definitions: [x187_request_graph ReqEq ReqNeq w] - the two request sets are disjoint and each
      request vertex has exactly two neighbours and positive weight (this file); [x187_request_pair
      r x y] - x and y are the two distinct neighbours of r (this file); [x187_eq_request_satisfied]
      and [x187_neq_request_satisfied] (this file); [x187_total_request_weight] and
      [x187_satisfied_request_weight] (this file); [x187_satisfies_fraction ... p q col] - the
      cross-multiplied inequality p * total <= q * satisfied (this file); [x187_triangle_free G] -
      girth at least 4 (this file); [wagner_planar] (GTBase base/theories/base.v).
    Notes: The source's positive REAL alpha and positive RATIONAL weights are represented by a
      positive rational p/q and positive natural weights, which is no loss for finite request sets
      after clearing denominators. Corpus status: DISPROVED. The source proves this problem
      equivalent to Thomassen's exponentially-many-3-colourings conjecture, which Dvorak refuted in
      2021, so no such alpha exists and the statement as written is false; it is kept as the
      faithful encoding of the refuted problem. *)
Definition planar_triangle_free_request_graph_fraction_statement : Prop :=
  exists p q : nat,
    [/\ 0 < p, p <= q &
      forall (G : sgraph) (ReqEq ReqNeq : {set G}) (w : G -> nat),
        wagner_planar G ->
        x187_triangle_free G ->
        x187_request_graph ReqEq ReqNeq w ->
        exists col : G -> 'I_3,
          x187_proper_3_colouring col /\
          x187_satisfies_fraction ReqEq ReqNeq w p q col].


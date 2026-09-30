(** * Chromatic.conjectures.X151 -- v2 random chromatic concentration row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X151 vocabulary ***********************************************)

Definition x151_chi_in_interval
    (n c start : nat) (E : {set {set 'I_n}}) : bool :=
  let G := fg_labelled_sgraph E in
  (start <= χ([set: G])) && (χ([set: G]) <= start + c).

Definition x151_not_constant_concentrated (p q c : nat) : Prop :=
  exists a b : nat,
    [/\ 0 < a, a <= b &
      eventually (fun n =>
        forall start : nat,
          b * @fg_event_weight {set {set 'I_n}} (@fg_gnp_weight p q n)
                (fun E => x151_chi_in_interval c start E) <=
          (b - a) * @fg_total_weight {set {set 'I_n}} (@fg_gnp_weight p q n))].

(** ** X151 statements *****************************************************)

(** Corpus row: arxiv:0806.0178#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/0806.0178__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/0806.0178__00.json
    English statement: (Scott 2017, open problem on the lower bound for the concentration interval, arXiv:0806.0178)
      For every fixed rational edge probability p/q with 0 < p < q and every interval length c there
      are naturals a and b with 0 < a <= b such that, for all sufficiently large n, every starting
      value start satisfies the weight inequality b * (weight of the labelled graphs on n vertices
      whose chromatic number lies in the interval from start to start + c) <= (b - a) * (total
      weight); that is, the probability that the chromatic number of a random graph falls in an
      interval of constant length c stays bounded away from 1 by a fixed margin a/b, so the
      chromatic number is not concentrated on a constant number of values.
    Definitions: [x151_chi_in_interval n c start E] - the chromatic number of the labelled graph
      with edge set E lies between start and start + c (this file); [x151_not_constant_concentrated
      p q c] - the eventual weight gap described above (this file); [fg_labelled_sgraph E] - the
      simple graph on ['I_n] with edge set E (GTBase base/theories/finite_graph.v); [fg_gnp_weight p
      q n] - the exact G(n, p/q) weight p^|E| * (q-p)^(non-edges), so probabilities are cross-
      multiplied natural weights (finite_graph.v); [fg_event_weight] and [fg_total_weight]
      (finite_graph.v); [eventually P] - P holds for all sufficiently large n (GTBase
      base/theories/asymptotics.v).
    Notes: Probability is modelled exactly by natural weights rather than reals, and the negation
      of concentration is expressed as a uniform multiplicative gap a/b below the total weight,
      valid for all intervals of the given length c simultaneously. Corpus status: the problem was
      resolved by Heckel 2019 and 2021, who proved non-concentration on n^{1/4-o(1)} and then
      n^{1/2-o(1)} consecutive values; the row keeps the original source-facing name and is stated
      only. The row was retargeted in 2026-07-16 from a blocked placeholder to this axiom-free
      finite formulation, see meta/BLOCKED_RETARGETING_FOUNDATIONS.md. *)
Definition random_graph_chromatic_not_constant_concentrated_statement : Prop :=
  forall p q : nat,
    0 < p ->
    p < q ->
    forall c : nat,
      x151_not_constant_concentrated p q c.

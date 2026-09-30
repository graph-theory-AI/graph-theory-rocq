(** * Chromatic.conjectures.X81 -- v2 proper-orientation bipartite row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X81 vocabulary ************************************************)

Definition x81_orientation_of (G : sgraph) (D : rel G) : Prop :=
  (forall x y : G, D x y -> x -- y) /\
  forall x y : G, x -- y -> (D x y) (+) (D y x).

Definition x81_indegree (G : sgraph) (D : rel G) (v : G) : nat :=
  #|[set u : G | D u v]|.

Definition x81_proper_orientation (G : sgraph) (D : rel G) : Prop :=
  forall x y : G, x -- y -> x81_indegree D x != x81_indegree D y.

Definition x81_proper_orientation_bound (G : sgraph) (k : nat) : Prop :=
  exists D : rel G,
    x81_orientation_of D /\
    x81_proper_orientation D /\
    forall v : G, x81_indegree D v <= k.

(** ** X81 statements ******************************************************)

(** Corpus row: studies:std_ara_jo_cohen_de_rezende_havet_moura_conjecture_p
    Site: none
    Review: none
    English statement: (Araujo, Cohen, de Rezende, Havet and Moura, studies slice of the corpus)
      There is a constant C such that every bipartite finite simple graph admits a proper
      orientation whose maximum indegree k satisfies 2k <= Delta(G) + 2C, i.e. the proper
      orientation number is at most Delta(G)/2 + C.
    Definitions: [x81_orientation_of G D] - D only relates adjacent vertices and orients every
      edge exactly one way (this file); [x81_indegree D v] - the number of vertices sending an arc
      to v (this file); [x81_proper_orientation D] - adjacent vertices have different indegrees
      (this file); [x81_proper_orientation_bound G k] - some proper orientation has all indegrees at
      most k (this file); [bipartite], [Delta] (GTBase base/theories/base.v).
    Notes: This row has no site or review page in the corpus, hence the literal "none" above. The
      corpus row is a QUESTION; the Rocq body is its affirmative reading. Rather than defining the
      proper orientation number as a minimum, the body exhibits an orientation with a bound on all
      indegrees, which is equivalent to bounding that minimum. The inequality is doubled to avoid
      nat division. *)
Definition bipartite_proper_orientation_half_delta_constant_statement : Prop :=
  exists C : nat,
    forall G : sgraph,
      bipartite G ->
      exists k : nat,
        x81_proper_orientation_bound G k /\
        2 * k <= Delta G + 2 * C.

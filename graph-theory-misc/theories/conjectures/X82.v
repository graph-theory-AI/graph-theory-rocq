(** * GTMisc.conjectures.X82 -- v2 outerplanar proper-orientation row *)

From GTBase Require Export base.
From GraphTheory Require Import minor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X82 vocabulary ************************************************)

Definition x82_orientation_of (G : sgraph) (D : rel G) : Prop :=
  (forall x y : G, D x y -> x -- y) /\
  forall x y : G, x -- y -> (D x y) (+) (D y x).

Definition x82_indegree (G : sgraph) (D : rel G) (v : G) : nat :=
  #|[set u : G | D u v]|.

Definition x82_proper_orientation (G : sgraph) (D : rel G) : Prop :=
  forall x y : G, x -- y -> x82_indegree D x != x82_indegree D y.

Definition x82_proper_orientation_bound (G : sgraph) (k : nat) : Prop :=
  exists D : rel G,
    x82_orientation_of D /\
    x82_proper_orientation D /\
    forall v : G, x82_indegree D v <= k.

Definition x82_outerplanar (G : sgraph) : Prop :=
  ~ minor G 'K_4 /\ ~ minor G (KB 2 3).

(** ** X82 statements ******************************************************)

(** Corpus row: studies:std_araujo_havet_linhares_sales_silva_conjecture_on
    Site: none
    Review: none
    English statement: (Araujo, Havet, Linhares Sales and Silva, conjecture on the bounded
      proper orientation number of outerplanar graphs)
      There is a natural number C such that every outerplanar finite simple graph G admits an
      orientation of its edges in which adjacent vertices have different in-degrees and every
      in-degree is at most C.
    Definitions: [x82_orientation_of G D] - D orients every edge of G exactly one way and
      relates no non-adjacent pair (this file); [x82_indegree D v] - the number of vertices
      sending an arc to v (this file); [x82_proper_orientation D] - adjacent vertices receive
      distinct in-degrees (this file); [x82_proper_orientation_bound G k] - some proper
      orientation of G has all in-degrees at most k (this file); [x82_outerplanar G] -
      outerplanarity in the Chartrand-Harary minor sense, no K4 minor and no K2,3 minor (this
      file); [minor], ['K_4], [KB 2 3] - minors and the complete / complete-bipartite graphs
      (coq-graph-theory).
    Notes: the constant C is chosen before the graph, so "bounded" is uniform over the class.
      Outerplanarity is rendered by the forbidden-minor characterization rather than by an
      embedding. *)
Definition outerplanar_bounded_proper_orientation_number_statement : Prop :=
  exists C : nat,
    forall G : sgraph,
      x82_outerplanar G ->
      x82_proper_orientation_bound G C.

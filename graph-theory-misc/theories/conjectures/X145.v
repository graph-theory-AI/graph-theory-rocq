(** * GTMisc.conjectures.X145 -- v2 asymptotic dimension of planar graphs row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X145 vocabulary ***********************************************)

Definition x145_set_diameter_at_most (G : sgraph) (S : {set G}) (D : nat) : Prop :=
  forall x y : G, x \in S -> y \in S -> @graph_dist G x y <= D.

Definition x145_cover (G : sgraph) (I : finType) (U : I -> {set G}) : Prop :=
  forall v : G, exists i : I, v \in U i.

Definition x145_r_multiplicity_at_most
    (G : sgraph) (I : finType) (U : I -> {set G}) (r k : nat) : Prop :=
  forall v : G,
    #|[set i : I | [exists x in U i, @graph_dist G v x <= r]]| <= k.

Definition x145_class_asymptotic_dimension_at_most
    (C : sgraph -> Prop) (k : nat) : Prop :=
  forall r : nat,
    exists D : nat,
      forall G : sgraph,
        C G ->
        exists (I : finType) (U : I -> {set G}),
          x145_cover U /\
          (forall i : I, x145_set_diameter_at_most (U i) D) /\
          x145_r_multiplicity_at_most U r k.+1.

(** ** X145 statements *****************************************************)

(** Corpus row: studies:std_fujiwara_papasoglu_question_asymptotic_dimension
    Site: none
    Review: none
    English statement: (Fujiwara and Papasoglu, question on the asymptotic dimension of planar
      graphs)
      For every r there is a D such that every planar finite simple graph admits a finite
      family of vertex sets that covers all vertices, each of diameter at most D in the graph
      metric, and such that every vertex has at most 3 family members within distance r of it.
      That is, the class of planar graphs has asymptotic dimension at most 2.
    Definitions: [x145_set_diameter_at_most G S D] - all pairs of S are at graph distance at
      most D (this file); [x145_cover U] - the family U covers every vertex (this file);
      [x145_r_multiplicity_at_most U r k] - every vertex has at most k members of U containing
      a point within distance r (this file);
      [x145_class_asymptotic_dimension_at_most C k] - for every r there is a uniform diameter
      bound D such that every member of C has a D-bounded cover of r-multiplicity at most k+1
      (this file); [wagner_planar] - combinatorial Wagner planarity (GTBase); [graph_dist] -
      graph distance (GTBase graph_metric.v).
    Notes: retargeted on 2026-07-16 from a blocked placeholder to this axiom-free finite-witness
      formulation, see meta/BLOCKED_RETARGETING_FOUNDATIONS.md.  Asymptotic dimension at most k
      is rendered by the multiplicity form (covers of uniformly bounded diameter with
      r-multiplicity at most k+1), so dimension at most 2 becomes multiplicity at most 3; the
      diameter bound D is chosen after r and before the graph, which is the required
      uniformity over the class. *)
Definition fujiwara_papasoglu_planar_asymptotic_dimension_two_statement : Prop :=
  x145_class_asymptotic_dimension_at_most wagner_planar 2.

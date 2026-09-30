(** * GTMisc.conjectures.X29 -- v2 normal graph row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X29 vocabulary ************************************************)

Definition x29_complement_rel (G : sgraph) : rel G :=
  fun x y => (x != y) && ~~ (x -- y).

Lemma x29_complement_sym (G : sgraph) : symmetric (@x29_complement_rel G).
Proof. by move=> x y; rewrite /x29_complement_rel eq_sym sg_sym. Qed.

Lemma x29_complement_irrefl (G : sgraph) : irreflexive (@x29_complement_rel G).
Proof. by move=> x; rewrite /x29_complement_rel eqxx. Qed.

Definition x29_complement (G : sgraph) : sgraph :=
  SGraph (@x29_complement_sym G) (@x29_complement_irrefl G).

Definition x29_stable_set (G : sgraph) (S : {set G}) : Prop :=
  forall x y : G, x \in S -> y \in S -> ~~ (x -- y).

Definition x29_clique_cover (G : sgraph) (C : seq {set G}) : Prop :=
  (forall K : {set G}, K \in C -> clique K) /\
  forall v : G, exists K : {set G}, K \in C /\ v \in K.

Definition x29_stable_cover (G : sgraph) (S : seq {set G}) : Prop :=
  (forall I : {set G}, I \in S -> x29_stable_set I) /\
  forall v : G, exists I : {set G}, I \in S /\ v \in I.

Definition x29_normal_graph (G : sgraph) : Prop :=
  exists (C S : seq {set G}),
    x29_clique_cover C /\
    x29_stable_cover S /\
    forall (K I : {set G}), K \in C -> I \in S -> K :&: I != set0.

Definition x29_has_induced_cycle (G : sgraph) (n : nat) : Prop :=
  exists S : {set G},
    #|S| = n /\ inhabited (induced S ≃ cycle_graph n).

(** ** X29 statements ******************************************************)

(** Corpus row: studies:std_normal_graph_conjecture_de_simone_k_rner
    Site: none
    Review: none
    English statement: (De Simone and Korner, normal graph conjecture)
      Every finite simple graph G with no induced 5-cycle, no induced 7-cycle and whose
      complement has no induced 7-cycle is normal, i.e. there are a family of cliques covering
      all vertices and a family of stable sets covering all vertices such that every chosen
      clique meets every chosen stable set.
    Definitions: [x29_complement_rel] / [x29_complement G] - the complement graph (this file);
      [x29_stable_set S] - S is stable (this file); [x29_clique_cover C] - a list of cliques
      covering every vertex (this file); [x29_stable_cover S] - a list of stable sets covering
      every vertex (this file); [x29_normal_graph G] - such a pair of covers exists with every
      clique meeting every stable set (this file); [x29_has_induced_cycle G n] - some n-element
      vertex set induces a subgraph isomorphic to the n-cycle (this file); [cycle_graph],
      [induced], [clique] - GTBase / coq-graph-theory.
    Notes: "G has no induced complement of C7" is rendered as "the complement of G has no
      induced C7", which is equivalent since induced subgraphs commute with complementation.
      The covers are lists rather than sets, so repetitions are allowed, which is immaterial. *)
Definition no_c5_c7_complement_c7_normal_graph_statement : Prop :=
  forall G : sgraph,
    ~ x29_has_induced_cycle G 5 ->
    ~ x29_has_induced_cycle G 7 ->
    ~ x29_has_induced_cycle (x29_complement G) 7 ->
    x29_normal_graph G.

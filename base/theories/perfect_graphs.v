(** * Perfect finite simple graphs: a Prop adapter for the upstream owner

    [is_perfect_graph] is exactly the Boolean [GraphTheory.wpgt.perfect_mem]
    predicate on the full carrier, viewed as Prop. The subset and induced-
    carrier equalities below are characterizations of that existing predicate.
    There is no nonempty graph, nonempty subset or connectivity requirement.
    Equality of chi and omega on the whole graph alone is not the definition.
    Registry: perfect-graph (C12). *)
From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph coloring wpgt.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition is_perfect_graph (G : sgraph) : Prop := perfect [set: G].

Lemma is_perfect_graphP (G : sgraph) :
  reflect (is_perfect_graph G) (perfect [set: G]).
Proof. exact: idP. Qed.

Lemma is_perfect_graph_subsets (G : sgraph) :
  is_perfect_graph G <-> forall A : {set G}, χ(A) = ω(A).
Proof.
split.
- move/forall_inP=> perf A; apply/esym/eqP; apply: perf; exact: subsetT.
- move=> equal; apply/forall_inP=> A _; apply/eqP; exact: esym (equal A).
Qed.

Lemma is_perfect_graph_induced_subsets (G : sgraph) :
  is_perfect_graph G <->
  forall A : {set G}, χ([set: induced A]) = ω([set: induced A]).
Proof.
rewrite is_perfect_graph_subsets; split=> equal A.
- by rewrite chiT omegaT chi_induced omega_induced; exact: equal.
- have := equal A; by rewrite chiT omegaT chi_induced omega_induced.
Qed.

Lemma is_perfect_graph_whole (G : sgraph) :
  is_perfect_graph G -> χ([set: G]) = ω([set: G]).
Proof. by move/is_perfect_graph_subsets=> /(_ [set: G]). Qed.

Lemma is_perfect_graph_induced (G : sgraph) (A : {set G}) :
  is_perfect_graph G -> is_perfect_graph (induced A).
Proof.
move=> perf; rewrite /is_perfect_graph perfectT perfect_induced.
exact: sub_perfect (subsetT A) perf.
Qed.

Lemma is_perfect_graph_diso (G H : sgraph) (iso : diso G H) :
  is_perfect_graph G <-> is_perfect_graph H.
Proof. by rewrite /is_perfect_graph !perfectT (diso_perfectT iso). Qed.

Lemma is_perfect_graph_isubgraph (G H : sgraph) :
  G ⇀ H -> is_perfect_graph H -> is_perfect_graph G.
Proof. rewrite /is_perfect_graph !perfectT; exact: isubgraph_perfect. Qed.

Lemma is_perfect_graph_complement (G : sgraph) :
  is_perfect_graph G -> is_perfect_graph (compl G).
Proof. rewrite /is_perfect_graph !perfectT; exact: weak_perfect. Qed.

Lemma is_perfect_graph_complete n : is_perfect_graph 'K_n.
Proof.
apply/is_perfect_graph_subsets=> A.
have cA : clique A by apply: sub_clique; [exact: subsetT|by []].
rewrite (chi_clique cA); apply/esym/eqP; rewrite eqn_leq; apply/andP; split.
- by rewrite -(chi_clique cA) omega_leq_chi.
- by apply: clique_bound; rewrite inE subxx /=; apply/cliqueP.
Qed.

Lemma is_perfect_graph_empty : is_perfect_graph 'K_0.
Proof. exact: is_perfect_graph_complete. Qed.

Lemma is_perfect_graph_complement_complete n : is_perfect_graph (compl 'K_n).
Proof. apply: is_perfect_graph_complement; exact: is_perfect_graph_complete. Qed.

Lemma is_perfect_graph_hajnal (G : sgraph) :
  is_perfect_graph G <->
  forall A : {set G}, #|A| <= α(A) * ω(A).
Proof.
split.
- move/Hajnal=> perf A; apply: perf; exact: subsetT.
- move=> bound; apply/Hajnal=> A _; exact: bound.
Qed.

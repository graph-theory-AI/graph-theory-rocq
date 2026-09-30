(** * Extremal.conjectures.X105 -- v2 tree inducibility row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X105 vocabulary ***********************************************)

Definition x105_induced_copy_family
    (H G : sgraph) (C : {set {set G}}) : Prop :=
  forall S : {set G},
    S \in C <-> #|S| = #|H| /\ inhabited (induced S ≃ H).

Definition x105_path_tree (T : sgraph) : Prop :=
  is_tree [set: T] /\ Delta T <= 2.

Definition x105_star_tree (T : sgraph) : Prop :=
  is_tree [set: T] /\
  exists c : T, forall v : T, v != c -> v -- c /\ #|N(v)| = 1.

Definition x105_density_at_most
    (H G : sgraph) (C : {set {set G}}) (num den : nat) : Prop :=
  den * #|C| <= num * 'C(#|G|, #|H|).

(** Corpus row: studies:std_bubeck_linial_problem_4_tree_inducibility_bounde
    Site: none
    Review: none
    English statement: (Bubeck and Linial, "Bubeck-Linial problem 4 (tree inducibility bounded away from 1)")
      There is a positive rational eps = eps_num/eps_den < 1 such that for every tree T that is
      neither a star nor a path there is a threshold N with: for every graph G on at least N
      vertices, the number of vertex sets of G inducing a copy of T is at most
      (1 - eps) * binomial(|V(G)|, |V(T)|); that is, the inducibility of T is at most 1 - eps.
    Definitions: [x105_induced_copy_family T G C] - C is exactly the set of vertex sets S of G with
      |S| = |V(T)| whose induced subgraph is isomorphic to T (X105.v); [x105_path_tree T] - a
      tree of maximum degree at most 2 (X105.v); [x105_star_tree T] - a tree with a centre
      adjacent to every other vertex, all of which have degree 1 (X105.v);
      [x105_density_at_most T G C num den] - den * |C| <= num * binomial(|V(G)|, |V(T)|)
      (X105.v); [is_tree], [Delta], [induced], [~=] (graph isomorphism) - GTBase /
      coq-graph-theory.
    Notes: this row comes from the studies slice of the corpus, which has no site or review page.
      eps is a ratio of naturals with 0 < eps_num < eps_den, so 1 - eps is the nat fraction
      (eps_den - eps_num)/eps_den and the subtraction is safe. Inducibility, a limit of
      densities, is encoded as an EVENTUAL density bound (there is N beyond which every graph
      has density at most 1 - eps), which bounds the limit superior and is the intended
      content. N may depend on T, while eps may not, matching the source's universal epsilon. *)
Definition non_star_non_path_tree_inducibility_bounded_away_statement : Prop :=
  exists eps_num eps_den : nat,
    [/\ 0 < eps_num, eps_num < eps_den
      & forall T : sgraph,
          is_tree [set: T] ->
          ~ x105_star_tree T ->
          ~ x105_path_tree T ->
          exists N : nat,
            forall (G : sgraph) (C : {set {set G}}),
              N <= #|G| ->
              @x105_induced_copy_family T G C ->
              @x105_density_at_most T G C (eps_den - eps_num) eps_den].

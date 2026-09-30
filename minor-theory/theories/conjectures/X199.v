(** * Minor.conjectures.X199 -- v2 constant-size separator residue row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X199 vocabulary ***********************************************)

Definition x199_weight (G : sgraph) (rho : G -> nat) (S : {set G}) : nat :=
  \sum_(v in S) rho v.

Definition x199_weighted_balanced_separator
    (G : sgraph) (rho : G -> nat) (S M : {set G}) : Prop :=
  forall A : {set G},
    A \subset ~: (S :|: M) ->
    connected A ->
    2 * x199_weight rho A <= x199_weight rho [set: G].

Definition x199_weighted_balanced_separator_with_constant_M
    (C : sgraph -> Prop) (ell bound : nat) : Prop :=
  forall (G : sgraph) (rho : G -> nat),
    C G ->
    exists S M : {set G},
      [/\ #|M| <= bound,
          #|S| <= ell * sqrt_ceil #|G|.+1 + ell &
          x199_weighted_balanced_separator rho S M].

(** ** X199 statements *****************************************************)

(** Corpus row: arxiv:1710.03117#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1710.03117__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1710.03117__00.json
    English statement: (Dvorak 2018, informal conjecture in "On classes of graphs with
      strongly sublinear separators")
      For every class C of finite simple graphs there is a constant bound such that for every
      l at least 1, every graph G of C and every vertex weighting of G admit two vertex sets S
      and M with M of at most `bound` vertices, S of at most l times the integer ceiling square
      root of |V(G)|+1 plus l vertices, and every connected vertex set avoiding both S and M
      carrying at most half the total weight.
    Definitions: [x199_weight rho S] - the sum of the weights rho over S
      (minor-theory/theories/conjectures/X199.v);
      [x199_weighted_balanced_separator rho S M] - every connected vertex set disjoint from the
      union of S and M carries at most half the total weight (same file);
      [x199_weighted_balanced_separator_with_constant_M C l bound] - the above together with
      the two cardinality bounds on M and S (same file); [sqrt_ceil n] - the least s with
      n <= s^2 (base/theories/asymptotics.v).
    Notes: PROXY, and believed FALSE as encoded (faithfulness audit 2026-07-17,
      meta/BLOCKED_RETARGETING_AUDIT.md).  Three departures from the source.  First, the
      source fixes a class with polynomial omega-expansion; this statement quantifies over
      ALL classes C with no such hypothesis.  Second, the constant `bound` is chosen before l,
      whereas the source lets it depend on the class AND on l.  Third, the source's bound on
      the separator is the WEIGHTED one q(C) <= q(V(G))/l; here it is replaced by a cardinality
      bound l * sqrt_ceil(|V(G)|+1) + l.  The row is recorded as blocked for these reasons. *)
Definition strongly_sublinear_separator_constant_M_statement : Prop :=
  forall C : sgraph -> Prop,
    exists bound : nat,
      forall ell : nat,
        1 <= ell ->
        x199_weighted_balanced_separator_with_constant_M C ell bound.

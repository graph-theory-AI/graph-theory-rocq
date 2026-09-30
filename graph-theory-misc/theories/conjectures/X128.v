(** * GTMisc.conjectures.X128 -- v2 cheap balanced separators row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X128 vocabulary ***********************************************)

Fixpoint x128_poly_eval (p : seq nat) (x : nat) : nat :=
  if p is a :: q then a + x * x128_poly_eval q x else 0.

(** Radius-bounded branch sets for shallow minors. *)
Definition x128_radius_at_most (G : sgraph) (S : {set G}) (r : nat) : Prop :=
  exists c : G,
    c \in S /\ forall x : G, x \in S -> @graph_dist G c x <= r.

Definition x128_shallow_minor_model (G H : sgraph) (r : nat) : Prop :=
  exists branch : H -> {set G},
    (forall h : H, branch h != set0) /\
    (forall h : H, connected (branch h)) /\
    (forall h : H, x128_radius_at_most (branch h) r) /\
    (forall h1 h2 : H, h1 != h2 -> branch h1 :&: branch h2 = set0) /\
    (forall h1 h2 : H, h1 -- h2 ->
      exists x y : G, [/\ x \in branch h1, y \in branch h2 & x -- y]).

Definition x128_grad_at_most (G : sgraph) (r d : nat) : Prop :=
  forall H : sgraph,
    x128_shallow_minor_model G H r ->
    2 * fg_edge_count H <= d * #|H|.

Definition x128_expansion_bounded (G : sgraph) (p : seq nat) : Prop :=
  forall r : nat, x128_grad_at_most G r (x128_poly_eval p r).

Definition x128_weight (G : sgraph) (rho : G -> nat) (S : {set G}) : nat :=
  \sum_(v in S) rho v.

Definition x128_cheap_bal_sep (G : sgraph) (rho : G -> nat) (t k : nat) : Prop :=
  exists S Z : {set G},
    [/\ #|Z| <= k,
        t * x128_weight rho S <= x128_weight rho [set: G] &
        forall A : {set G},
          A \subset ~: (S :|: Z) ->
          connected A ->
          2 * x128_weight rho A <= x128_weight rho [set: G]].

(** ** X128 statements *****************************************************)

(** Corpus row: studies:std_dvo_k_conjecture_cheap_balanced_separators_with
    Site: none
    Review: none
    English statement: (Dvorak, conjecture on cheap balanced separators with few outliers for
      bounded-expansion graphs)
      For every polynomial p, given by its list of coefficients, there is a function q such
      that for every finite simple graph G whose expansion is bounded by p, every vertex cost
      assignment rho and every integer t >= 1, there are vertex sets S and Z with |Z| <= q(t),
      with t times the cost of S at most the total cost of V(G), and such that every connected
      subset A of the complement of S union Z has twice its cost at most the total cost.
    Definitions: [x128_poly_eval p x] - evaluation of the coefficient list p at x (this file);
      [x128_radius_at_most G S r] - S has a centre within distance r of all of S (this file);
      [x128_shallow_minor_model G H r] - H is a depth-r shallow minor of G, witnessed by
      non-empty, connected, pairwise disjoint branch sets of radius at most r, adjacent branch
      sets being joined by an edge (this file); [x128_grad_at_most G r d] - every depth-r
      shallow minor H of G satisfies 2 * |E(H)| <= d * |V(H)|, i.e. the greatest reduced
      average density at depth r is at most d/2 (this file); [x128_expansion_bounded G p] -
      that bound holds at every depth r with d = p(r) (this file); [x128_weight rho S] - the
      total cost of S (this file); [x128_cheap_bal_sep G rho t k] - the separator conclusion
      above, S being the (rho/t)-cheap separator and Z the at most k outliers (this file);
      [graph_dist] - graph distance (GTBase graph_metric.v); [fg_edge_count] - number of edges
      (GTBase finite_graph.v); [connected] - coq-graph-theory connectivity.
    Notes: retargeted on 2026-07-16 from a blocked placeholder to this axiom-free finite-witness
      formulation, see meta/BLOCKED_RETARGETING_FOUNDATIONS.md.  Modelling choices: costs are
      non-negative reals in the source and naturals here, and the polynomial p is a natural
      coefficient list, so both cheapness and balance are stated cross-multiplied over naturals;
      "balanced" is rendered as "every connected part left after removing S and Z carries at
      most half the total cost"; the outliers Z are exactly the vertices exempted from that
      balance requirement.  Bounded expansion is a hypothesis on the individual graph G rather
      than on a class. *)
Definition dvorak_cheap_balanced_separator_bounded_expansion_statement : Prop :=
  forall p : seq nat,
    exists q : nat -> nat,
      forall (G : sgraph) (rho : G -> nat) (t : nat),
        1 <= t ->
        x128_expansion_bounded G p ->
        x128_cheap_bal_sep rho t (q t).

(** * GTMisc.conjectures.X139 -- v2 polynomial-expansion/scol row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X139 vocabulary ***********************************************)

Fixpoint x139_poly_eval (p : seq nat) (x : nat) : nat :=
  if p is a :: q then a + x * x139_poly_eval q x else 0.

Definition x139_radius_at_most (G : sgraph) (S : {set G}) (r : nat) : Prop :=
  exists c : G,
    c \in S /\ forall x : G, x \in S -> @graph_dist G c x <= r.

Definition x139_shallow_minor_model (G H : sgraph) (r : nat) : Prop :=
  exists branch : H -> {set G},
    (forall h : H, branch h != set0) /\
    (forall h : H, connected (branch h)) /\
    (forall h : H, x139_radius_at_most (branch h) r) /\
    (forall h1 h2 : H, h1 != h2 -> branch h1 :&: branch h2 = set0) /\
    (forall h1 h2 : H, h1 -- h2 ->
      exists x y : G, [/\ x \in branch h1, y \in branch h2 & x -- y]).

Definition x139_grad_at_most (G : sgraph) (r d : nat) : Prop :=
  forall H : sgraph,
    x139_shallow_minor_model G H r ->
    2 * fg_edge_count H <= d * #|H|.

Definition x139_polynomial_expansion_class (C : sgraph -> Prop) : Prop :=
  exists p : seq nat,
    forall (r : nat) (G : sgraph), C G -> x139_grad_at_most G r (x139_poly_eval p r).

Definition x139_ordering (G : sgraph) (ord : G -> nat) : Prop := injective ord.

Definition x139_strong_reach_set
    (G : sgraph) (ord : G -> nat) (r : nat) (v : G) : {set G} :=
  [set u : G | (@graph_dist G v u <= r) && (ord u <= ord v)].

Definition x139_scol_at_most (G : sgraph) (r k : nat) : Prop :=
  exists ord : G -> nat,
    x139_ordering ord /\
    forall v : G, #|x139_strong_reach_set ord r v| <= k.

(** ** X139 statements *****************************************************)

(** Corpus row: studies:std_esperet_raymond_conjecture_polynomial_expansion
    Site: none
    Review: none
    English statement: (Esperet and Raymond, conjecture on polynomial expansion and strong
      colouring numbers)
      For every class C of finite simple graphs with polynomial expansion there is a polynomial
      f such that for every r and every graph G in C there is an injective vertex ordering in
      which every vertex v has at most f(r) vertices u with graph distance from v at most r and
      ordering value at most that of v.
    Definitions: [x139_poly_eval p x] - evaluation of a coefficient list (this file);
      [x139_radius_at_most], [x139_shallow_minor_model G H r], [x139_grad_at_most G r d] - the
      depth-r shallow-minor and reduced-average-density vocabulary, as in
      graph-theory-misc/theories/conjectures/X128.v (this file);
      [x139_polynomial_expansion_class C] - one coefficient list bounds the density of the
      depth-r shallow minors of every member of C, at every r (this file);
      [x139_ordering ord] - injectivity of the vertex ordering (this file);
      [x139_strong_reach_set ord r v] - the set of u with distance at most r from v and
      ord u <= ord v (this file); [x139_scol_at_most G r k] - some ordering makes every such
      set of size at most k (this file); [graph_dist] - graph distance (GTBase graph_metric.v);
      [fg_edge_count] - GTBase finite_graph.v.
    Notes: KNOWN UNFAITHFUL, row leg is blocked (faithfulness audit 2026-07-17,
      meta/BLOCKED_RETARGETING_AUDIT.md).  The strong r-colouring number scol_r requires u to be
      reachable from v by a path of length at most r all of whose INTERNAL vertices come after
      v in the ordering; [x139_strong_reach_set] drops that constraint and keeps only distance
      and the comparison of the two ordering values.  What is bounded here is therefore the
      backward r-ball, i.e. the colouring number of the r-th power of G, which is at least
      scol_r; the Rocq statement is consequently a strictly stronger claim than the conjecture,
      not an encoding of it.  Recorded in meta/STATEMENT_IMPROVEMENTS.md. *)
Definition esperet_raymond_polynomial_expansion_scol_statement : Prop :=
  forall C : sgraph -> Prop,
    x139_polynomial_expansion_class C ->
    exists f : seq nat,
      forall (r : nat) (G : sgraph),
        C G -> x139_scol_at_most G r (x139_poly_eval f r).

(** * Digraph.conjectures.XE2 -- Erdos solved clean rows *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition xe2_orients_edge (G : sgraph) (r : rel G) : Prop :=
  forall x y : G, x -- y -> (r x y = ~~ r y x).

Definition xe2_uses_only_edges (G : sgraph) (r : rel G) : Prop :=
  forall x y : G, r x y -> x -- y.

Definition xe2_directed_cycle (V : finType) (r : rel V) (c : seq V) : Prop :=
  ucycle r c /\ 2 < size c.

Definition xe2_acyclic_rel (V : finType) (r : rel V) : Prop :=
  forall c : seq V, ~ xe2_directed_cycle r c.

Definition xe2_reverse_one_edge (G : sgraph) (r : rel G) (a b : G) : rel G :=
  fun x y =>
    if (x == a) && (y == b) then false
    else if (x == b) && (y == a) then true
    else r x y.

Definition xe2_orientation_stays_acyclic_after_one_reversal
    (G : sgraph) (r : rel G) : Prop :=
  xe2_acyclic_rel r /\
  forall a b : G, r a b ->
    xe2_acyclic_rel (xe2_reverse_one_edge r a b).

Definition xe2_tournament (V : finType) (r : rel V) : Prop :=
  irreflexive r /\
  forall x y : V, x != y -> r x y = ~~ r y x.

Definition xe2_transitive_on (V : finType) (r : rel V) (S : {set V}) : Prop :=
  forall x y z : V,
    x \in S -> y \in S -> z \in S ->
    r x y -> r y z -> r x z.

Definition xe2_transitive_tournament_guarantee (n k : nat) : Prop :=
  (forall r : rel 'I_n,
      xe2_tournament r ->
      exists S : {set 'I_n}, #|S| = k /\ xe2_transitive_on r S) /\
  forall k' : nat,
    (forall r : rel 'I_n,
      xe2_tournament r ->
      exists S : {set 'I_n}, #|S| = k' /\ xe2_transitive_on r S) ->
    k' <= k.

(** Corpus row: erdos:1006
    Site: none
    Review: none
    English statement: (Erdos problem 1006)
      Every finite simple graph of girth at least 5 (no cycle of length 3 or 4) has an
      orientation of its edges that is acyclic and stays acyclic after reversing any single arc.
    Definitions: [xe2_uses_only_edges r] and [xe2_orients_edge r] - the relation r orients
      exactly the edges of the graph, one direction per edge (this file); [xe2_acyclic_rel r] -
      no directed cycle, a directed cycle being a [ucycle] of r with more than two vertices
      (this file); [xe2_reverse_one_edge r a b] - r with the single arc from a to b reversed
      (this file); [girth_geq G n] - no cycle shorter than n (GTBase base.v).
    Notes: The corpus asks the question for girth greater than 4, which is [girth_geq G 5]. The
      orientation is a relation rather than a digraph structure, so that reversing one arc is an
      update of the relation. Erdos rows carry no site or review page. *)
Definition erdos_1006_statement : Prop :=
  forall G : sgraph,
    girth_geq G 5 ->
    exists r : rel G,
      xe2_uses_only_edges r /\
      xe2_orients_edge r /\
      xe2_orientation_stays_acyclic_after_one_reversal r.

(** Corpus row: erdos:1216
    Site: none
    Review: none
    English statement: (Erdos problem 1216)
      For every n >= 1, the largest k such that every tournament on n vertices contains a
      transitive subtournament on k vertices equals floor(log2 n) + 1: every tournament on n
      vertices has a transitively ordered set of that size, and no larger value has that
      property.
    Definitions: [xe2_tournament r] - irreflexive relation on 'I_n that holds in exactly one
      direction between distinct vertices (this file); [xe2_transitive_on r S] - r is transitive
      on S (this file); [xe2_transitive_tournament_guarantee n k] - k is the largest guaranteed
      size (this file); [trunc_log 2 n] - floor of the base-2 logarithm (MathComp).
    Notes: The guarantee is stated with both a lower bound (every tournament has such a set of
      that size) and maximality (no larger k has the property), which pins the value f(n)
      exactly. Erdos rows carry no site or review page. *)
Definition erdos_1216_statement : Prop :=
  forall n : nat,
    0 < n ->
    xe2_transitive_tournament_guarantee n (trunc_log 2 n).+1.

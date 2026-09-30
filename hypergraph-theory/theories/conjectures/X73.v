(** * Hypergraph.conjectures.X73 -- v2 regular tripartite matching row *)

From GTBase Require Export base.
From Hypergraph.conjectures Require Import X6.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X73 vocabulary ************************************************)

Definition x73_balanced_tripartite
    (T : finType) (part : T -> 'I_3) (n : nat) : Prop :=
  forall i : 'I_3, #|[set v : T | part v == i]| = n.

Definition x73_hyperdegree (T : finType) (E : {set {set T}}) (v : T) : nat :=
  #|[set e in E | v \in e]|.

Definition x73_regular (T : finType) (E : {set {set T}}) (d : nat) : Prop :=
  forall v : T, x73_hyperdegree E v = d.

(** ** X73 statements ******************************************************)

(** Corpus row: studies:std_aharoni_charbit_howard_conjecture_on_matchings_i
    Site: none
    Review: none
    English statement: (Aharoni, Charbit and Howard, conjecture on matchings in d-regular
      tripartite 3-uniform hypergraphs)
      In every d-regular 3-partite 3-uniform hypergraph with d at least 1, n vertices in each of
      the three parts and no repeated hyperedges, there is a matching of at least the floor of
      (d-1)n/d hyperedges.
    Definitions: [x73_balanced_tripartite part n] - each of the three parts determined by the
      vertex map part has exactly n vertices (hypergraph-theory/theories/conjectures/X73.v);
      [x73_hyperdegree E v] - the number of hyperedges containing v (same file);
      [x73_regular E d] - every vertex lies in exactly d hyperedges (same file);
      [x6_r_partite_uniform part E] - every hyperedge meets each part in exactly one vertex, so
      it is 3-uniform (hypergraph-theory/theories/conjectures/X6.v); [x6_matching M E] - a subfamily of
      pairwise disjoint hyperedges (same file).
    Notes: a hyperedge family is a [{set {set T}}], so "not containing repeated edges" holds by
      construction.  The floor of (d-1)n/d is [(d.-1 * n) %/ d], natural division;
      [d.-1] is the predecessor, faithful because d is at least 1.  [x73_hyperdegree] and
      [x73_regular] duplicate [x6_hg_degree] of X6.v and the degree vocabulary of U12.v (see
      meta/STATEMENT_IMPROVEMENTS.md). *)
Definition regular_tripartite_hypergraph_matching_lower_bound_statement : Prop :=
  forall (d n : nat) (T : finType) (part : T -> 'I_3) (E : {set {set T}}),
    1 <= d ->
    x73_balanced_tripartite part n ->
    @x6_r_partite_uniform T 3 part E ->
    x73_regular E d ->
    exists M : {set {set T}},
      x6_matching M E /\ ((d.-1 * n) %/ d <= #|M|).

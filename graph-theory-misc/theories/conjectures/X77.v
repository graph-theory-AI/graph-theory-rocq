(** * GTMisc.conjectures.X77 -- v2 separation dimension row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X77 vocabulary ************************************************)

Definition x77_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

Definition x77_separates_edges
    (G : sgraph) (pos : G -> nat) (e f : {set G}) : Prop :=
  (forall x y : G, x \in e -> y \in f -> pos x < pos y) \/
  (forall x y : G, x \in e -> y \in f -> pos y < pos x).

Definition x77_separation_dimension_at_most (G : sgraph) (k : nat) : Prop :=
  exists pos : 'I_k -> G -> nat,
    (forall i : 'I_k, injective (pos i)) /\
    forall e f : {set G},
      e \in x77_edge_set G ->
      f \in x77_edge_set G ->
      e != f ->
      [disjoint e & f] ->
      exists i : 'I_k, x77_separates_edges (pos i) e f.

(** ** X77 statements ******************************************************)

(** Corpus row: studies:std_alon_et_al_conjecture_on_separation_dimension_an
    Site: none
    Review: none
    English statement: (Alon et al., conjecture on separation dimension and maximum degree)
      There is a constant c such that every finite simple graph G has separation dimension at
      most c * Delta(G): there are c * Delta(G) injective vertex orderings such that any two
      distinct disjoint edges of G are separated by one of them, an ordering separating two
      edges when all endpoints of the first precede all endpoints of the second, or conversely.
    Definitions: [x77_edge_set G] - the edges of G as two-element vertex sets (this file);
      [x77_separates_edges pos e f] - under the position map pos, every vertex of e precedes
      every vertex of f, or the other way round (this file);
      [x77_separation_dimension_at_most G k] - k injective orderings exist separating every
      pair of distinct disjoint edges (this file); [Delta] - maximum degree (GTBase).
    Notes: the source writes O(Delta); the Rocq body fixes the implied constant c before the
      graph, which is the intended uniform reading.  Only disjoint pairs of edges are required
      to be separated, which is the standard definition of separation dimension; orderings are
      given as injective maps into the naturals, hence as linear orders on the vertices. *)
Definition separation_dimension_maximum_degree_linear_statement : Prop :=
  exists c : nat,
    forall G : sgraph,
      x77_separation_dimension_at_most G (c * Delta G).

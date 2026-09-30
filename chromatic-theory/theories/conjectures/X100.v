(** * Chromatic.conjectures.X100 -- v2 modular edge-colouring row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X100 vocabulary ***********************************************)

Definition x100_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} | (#|e| == 2) && cliqueb e].

Definition x100_col_deg
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (v : G) (c : 'I_q) : nat :=
  \sum_(e in x100_edge_set G | (v \in e) && (col e == c)) 1.

Definition x100_modular_edge_colouring
    (G : sgraph) (k q : nat) (col : {set G} -> 'I_q) : Prop :=
  forall (v : G) (c : 'I_q),
    x100_col_deg col v c = 0 \/ x100_col_deg col v c %% k = 1.

Definition x100_modular_edge_colourable
    (G : sgraph) (k q : nat) : Prop :=
  exists col : {set G} -> 'I_q, @x100_modular_edge_colouring G k q col.

(** ** X100 statements *****************************************************)

(** Corpus row: studies:std_botler_colucci_kohayakawa_modular_edge_colouring
    Site: none
    Review: none
    English statement: (Botler, Colucci and Kohayakawa, studies slice of the corpus)
      For every integer k >= 2 there is a constant C, depending on k but not on the graph, such that
      every finite simple graph admits a modular k-edge-colouring with k + C colours, i.e. an
      assignment of colours to the edges such that at every vertex, for every colour, the number of
      incident edges of that colour is either 0 or congruent to 1 modulo k.
    Definitions: [x100_modular_edge_colouring G k q col] - for every vertex v and colour c, the
      number of edges at v coloured c is 0 or is 1 modulo k (this file); [x100_col_deg col v c] -
      that number, counted over [x100_edge_set G] (this file); [x100_edge_set G] - the 2-element
      vertex sets that are cliques, i.e. the edges (this file); [x100_modular_edge_colourable G k q]
      - such a colouring with q colours exists (this file).
    Notes: This row has no site or review page in the corpus, hence the literal "none" above. The
      source bound chi'_k(G) <= k + C is encoded as colourability with exactly k + C colours, which
      is equivalent since a colouring with fewer colours can be seen as one with k + C. The constant
      C is chosen after k and before the graph, matching "there is a constant C such that ... for
      every graph G". *)
Definition modular_edge_colouring_k_plus_constant_statement : Prop :=
  forall k : nat,
    2 <= k ->
    exists C : nat,
      forall G : sgraph,
        x100_modular_edge_colourable G k (k + C).

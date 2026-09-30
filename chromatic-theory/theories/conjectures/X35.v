(** * Chromatic.conjectures.X35 -- v2 sparse cut chromatic row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X35 vocabulary ************************************************)

Definition x35_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

(** A GENUINE cut/separator (arXiv:2510.01791, Conjecture 1.3): deleting [X]
    disconnects [G], i.e. the subgraph induced on [V(G) \ X] (= [~: X]) is
    disconnected.  Empty [X] is a legitimate cut exactly when [G] itself is
    disconnected -- the folklore [k = 1] case (chi(G[emptyset]) = 0 < 1). *)
Definition x35_nontrivial_cut (G : sgraph) (X : {set G}) : Prop :=
  disconnected (~: X).

(** ** X35 statements ******************************************************)

(** Corpus row: arxiv:2510.01791#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2510.01791__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2510.01791__00.json
    English statement: (Aubian, Bonamy, Bourneuf, Fontaine and Picasarri-Arrieta 2025, Conjecture 1.3, arXiv:2510.01791)
      For every k > 0 and every finite simple graph G with at least k vertices, if 2|E(G)| <
      2k|V(G)| - k(k+1), i.e. |E(G)| < k|V(G)| - k(k+1)/2, then G has a vertex set X whose deletion
      disconnects G and whose induced subgraph has chromatic number less than k.
    Definitions: [x35_edge_set G] - the edges as 2-element vertex sets (this file);
      [x35_nontrivial_cut G X] - the subgraph induced on the complement of X is [disconnected], so X
      is a genuine cut; the empty set is a cut exactly when G itself is disconnected (this file);
      [disconnected] (coq-graph-theory connectivity.v via GTBase).
    Notes: The source inequality is multiplied by 2 to avoid the halving; the nat subtraction on
      the right is harmless under the guard k <= #|G| and 0 < k, where 2k|V| is at least k(k+1).
      Corpus status: DISPROVED in the very paper that states it, which shows the corresponding
      threshold is asymptotically k/2 rather than k; the statement is kept as the faithful encoding
      of the refuted conjecture. *)
Definition sparse_graph_low_chromatic_cut_statement : Prop :=
  forall (k : nat) (G : sgraph),
    0 < k ->
    k <= #|G| ->
    (2 * #|x35_edge_set G| < 2 * k * #|G| - k * k.+1)%N ->
    exists X : {set G},
      x35_nontrivial_cut X /\
      χ([set: induced X]) < k.

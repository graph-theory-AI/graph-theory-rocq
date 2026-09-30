(** * GTMisc.conjectures.X37 -- v2 regular irregular-subgraph row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X37 vocabulary ************************************************)

Definition x37_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

Definition x37_subgraph_degree
    (G : sgraph) (F : {set {set G}}) (v : G) : nat :=
  #|[set e in F | v \in e]|.

Definition x37_degree_class_size
    (G : sgraph) (F : {set {set G}}) (k : nat) : nat :=
  #|[set v : G | x37_subgraph_degree F v == k]|.

Definition x37_close_to_uniform_degree_class
    (G : sgraph) (d : nat) (F : {set {set G}}) (k : nat) : Prop :=
  let m := x37_degree_class_size F k in
  (d.+1 * m <= #|G| + 2 * d.+1)%N /\
  (#|G| <= d.+1 * (m + 2))%N.

(** ** X37 statements ******************************************************)

(** Corpus row: arxiv:2108.02685#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2108.02685__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2108.02685__00.json
    English statement: (Alon and Wei 2021, "Irregular Subgraphs", Conjecture 1.1)
      For every d and every d-regular finite simple graph G there is a set F of edges of G
      such that, for every k <= d, the number m of vertices having exactly k incident edges in
      F satisfies (d+1) * m <= |V(G)| + 2 * (d+1) and |V(G)| <= (d+1) * (m + 2), which is the
      fraction-free form of |m - |V(G)|/(d+1)| <= 2.
    Definitions: [x37_edge_set G] - the edges of G as two-element vertex sets (this file);
      [x37_subgraph_degree F v] - the number of edges of F containing v (this file);
      [x37_degree_class_size F k] - the number of vertices of F-degree exactly k, the m(H,k) of
      the source (this file); [x37_close_to_uniform_degree_class G d F k] - the two
      cross-multiplied inequalities above (this file); [regular G d] - every vertex has degree
      d (GTBase).
    Notes: a spanning subgraph H of G is modelled by its edge set F, all vertices being kept,
      which is what "spanning" means here.  The two-sided bound is stated fraction-free over
      naturals, so no subtraction of a rational is involved. *)
Definition regular_graph_spanning_subgraph_degree_class_balance_statement : Prop :=
  forall (d : nat) (G : sgraph),
    regular G d ->
    exists F : {set {set G}},
      F \subset x37_edge_set G /\
      forall k : nat,
        k <= d ->
        @x37_close_to_uniform_degree_class G d F k.

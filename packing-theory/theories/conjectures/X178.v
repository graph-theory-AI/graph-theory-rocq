(** * Packing.conjectures.X178 -- v2 Gallai odd-semiclique path row *)

From GTBase Require Export base.
From Packing.conjectures Require Import U9.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X178 vocabulary ***********************************************)

Definition x178_path_seq (G : sgraph) (p : seq G) : Prop :=
  (p != [::]) /\ uniq p /\ sorted (--) p.

Definition x178_path_edge_set (G : sgraph) (p : seq G) : {set {set G}} :=
  [set e : {set G} |
    [exists x : G, [exists y : G,
      [&& x -- y, e == [set x; y], x \in p, y \in p & @consec G p x y]]]].

Definition x178_path_decomposition_at_most (G : sgraph) (m : nat) : Prop :=
  exists (r : nat) (P : 'I_r -> seq G),
    [/\ r <= m,
        (forall i : 'I_r, x178_path_seq (P i)),
        (forall i j : 'I_r,
            i != j ->
            [disjoint x178_path_edge_set (P i) & x178_path_edge_set (P j)])
      & \bigcup_(i : 'I_r) x178_path_edge_set (P i) = edge_setG G].

Definition x178_missing_edges (G : sgraph) : {set {set G}} :=
  [set e : {set G} | (#|e| == 2) && ~~ cliqueb e].

Definition x178_odd_semi_clique (G : sgraph) : Prop :=
  exists k : nat,
    [/\ 1 <= k, #|G| = 2 * k + 1 & #|x178_missing_edges G| <= k.-1].

(** ** X178 statements *****************************************************)

(** Corpus row: arxiv:1609.06257#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1609.06257__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1609.06257__00.json
    English statement: (Bonamy and Perrett 2016, "Question 1.1")
      For every connected simple graph G that is not an odd semi-clique, the edge set
      of G decomposes into at most floor(|V(G)|/2) paths: there are an r with
      r <= floor(|V(G)|/2) and vertex sequences P_0, ..., P_{r-1}, each a nonempty path
      with pairwise distinct vertices, whose edge sets are pairwise disjoint and whose
      union is the whole edge set of G.
    Definitions: [x178_path_seq p] — p is nonempty, has no repeated vertex and has
      consecutive entries adjacent (this file); [x178_path_edge_set p] — the edges
      {x, y} of G whose endpoints are consecutive on p (this file, via U9's [consec]);
      [x178_path_decomposition_at_most G m] — such a family of at most m paths (this
      file); [x178_missing_edges G] — the two-element vertex sets that are not cliques,
      i.e. the non-edges (this file); [x178_odd_semi_clique G] — |V(G)| = 2k+1 for some
      k >= 1 with at most k-1 non-edges (this file); [edge_setG] — U9.v; [cliqueb],
      [connected] — coq-graph-theory.
    Notes: the corpus row is partial: the question is settled for planar graphs
      (Blanche, Bonamy, Bonichon 2021) and for 2-degenerate graphs (Anto, Basavaraju
      2022), and open in general. Floor division is MathComp's %/; odd semi-cliques are
      encoded by their counting characterisation (2k+1 vertices, at most k-1 missing
      edges) rather than as an explicit construction from a clique. *)
Definition gallai_odd_semiclique_path_decomposition_statement : Prop :=
  forall G : sgraph,
    connected [set: G] ->
    ~ x178_odd_semi_clique G ->
    x178_path_decomposition_at_most G (#|G| %/ 2).


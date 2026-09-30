(** * Packing.conjectures.XE1 -- Erdos open clean/bounded rows *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition xe1_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

Definition xe1_stable_set (G : sgraph) (S : {set G}) : Prop :=
  forall x y : G, x \in S -> y \in S -> x -- y -> False.

Definition xe1_maximal_clique (G : sgraph) (K : {set G}) : Prop :=
  clique K /\
  forall L : {set G}, K \proper L -> ~ clique L.

Definition xe1_clique_transversal (G : sgraph) (X : {set G}) : Prop :=
  forall K : {set G}, xe1_maximal_clique K -> 2 <= #|K| -> X :&: K != set0.

Definition xe1_clique_transversal_number (G : sgraph) (t : nat) : Prop :=
  (exists X : {set G}, xe1_clique_transversal X /\ #|X| = t) /\
  forall u : nat, (exists X : {set G}, xe1_clique_transversal X /\ #|X| = u) -> t <= u.

Definition xe1_triangle_free_independence_guarantee (n h : nat) : Prop :=
  (forall G : sgraph,
      #|G| = n -> triangle_free G ->
      exists A : {set G}, xe1_stable_set A /\ h <= #|A|) /\
  forall h' : nat,
    (forall G : sgraph,
      #|G| = n -> triangle_free G ->
      exists A : {set G}, xe1_stable_set A /\ h' <= #|A|) -> h' <= h.

Definition xe1_tree (T : sgraph) : Prop :=
  is_forest [set: T] /\ connected [set: T].

Definition xe1_image_edges (G T : sgraph) (f : T -> G) : {set {set G}} :=
  [set e : {set G} |
      [exists x : T, [exists y : T,
        (x -- y) && (e == [set f x; f y])]]].

Definition xe1_edge_disjoint_tree_packing
    (n : nat) (T : forall k : 'I_n, sgraph) (emb : forall k : 'I_n, T k -> 'I_n)
    : Prop :=
  (forall k : 'I_n, injective (emb k)) /\
  (forall i j : 'I_n, i != j ->
      [disjoint @xe1_image_edges 'K_n (T i) (emb i)
              & @xe1_image_edges 'K_n (T j) (emb j)]) /\
  (forall e : {set 'I_n}, #|e| = 2 ->
      exists k : 'I_n, e \in @xe1_image_edges 'K_n (T k) (emb k)).

Definition xe1_induced_cycle (G : sgraph) (c : seq G) : Prop :=
  ucycle (--) c /\ 2 < size c /\
  forall x y : G, x \in c -> y \in c -> x != y -> x -- y ->
    ((x, y) \in zip c (rot 1 c)) || ((y, x) \in zip c (rot 1 c)).

Definition xe1_chordal (G : sgraph) : Prop :=
  forall c : seq G, xe1_induced_cycle c -> size c <= 3.

Definition xe1_clique_edge_set (G : sgraph) (K : {set G}) : {set {set G}} :=
  [set e in xe1_edge_set G | e \subset K].

Definition xe1_clique_edge_partition
    (G : sgraph) (m : nat) (K : 'I_m -> {set G}) : Prop :=
  (forall i : 'I_m, clique (K i)) /\
  (forall i j : 'I_m, i != j ->
      [disjoint xe1_clique_edge_set (K i) & xe1_clique_edge_set (K j)]) /\
  (forall e : {set G}, e \in xe1_edge_set G ->
      exists i : 'I_m, e \in xe1_clique_edge_set (K i)).

Definition xe1_independent_set_count (G : sgraph) (k : nat) : nat :=
  #|[set S : {set G} | (#|S| == k) && [forall x in S, [forall y in S, ~~ (x -- y)]] ]|.

Definition xe1_unimodal_independent_sequence (G : sgraph) : Prop :=
  exists m : nat,
    (forall i : nat, i < m -> xe1_independent_set_count G i <= xe1_independent_set_count G i.+1) /\
    forall i : nat, m <= i -> xe1_independent_set_count G i.+1 <= xe1_independent_set_count G i.

(** Corpus row: erdos:151
    Site: none
    Review: none
    English statement: (Erdos problem #151)
      For every simple graph G on n vertices: if h is the largest number such that
      every triangle-free graph on n vertices has an independent set of at least h
      vertices, and t is the clique transversal number of G — the least size of a
      vertex set meeting every maximal clique with at least two vertices — then
      t <= n - h.
    Definitions: [xe1_stable_set S] — no two members of S are adjacent (this file);
      [xe1_maximal_clique K] — a clique with no proper clique superset (this file);
      [xe1_clique_transversal X] — X meets every maximal clique of at least two
      vertices (this file); [xe1_clique_transversal_number G t] — t is attained by some
      clique transversal and no clique transversal has smaller size (this file);
      [xe1_triangle_free_independence_guarantee n h] — every triangle-free graph on n
      vertices has an independent set of at least h vertices, and h is the greatest
      such guarantee, i.e. H(n) (this file); [triangle_free] — GTBase base; [clique] —
      coq-graph-theory sgraph.v.
    Notes: n - h is MathComp's truncated natural subtraction. Both H(n) and the clique
      transversal number are characterised relationally (a witness plus an extremality
      clause) rather than as functions, so no existence proof for the extrema is
      needed; the hypotheses on h and t are therefore load-bearing. *)
Definition erdos_151_statement : Prop :=
  forall (G : sgraph) (n h t : nat),
    #|G| = n ->
    xe1_triangle_free_independence_guarantee n h ->
    xe1_clique_transversal_number G t ->
    t <= n - h.

(** Corpus row: erdos:743
    Site: none
    Review: none
    English statement: (Erdos problem #743)
      For every n >= 2 and every family of trees T_0, ..., T_{n-1} in which T_k has
      exactly k+1 vertices, there are injective maps emb_k from V(T_k) into the vertex
      set of the complete graph K_n such that the edge images of distinct trees are
      disjoint and every two-element vertex set of K_n is covered by the edge image of
      some tree — that is, K_n is the edge-disjoint union of the T_k.
    Definitions: [xe1_tree T] — [is_forest [set: T]] together with
      [connected [set: T]] (this file); [xe1_image_edges f] — the set of pairs
      {f x, f y} for adjacent x, y of the source graph (this file);
      [xe1_edge_disjoint_tree_packing n T emb] — each emb k injective, edge images of
      distinct trees disjoint, and every pair of K_n covered (this file); [is_forest],
      [connected] — coq-graph-theory sgraph.v.
    Notes: the source's indexing T_2, ..., T_n with |T_k| = k is shifted to 'I_n with
      |T_k| = k+1, so the family runs over trees on 1, 2, ..., n vertices; the extra
      one-vertex tree contributes no edge, and the total edge count is still
      0 + 1 + ... + (n-1) = |E(K_n)|, so the two readings agree. The vertex set of K_n
      is 'I_n and edges are its two-element subsets. *)
Definition erdos_743_statement : Prop :=
  forall n : nat, 2 <= n ->
    forall T : forall k : 'I_n, sgraph,
      (forall k : 'I_n, #|T k| = (val k).+1 /\ xe1_tree (T k)) ->
      exists emb : forall k : 'I_n, T k -> 'I_n,
        @xe1_edge_disjoint_tree_packing n T emb.

(** Corpus row: erdos:81
    Site: none
    Review: none
    English statement: (Erdos problem #81)
      There is a constant C such that every chordal simple graph G on n vertices admits
      a partition of its edge set into m cliques with 6 * m <= n^2 + C * n, that is,
      into n^2/6 + O(n) cliques.
    Definitions: [xe1_edge_set G] — the two-element vertex sets {x, y} with x -- y
      (this file); [xe1_induced_cycle c] — a uniq cycle on more than two vertices whose
      only adjacencies among its vertices are the consecutive ones, i.e. a chordless
      cycle (this file); [xe1_chordal G] — every induced cycle has at most three
      vertices (this file); [xe1_clique_edge_set K] — the edges of G with both
      endpoints in K (this file); [xe1_clique_edge_partition K] — the K i are cliques,
      their edge sets are pairwise disjoint, and every edge of G lies in one of them
      (this file); [clique], [ucycle] — coq-graph-theory / MathComp.
    Notes: "n^2/6 + O(n)" is rendered fraction-free as one constant C, quantified
      before the graph, with 6 * m <= n^2 + C * n. The partition need only exist: m is
      not required to be the minimum number of cliques. *)
Definition erdos_81_statement : Prop :=
  exists C : nat,
    forall (G : sgraph) (n : nat),
      #|G| = n -> xe1_chordal G ->
      exists m : nat, exists K : 'I_m -> {set G},
        xe1_clique_edge_partition K /\
        6 * m <= n ^ 2 + C * n.

(** Corpus row: erdos:993
    Site: none
    Review: none
    English statement: (Erdos problem #993)
      For every simple graph T whose vertex set induces a forest, the independent-set
      sequence of T is unimodal: there is an m such that the number of independent sets
      of size i is nondecreasing in i for i below m, and nonincreasing from m on.
    Definitions: [xe1_independent_set_count G k] — the number of k-element vertex sets
      with no edge inside (this file); [xe1_unimodal_independent_sequence G] — the
      existence of such an m (this file); [is_forest] — coq-graph-theory sgraph.v.
    Notes: the source says "any tree or forest"; the body quantifies over forests only,
      which subsumes trees, so no connectedness hypothesis is needed. The two monotone
      runs are stated for all natural i (not only up to |V(T)|), which is harmless
      since the counts are eventually 0. *)
Definition erdos_993_statement : Prop :=
  forall T : sgraph,
    is_forest [set: T] ->
    xe1_unimodal_independent_sequence T.

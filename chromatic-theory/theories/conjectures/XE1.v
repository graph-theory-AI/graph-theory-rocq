(** * Chromatic.conjectures.XE1 -- Erdős open clean/bounded rows *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local vocabulary ****************************************************)

Definition xe1_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

Definition xe1_edge_count (G : sgraph) : nat := #|xe1_edge_set G|.

Definition xe1_subgraph_of (H G : sgraph) : Prop :=
  exists f : H -> G, injective f /\ forall x y : H, x -- y -> f x -- f y.

Definition xe1_stable_set (G : sgraph) (S : {set G}) : Prop :=
  forall x y : G, x \in S -> y \in S -> x -- y -> False.

Definition xe1_vertices_of_seq (G : sgraph) (c : seq G) : {set G} :=
  [set v : G | v \in c].

Definition xe1_consecutive_in_cycle (G : sgraph) (c : seq G) (u v : G) : bool :=
  ((u, v) \in zip c (rot 1 c)) || ((v, u) \in zip c (rot 1 c)).

Definition xe1_cycle (G : sgraph) (c : seq G) : Prop :=
  ucycle (--) c /\ 2 < size c.

Definition xe1_cycle_diagonal_count (G : sgraph) (c : seq G) : nat :=
  #|[set p : G * G |
      [&& p.1 \in c, p.2 \in c, (enum_rank p.1 < enum_rank p.2)%N,
          p.1 -- p.2 & ~~ xe1_consecutive_in_cycle c p.1 p.2]]|.

Definition xe1_odd_cycle_with_diagonals (G : sgraph) (d : nat) : Prop :=
  exists c : seq G,
    xe1_cycle c /\ odd (size c) /\ d <= xe1_cycle_diagonal_count c.

Definition xe1_induced_subgraph_chi_le (G : sgraph) (r b : nat) : Prop :=
  forall S : {set G}, #|S| <= r -> χ([set: induced S]) <= b.

Definition xe1_unbounded (f : nat -> nat) : Prop :=
  forall M : nat, exists n : nat, M <= f n.

Definition xe1_delete_edges_rel (G : sgraph) (F : {set {set G}}) : rel G :=
  fun x y => (x -- y) && ([set x; y] \notin F).

Lemma xe1_delete_edges_sym (G : sgraph) (F : {set {set G}}) :
  symmetric (@xe1_delete_edges_rel G F).
Proof.
move=> x y; rewrite /xe1_delete_edges_rel.
rewrite sgP.
by rewrite setUC.
Qed.

Lemma xe1_delete_edges_irrefl (G : sgraph) (F : {set {set G}}) :
  irreflexive (@xe1_delete_edges_rel G F).
Proof. by move=> x; rewrite /xe1_delete_edges_rel sg_irrefl. Qed.

Definition xe1_delete_edges (G : sgraph) (F : {set {set G}}) : sgraph :=
  SGraph (@xe1_delete_edges_sym G F) (@xe1_delete_edges_irrefl G F).

Definition xe1_vertex_critical (G : sgraph) (k : nat) : Prop :=
  forall v : G, χ([set: induced (~: [set v])]) < k.

Definition xe1_edge_critical_set (G : sgraph) (F : {set {set G}}) (k : nat) : Prop :=
  F \subset @xe1_edge_set G /\ χ([set: @xe1_delete_edges G F]) < k.

Definition xe1_all_edge_critical_sets_large (G : sgraph) (r k : nat) : Prop :=
  forall F : {set {set G}}, xe1_edge_critical_set F k -> r < #|F|.

Definition xe1_strongly_independent_edges (G : sgraph) (F : {set {set G}}) : Prop :=
  F \subset @xe1_edge_set G /\
  forall e1 e2 : {set G}, e1 \in F -> e2 \in F -> e1 != e2 ->
    [disjoint e1 & e2] /\
    forall x y : G, x \in e1 -> y \in e2 -> x -- y -> False.

Definition xe1_strong_edge_colouring (G : sgraph) (k : nat) : Prop :=
  if @xe1_edge_set G == set0 then k = 0 else
    exists col : {set G} -> 'I_k,
      forall i : 'I_k,
        @xe1_strongly_independent_edges G [set e in @xe1_edge_set G | col e == i].

Definition xe1_strong_chromatic_index (G : sgraph) (k : nat) : Prop :=
  xe1_strong_edge_colouring G k /\
  forall j : nat, xe1_strong_edge_colouring G j -> k <= j.

(** ** XE1 statements ******************************************************)

(** Corpus row: erdos:108
    Site: none
    Review: none
    English statement: (Erdos Problems #108)
      For all r >= 4 and k >= 2 there is a finite bound f such that every finite simple graph with
      chromatic number at least f contains a subgraph of girth at least r and chromatic number at
      least k.
    Definitions: [xe1_subgraph_of H G] - there is an injective adjacency-preserving map from H
      into G, i.e. H embeds as a subgraph, not necessarily induced (this file); [girth_geq H r] -
      every cycle of H has at least r vertices (GTBase base/theories/base.v).
    Notes: This row has no site or review page in the corpus, hence the literal "none" above. The
      corpus row is a QUESTION, "is there some finite f(k,r)?"; the Rocq body is its affirmative
      reading, the bound f being chosen after r and k and before G. [xe1_subgraph_of] allows extra
      edges in the image, which is the correct reading of "subgraph" here. *)
Definition erdos_108_statement : Prop :=
  forall r k : nat, 4 <= r -> 2 <= k ->
    exists f : nat,
      forall G : sgraph,
        f <= χ([set: G]) ->
        exists H : sgraph,
          xe1_subgraph_of H G /\ girth_geq H r /\ k <= χ([set: H]).

(** Corpus row: erdos:149
    Site: none
    Review: none
    English statement: (Erdos Problems #149)
      For every finite simple graph G whose strong chromatic index is sq, 4 * sq <= 5 * Delta(G)^2,
      the integer form of sq(G) <= (5/4) * Delta(G)^2.
    Definitions: [xe1_strong_chromatic_index G sq] - sq is the least k admitting an
      [xe1_strong_edge_colouring] (this file); [xe1_strong_edge_colouring G k] - k = 0 when G has no
      edge, and otherwise a map from edges to ['I_k] each of whose colour classes is a set of
      [xe1_strongly_independent_edges] (this file); [xe1_strongly_independent_edges F] - the edges
      of F are pairwise disjoint and no vertex of one is adjacent to a vertex of another, i.e. F
      induces a union of vertex-disjoint edges (this file); [xe1_edge_set G] - the edges of G as
      2-element vertex sets (this file); [Delta] (GTBase base/theories/base.v).
    Notes: This row has no site or review page in the corpus, hence the literal "none" above. The
      corpus row is a QUESTION; the Rocq body is its affirmative reading. The rational bound is
      cleared of denominators, so no rounding is involved. The edgeless case is handled explicitly
      inside [xe1_strong_edge_colouring], where k = 0 is required rather than a colouring into an
      empty palette. *)
Definition erdos_149_statement : Prop :=
  forall (G : sgraph) (sq : nat),
    xe1_strong_chromatic_index G sq ->
    4 * sq <= 5 * (Delta G) ^ 2.

(** Corpus row: erdos:628
    Site: none
    Review: none
    English statement: (Erdos Problems #628)
      For every finite simple graph G with chromatic number k that contains no copy of the complete
      graph on k vertices, and all a, b >= 2 with a + b = k + 1, there are two disjoint vertex sets
      A and B such that the subgraph induced on A has chromatic number at least a and the subgraph
      induced on B has chromatic number at least b.
    Definitions: [xe1_subgraph_of 'K_k G] - the complete graph on k vertices embeds into G, so its
      negation is the source's "containing no K_k" (this file); [induced A] (coq-graph-theory
      sgraph.v).
    Notes: This row has no site or review page in the corpus, hence the literal "none" above. The
      corpus row is a QUESTION; the Rocq body is its affirmative reading. The source's "two disjoint
      subgraphs" is encoded by two disjoint vertex sets and their induced subgraphs, which is the
      strongest reading; disjointness is on vertices only, so edges between A and B are allowed, as
      in the source. *)
Definition erdos_628_statement : Prop :=
  forall (G : sgraph) (k a b : nat),
    χ([set: G]) = k ->
    ~ xe1_subgraph_of 'K_k G ->
    2 <= a -> 2 <= b -> a + b = k.+1 ->
    exists A B : {set G},
      [disjoint A & B] /\
      a <= χ([set: induced A]) /\
      b <= χ([set: induced B]).

(** Corpus row: erdos:944
    Site: none
    Review: none
    English statement: (Erdos Problems #944)
      For all k >= 4 and r >= 1 there exists a finite simple graph G with chromatic number k such
      that every vertex is critical, i.e. deleting it lowers the chromatic number below k, while
      every critical set of edges, i.e. every edge set whose deletion lowers the chromatic number
      below k, has more than r elements.
    Definitions: [xe1_vertex_critical G k] - deleting any single vertex leaves chromatic number
      less than k (this file); [xe1_edge_critical_set G F k] - F is a set of edges whose deletion
      leaves chromatic number less than k (this file); [xe1_all_edge_critical_sets_large G r k] -
      every such F has more than r elements (this file); [xe1_delete_edges G F] - G with the edges
      of F removed (this file).
    Notes: This row has no site or review page in the corpus, hence the literal "none" above. The
      corpus row is a QUESTION; the Rocq body is its affirmative reading. "Every critical set of
      edges has size > r" is stated for ALL edge sets whose deletion lowers chi, not only minimal
      ones, which is the same condition. *)
Definition erdos_944_statement : Prop :=
  forall k r : nat, 4 <= k -> 1 <= r ->
    exists G : sgraph,
      χ([set: G]) = k /\
      xe1_vertex_critical G k /\
      xe1_all_edge_critical_sets_large G r k.

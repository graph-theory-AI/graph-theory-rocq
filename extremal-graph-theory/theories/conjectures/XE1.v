(** * Extremal.conjectures.XE1 -- Erdos open clean/bounded rows *)

From GTBase Require Export base.
From Extremal.conjectures Require Import X4.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition xe1_subgraph_of (H G : sgraph) : Prop :=
  exists f : H -> G, injective f /\ forall x y : H, x -- y -> f x -- f y.

Definition xe1_stable_set (G : sgraph) (S : {set G}) : Prop :=
  forall x y : G, x \in S -> y \in S -> x -- y -> False.

Definition xe1_has_independent_set (G : sgraph) (k : nat) : Prop :=
  exists S : {set G}, xe1_stable_set S /\ #|S| = k.

Definition xe1_no_isolated_vertices (G : sgraph) : Prop :=
  forall v : G, 0 < #|N(v)|.

Definition xe1_complement_rel (G : sgraph) : rel G :=
  fun x y => (x != y) && ~~ (x -- y).

Lemma xe1_complement_sym (G : sgraph) : symmetric (@xe1_complement_rel G).
Proof. by move=> x y; rewrite /xe1_complement_rel eq_sym sgP. Qed.

Lemma xe1_complement_irrefl (G : sgraph) : irreflexive (@xe1_complement_rel G).
Proof. by move=> x; rewrite /xe1_complement_rel eqxx. Qed.

Definition xe1_complement_graph (G : sgraph) : sgraph :=
  SGraph (@xe1_complement_sym G) (@xe1_complement_irrefl G).

Definition xe1_graph_ramsey (H K : sgraph) (R : nat) : Prop :=
  forall G : sgraph, #|G| = R ->
    xe1_subgraph_of H G \/ xe1_subgraph_of K (xe1_complement_graph G).

Definition xe1_graph_ramsey_number (H K : sgraph) (R : nat) : Prop :=
  xe1_graph_ramsey H K R /\
  forall R' : nat, xe1_graph_ramsey H K R' -> R <= R'.

Definition xe1_diagonal_ramsey_number (H : sgraph) (R : nat) : Prop :=
  xe1_graph_ramsey_number H H R.

Definition xe1_size_ramsey (H K : sgraph) (m : nat) : Prop :=
  exists G : sgraph,
    x4_edge_count G = m /\
    forall col : rel G, symmetric col ->
      (exists f : H -> G, injective f /\ forall x y : H, x -- y -> f x -- f y /\ col (f x) (f y)) \/
      (exists f : K -> G, injective f /\ forall x y : K, x -- y -> f x -- f y /\ ~~ col (f x) (f y)).

Definition xe1_size_ramsey_number (H K : sgraph) (m : nat) : Prop :=
  xe1_size_ramsey H K m /\
  forall m' : nat, xe1_size_ramsey H K m' -> m <= m'.

Definition xe1_delete_edges_rel (G : sgraph) (F : {set {set G}}) : rel G :=
  fun x y => (x -- y) && ([set x; y] \notin F).

Lemma xe1_delete_edges_sym (G : sgraph) (F : {set {set G}}) :
  symmetric (@xe1_delete_edges_rel G F).
Proof. by move=> x y; rewrite /xe1_delete_edges_rel sgP setUC. Qed.

Lemma xe1_delete_edges_irrefl (G : sgraph) (F : {set {set G}}) :
  irreflexive (@xe1_delete_edges_rel G F).
Proof. by move=> x; rewrite /xe1_delete_edges_rel sg_irrefl. Qed.

Definition xe1_delete_edges (G : sgraph) (F : {set {set G}}) : sgraph :=
  SGraph (@xe1_delete_edges_sym G F) (@xe1_delete_edges_irrefl G F).

Fixpoint xe1_hypercube (d : nat) : sgraph :=
  match d with
  | 0 => 'K_1
  | d'.+1 => cartesian_product 'K_2 (xe1_hypercube d')
  end.

Definition xe1_tree (T : sgraph) : Prop :=
  is_forest [set: T] /\ connected [set: T].

Definition xe1_min_degree_at_least (G : sgraph) (d : nat) : Prop :=
  forall v : G, d <= #|N(v)|.

Definition xe1_every_k_set_sparse (G : sgraph) (k : nat) : Prop :=
  forall S : {set G}, #|S| = k -> x4_edge_count (induced S) <= 2 * k - 3.

Definition xe1_diameter_at_most (G : sgraph) (r : nat) : Prop :=
  forall x y : G, y \in ball r x.

Definition xe1_triangle_free_diameter_completion_edges
    (G : sgraph) (r h : nat) : Prop :=
  exists F : {set {set G}},
    #|F| = h /\
    F \subset [set e : {set G} | #|e| == 2] /\
    triangle_free (@xe1_delete_edges G set0) /\
    xe1_diameter_at_most (@xe1_delete_edges G set0) r.

Definition xe1_c4_forcing_min_degree (n f : nat) : Prop :=
  (forall G : sgraph, #|G| = n -> xe1_min_degree_at_least G f -> xe1_subgraph_of (cycle_graph 4) G) /\
  forall f' : nat,
    (forall G : sgraph, #|G| = n -> xe1_min_degree_at_least G f' -> xe1_subgraph_of (cycle_graph 4) G) ->
    f <= f'.

Definition xe1_sqrt_floor (n s : nat) : Prop :=
  s ^ 2 <= n /\ forall t : nat, t ^ 2 <= n -> t <= s.

Definition xe1_complete_plus_vertex (H : sgraph) (n t : nat) : Prop :=
  exists x : H, exists K : {set H},
    x \notin K /\
    K :|: [set x] = [set: H] /\
    #|K| = n /\
    clique K /\
    #|N(x) :&: K| = t /\
    forall y z : H, y -- z ->
      (y \in K /\ z \in K) \/
      (y = x /\ z \in K /\ z \in N(x)) \/
      (z = x /\ y \in K /\ y \in N(x)).

Definition xe1_h5_graph (G : sgraph) : Prop :=
  exists c : seq G, exists e1 e2 : {set G},
    #|G| = 5 /\
    (forall v : G, v \in c) /\
    ucycle (--) c /\
    size c = 5 /\
    #|e1| = 2 /\ #|e2| = 2 /\
    e1 \in x4_edge_set G /\
    e2 \in x4_edge_set G /\
    [disjoint e1 & e2] /\
    e1 \subset [set v : G | v \in c] /\
    e2 \subset [set v : G | v \in c] /\
    (forall x y : G, [set x; y] = e1 -> ~~ x4_consecutive_in_cycle c x y) /\
    (forall x y : G, [set x; y] = e2 -> ~~ x4_consecutive_in_cycle c x y) /\
    (forall x y : G, x -- y ->
      x4_consecutive_in_cycle c x y \/ [set x; y] = e1 \/ [set x; y] = e2).

Definition xe1_sqrt_ceil (n s : nat) : Prop :=
  n <= s ^ 2 /\ forall t : nat, n <= t ^ 2 -> s <= t.

Definition xe1_colour_k_free_on
    (N k r : nat) (col : {set 'I_N} -> 'I_r)
    (colour : 'I_r) (S : {set 'I_N}) : Prop :=
  forall K : {set 'I_N}, K \subset S -> #|K| = k ->
    exists e : {set 'I_N}, e \subset K /\ #|e| = 2 /\ col e != colour.

Definition xe1_multicolour_missing_clique_ramsey
    (n k r R : nat) : Prop :=
  forall col : {set 'I_R} -> 'I_r,
    exists S : {set 'I_R}, exists colour : 'I_r,
      #|S| = n /\ @xe1_colour_k_free_on R k r col colour S.

Definition xe1_multicolour_missing_clique_ramsey_number
    (n k r R : nat) : Prop :=
  xe1_multicolour_missing_clique_ramsey n k r R /\
  forall R' : nat, xe1_multicolour_missing_clique_ramsey n k r R' -> R <= R'.

Definition xe1_complete_multipartite_with_sizes
    (G : sgraph) (k : nat) (sizes : 'I_k -> nat) : Prop :=
  exists P : 'I_k -> {set G},
    (forall i : 'I_k, #|P i| = sizes i) /\
    (forall i j : 'I_k, i != j -> [disjoint P i & P j]) /\
    (forall v : G, exists i : 'I_k, v \in P i) /\
    forall x y : G,
      x -- y =
        [exists i : 'I_k,
          [exists j : 'I_k,
            (i != j) && (x \in P i) && (y \in P j)]].

Definition xe1_two_smallest_part_sizes
    (k : nat) (sizes : 'I_k -> nat) (m1 m2 : nat) : Prop :=
  exists i j : 'I_k,
    i != j /\
    sizes i = m1 /\
    sizes j = m2 /\
    forall h : 'I_k, m1 <= sizes h /\ (h != i -> m2 <= sizes h).

Definition xe1_monochromatic_copy_in_complete
    (k : nat) (H : sgraph) (R : nat)
    (col : {set 'I_R} -> 'I_k) : Prop :=
  exists colour : 'I_k, exists f : H -> 'I_R,
    injective f /\
    forall x y : H, x -- y -> col [set f x; f y] = colour.

Definition xe1_multicolour_graph_ramsey (k : nat) (H : sgraph) (R : nat) : Prop :=
  forall col : {set 'I_R} -> 'I_k,
    @xe1_monochromatic_copy_in_complete k H R col.

Definition xe1_multicolour_graph_ramsey_number
    (k : nat) (H : sgraph) (R : nat) : Prop :=
  xe1_multicolour_graph_ramsey k H R /\
  forall R' : nat, xe1_multicolour_graph_ramsey k H R' -> R <= R'.

Definition xe1_positive_sequence (s : seq nat) : Prop :=
  forall x : nat, x \in s -> 0 < x.

Definition xe1_nonincreasing_sequence (s : seq nat) : Prop :=
  forall i j : nat, i < j -> j < size s -> nth 0 s j <= nth 0 s i.

Definition xe1_star_on_set (G : sgraph) (S : {set G}) (leaves : nat) : Prop :=
  exists c : G,
    c \in S /\
    #|S| = leaves.+1 /\
    forall x y : G,
      x \in S -> y \in S ->
      x -- y =
        (((x == c) && (y \in S) && (y != c)) ||
         ((y == c) && (x \in S) && (x != c))).

Definition xe1_star_forest_with_leaves (G : sgraph) (leaves : seq nat) : Prop :=
  exists C : 'I_(size leaves) -> {set G},
    (forall i : 'I_(size leaves), xe1_star_on_set (C i) (nth 0 leaves i)) /\
    (forall i j : 'I_(size leaves), i != j -> [disjoint C i & C j]) /\
    (forall v : G, exists i : 'I_(size leaves), v \in C i) /\
    forall x y : G, x -- y ->
      exists i : 'I_(size leaves), x \in C i /\ y \in C i.

Definition xe1_star_formula_term
    (ns ms : seq nat) (q l : nat) : Prop :=
  (exists i j : nat,
      i < size ns /\ j < size ms /\ i.+1 + j.+1 = q /\
      l = nth 0 ns i + nth 0 ms j - 1) /\
  forall i j : nat, i < size ns -> j < size ms -> i.+1 + j.+1 = q ->
    nth 0 ns i + nth 0 ms j - 1 <= l.

Definition xe1_star_forest_formula (ns ms : seq nat) (value : nat) : Prop :=
  exists l : nat -> nat,
    (forall q : nat, 2 <= q -> q <= size ns + size ms ->
      xe1_star_formula_term ns ms q (l q)) /\
    value = \sum_(q <- iota 2 ((size ns + size ms).-1)) l q.

Definition xe1_add_edges_rel (G : sgraph) (F : {set {set G}}) : rel G :=
  fun x y => (x != y) && ((x -- y) || ([set x; y] \in F)).

Lemma xe1_add_edges_sym (G : sgraph) (F : {set {set G}}) :
  symmetric (@xe1_add_edges_rel G F).
Proof. by move=> x y; rewrite /xe1_add_edges_rel eq_sym sgP setUC. Qed.

Lemma xe1_add_edges_irrefl (G : sgraph) (F : {set {set G}}) :
  irreflexive (@xe1_add_edges_rel G F).
Proof. by move=> x; rewrite /xe1_add_edges_rel eqxx. Qed.

Definition xe1_add_edges (G : sgraph) (F : {set {set G}}) : sgraph :=
  SGraph (@xe1_add_edges_sym G F) (@xe1_add_edges_irrefl G F).

Definition xe1_triangle_free_diameter_completion_number
    (G : sgraph) (r h : nat) : Prop :=
  (exists F : {set {set G}},
      #|F| = h /\
      F \subset [set e : {set G} | #|e| == 2] /\
      [disjoint F & x4_edge_set G] /\
      triangle_free (@xe1_add_edges G F) /\
      xe1_diameter_at_most (@xe1_add_edges G F) r) /\
  forall h' : nat,
    (exists F : {set {set G}},
      #|F| = h' /\
      F \subset [set e : {set G} | #|e| == 2] /\
      [disjoint F & x4_edge_set G] /\
      triangle_free (@xe1_add_edges G F) /\
      xe1_diameter_at_most (@xe1_add_edges G F) r) ->
    h <= h'.

Definition xe1_turan_number_for_graph (F : sgraph) (n m : nat) : Prop :=
  (exists G : sgraph, #|G| = n /\ x4_edge_count G = m /\ ~ xe1_subgraph_of F G) /\
  forall m' : nat,
    (exists G : sgraph, #|G| = n /\ x4_edge_count G = m' /\ ~ xe1_subgraph_of F G) ->
    m' <= m.

Definition xe1_min_turan_over_size_edges (k l n a : nat) : Prop :=
  (exists F : sgraph,
      #|F| = k /\ x4_edge_count F = l /\ xe1_turan_number_for_graph F n a) /\
  forall b : nat,
    (exists F : sgraph,
      #|F| = k /\ x4_edge_count F = l /\ xe1_turan_number_for_graph F n b) ->
    a <= b.

Definition xe1_every_7_set_has_triangle (G : sgraph) : Prop :=
  forall S : {set G}, #|S| = 7 ->
    exists T : {set G}, T \subset S /\ x4_triangle_set T.

Definition xe1_seven_triangle_clique_property (n h : nat) : Prop :=
  forall G : sgraph,
    #|G| = n ->
    xe1_every_7_set_has_triangle G ->
    exists K : {set G}, clique K /\ h <= #|K|.

Definition xe1_seven_triangle_clique_guarantee (n h : nat) : Prop :=
  xe1_seven_triangle_clique_property n h /\
  forall h' : nat, xe1_seven_triangle_clique_property n h' -> h' <= h.

Definition xe1_between_rational_power_bounds
    (n h a1 b1 a2 b2 C1 C2 : nat) : Prop :=
  n ^ (b1 + 3 * a1) <= C1 * h ^ (3 * b1) /\
  h ^ (2 * b2) <= C2 * n ^ (b2 - 2 * a2).

(** Corpus row: erdos:1035
    Site: none
    Review: none
    English statement: (Erdos problem #1035)
      There is a positive rational constant c/d (0 < c < d) such that for every n, every
      graph G on exactly 2^n vertices in which every vertex v satisfies
      d * deg(v) > (d - c) * 2^n contains the n-dimensional hypercube Q_n as a subgraph.
    Definitions: [xe1_hypercube n] - the n-dimensional hypercube, built by n iterated Cartesian
      products of 'K_2 with 'K_1 as base (XE1.v); [xe1_subgraph_of H G] - an injective map
      H -> G carrying every edge of H to an edge of G, i.e. H is a (not necessarily induced)
      subgraph of G (XE1.v); [N(v)] - neighbourhood, [cartesian_product] - GTBase.
    Notes: the real constant c of the source is encoded as the rational c/d with naturals
      0 < c < d, so the minimum-degree hypothesis d * deg(v) > (d - c) * 2^n reads
      deg(v) > (1 - c/d) * 2^n; nat subtraction is safe because c < d is assumed. The
      hypothesis is stated vertexwise (every vertex has large degree), which is the minimum
      degree condition. *)
Definition erdos_1035_statement : Prop :=
  exists c d : nat,
    0 < c /\ c < d /\
    forall n : nat, forall G : sgraph,
      #|G| = 2 ^ n ->
      (forall v : G, d * #|N(v)| > (d - c) * 2 ^ n) ->
      xe1_subgraph_of (xe1_hypercube n) G.

(** Corpus row: erdos:128
    Site: none
    Review: none
    English statement: (Erdos problem #128)
      For every n and every graph G on n vertices: if every vertex subset S with
      |S| >= floor(n/2) induces more than n^2/50 edges (written n^2 < 50 * e(G[S])), then G
      contains a triangle.
    Definitions: [x4_edge_count G] - the number of 2-element subsets of vertices that are
      edges of G (X4.v); [x4_triangle_set T] - T is a 3-element set of pairwise adjacent
      vertices (X4.v); [induced S] - the induced subgraph on S (coq-graph-theory).
    Notes: the division by 50 is cleared to keep the statement over nat, and floor(n/2) is
      [n %/ 2]. The conclusion asserts the existence of a triangle vertex set in G itself,
      not in an induced subgraph. *)
Definition erdos_128_statement : Prop :=
  forall (n : nat) (G : sgraph),
    #|G| = n ->
    (forall S : {set G}, n %/ 2 <= #|S| -> n ^ 2 < 50 * x4_edge_count (induced S)) ->
    exists T : {set G}, x4_triangle_set T.

(** Corpus row: erdos:129
    Site: none
    Review: none
    English statement: (Erdos problem #129)
      For every number r >= 1 of colours there is a constant C > 1 such that for all n, if R
      is the least N for which every r-colouring of the edges of the complete graph on N
      vertices admits a set of n vertices missing a copy of K_3 in at least one colour, then
      R < C^s where s is the least integer with n <= s^2, i.e. s = ceil(sqrt n).
    Definitions: [xe1_multicolour_missing_clique_ramsey_number n k r R] - R is minimal such
      that every colouring col of the 2-element subsets of 'I_R by 'I_r leaves some n-set S
      and some colour c with no k-clique of S monochromatic in c, via
      [xe1_colour_k_free_on] (XE1.v); [xe1_sqrt_ceil n s] - n <= s^2 and s is least with that
      property (XE1.v).
    Notes: the source bound is C^{sqrt n}; the Rocq body uses the integer ceiling of sqrt n,
      hence bounds R by C^{ceil(sqrt n)}, which is formally a weaker conclusion than
      C^{sqrt n} (recorded in the ledger). The colouring is a total function on all subsets
      of 'I_R, and [xe1_colour_k_free_on] only constrains the 2-element ones. *)
Definition erdos_129_statement : Prop :=
  forall r : nat, 1 <= r -> exists C : nat,
    1 < C /\
    forall n R : nat,
      xe1_multicolour_missing_clique_ramsey_number n 3 r R ->
      exists s : nat, xe1_sqrt_ceil n s /\ R < C ^ s.

(** Corpus row: erdos:23
    Site: none
    Review: none
    English statement: (Erdos problem #23)
      For every n, every triangle-free graph G on exactly 5n vertices has a set F of at most
      n^2 of its edges whose deletion leaves a bipartite graph.
    Definitions: [x4_edge_set G] - the set of 2-element vertex sets that are edges of G
      (X4.v); [xe1_delete_edges G F] - the graph on the same vertices keeping exactly the
      edges of G whose 2-element vertex set is not in F (XE1.v); [triangle_free],
      [bipartite] - GTBase.
    Notes: the answer to the source question is asserted positively (the source phrases it as
      a question). *)
Definition erdos_23_statement : Prop :=
  forall (n : nat) (G : sgraph),
    #|G| = 5 * n ->
    triangle_free G ->
    exists F : {set {set G}},
      F \subset x4_edge_set G /\
      #|F| <= n ^ 2 /\
      bipartite (@xe1_delete_edges G F).

(** Corpus row: erdos:545
    Site: none
    Review: none
    English statement: (Erdos problem #545)
      For all m, n, t: if G has m edges and no isolated vertex, m = binomial(n,2) + t with
      t < n, and H is obtained from the complete graph on n vertices by adding one new vertex
      joined to exactly t of them, then the diagonal Ramsey number of G is at most that of H.
    Definitions: [xe1_graph_ramsey_number G G R] - R is the least N such that in every graph
      on N vertices, G embeds either in the graph or in its complement, where an embedding is
      [xe1_subgraph_of] (an injective edge-preserving map) and the complement is
      [xe1_complement_graph] (XE1.v); [xe1_no_isolated_vertices G] - every vertex has degree
      at least 1 (XE1.v); [xe1_complete_plus_vertex H n t] - H consists of an n-clique K plus
      one extra vertex x adjacent to exactly t vertices of K and to nothing else (XE1.v);
      [x4_edge_count] - number of edges (X4.v).
    Notes: R(G) is read as the diagonal Ramsey number R(G,G), as in the source. The two
      Ramsey numbers are passed as parameters constrained by the minimality predicate rather
      than computed, so the statement is vacuous for a pair (G,H) whose Ramsey numbers do not
      exist in this sense. *)
Definition erdos_545_statement : Prop :=
  forall (m n t RG RH : nat) (G H : sgraph),
    x4_edge_count G = m -> xe1_no_isolated_vertices G ->
    m = 'C(n, 2) + t -> t < n ->
    xe1_complete_plus_vertex H n t ->
    xe1_graph_ramsey_number G G RG ->
    xe1_graph_ramsey_number H H RH ->
    RG <= RH.

(** Corpus row: erdos:548
    Site: none
    Review: none
    English statement: (Erdos problem #548)
      For all n >= k+1, every graph G on n vertices with at least ((k-1)/2) * n + 1 edges
      (written 2 * e(G) >= (k-1) * n + 2) contains every tree T on k+1 vertices as a
      subgraph.
    Definitions: [xe1_tree T] - the whole vertex set of T is a forest and is connected
      (XE1.v, on coq-graph-theory's [is_forest] and [connected]); [xe1_subgraph_of T G] -
      injective edge-preserving map T -> G (XE1.v); [x4_edge_count] - number of edges (X4.v).
    Notes: the edge bound is doubled to stay in nat. [k - 1] is nat subtraction, so for k = 0
      the hypothesis degenerates to 2 * e(G) >= 2; the intended range k >= 1 is implied by
      k+1 <= n together with the tree having k+1 vertices. *)
Definition erdos_548_statement : Prop :=
  forall (n k : nat) (G T : sgraph),
    k.+1 <= n ->
    #|G| = n -> #|T| = k.+1 -> xe1_tree T ->
    2 * x4_edge_count G >= (k - 1) * n + 2 ->
    xe1_subgraph_of T G.

(** Corpus row: erdos:550
    Site: none
    Review: none
    English statement: (Erdos problem #550)
      Let k >= 2 and let sizes be positive part sizes with two smallest values m1 <= m2. Then
      there is N such that for every n >= N, every tree T on n vertices and every complete
      multipartite graph G with those part sizes, the Ramsey number R(T,G) is at most
      (chi(G) - 1) * (R(T, K_{m1,m2}) - 1) + m1.
    Definitions: [xe1_two_smallest_part_sizes sizes m1 m2] - two distinct part indices realise
      m1 and m2, m1 bounds every size from below and m2 bounds every size other than the
      m1-index from below (XE1.v); [xe1_complete_multipartite_with_sizes G k sizes] - the
      vertices of G split into k classes of the given sizes with adjacency exactly across
      classes (XE1.v); [xe1_tree] - connected forest (XE1.v); [xe1_graph_ramsey_number H K R]
      - the least N forcing H in the graph or K in the complement (XE1.v); [KB m1 m2] -
      complete bipartite graph (GTBase); [chi] - chromatic number (coq-graph-theory).
    Notes: both subtractions are nat subtractions, harmless because chi(G) >= 1 and the
      Ramsey number is at least 1 in the intended range. "n sufficiently large" is encoded as
      an existential N depending only on k and the part sizes. *)
Definition erdos_550_statement : Prop :=
  forall (k : nat) (sizes : 'I_k -> nat) (m1 m2 : nat),
    2 <= k ->
    (forall i : 'I_k, 0 < sizes i) ->
    xe1_two_smallest_part_sizes sizes m1 m2 ->
    exists N : nat,
    forall (n RTB RTG : nat) (T G : sgraph),
      N <= n -> xe1_tree T -> #|T| = n ->
      xe1_complete_multipartite_with_sizes G sizes ->
      xe1_graph_ramsey_number T (KB m1 m2) RTB ->
      xe1_graph_ramsey_number T G RTG ->
      RTG <= (χ([set: G]) - 1) * (RTB - 1) + m1.

(** Corpus row: erdos:552
    Site: none
    Review: none
    English statement: (Erdos problem #552)
      For every constant c and every bound M there is n >= M such that the Ramsey number
      R(C_4, K_{1,n}) satisfies R + c <= n + floor(sqrt n); that is, for every c there are
      infinitely many n with R(C_4, S_n) <= n + sqrt(n) - c.
    Definitions: [xe1_sqrt_floor n s] - s^2 <= n and s is largest with that property (XE1.v);
      [xe1_graph_ramsey_number H K R] - the least N forcing H in the graph or K in the
      complement (XE1.v); [cycle_graph 4], [KB 1 n] (the star S_n = K_{1,n}) - GTBase.
    Notes: only the second half of the source problem is formalised; the first half
      ("determine R(C_4,S_n)") has no Prop form. The subtraction of c is moved to the left
      side to stay in nat, and floor(sqrt n) replaces sqrt(n), so the encoded bound is
      slightly stronger than the source for non-square n. *)
Definition erdos_552_statement : Prop :=
  forall c M : nat, exists n R s : nat,
    M <= n /\
    xe1_sqrt_floor n s /\
    xe1_graph_ramsey_number (cycle_graph 4) (KB 1 n) R /\
    R + c <= n + s.

(** Corpus row: erdos:557
    Site: none
    Review: none
    English statement: (Erdos problem #557)
      For every number k >= 1 of colours there is a constant C such that for every tree T on
      n vertices, the k-colour Ramsey number R_k(T) - the least N such that every k-colouring
      of the edges of the complete graph on N vertices contains a monochromatic copy of T -
      is at most k * n + C.
    Definitions: [xe1_multicolour_graph_ramsey_number k H R] - R is least such that every
      colouring of the 2-element subsets of 'I_R by 'I_k admits a colour and an injective map
      H -> 'I_R sending every edge of H to a pair of that colour
      ([xe1_monochromatic_copy_in_complete], XE1.v); [xe1_tree] - connected forest (XE1.v).
    Notes: the O(1) of the source is encoded as a constant C depending only on k, uniform in
      the tree and in n, which is the intended reading. *)
Definition erdos_557_statement : Prop :=
  forall k : nat, 1 <= k -> exists C : nat,
    forall (n R : nat) (T : sgraph),
      xe1_tree T -> #|T| = n ->
      xe1_multicolour_graph_ramsey_number k T R ->
      R <= k * n + C.

(** Corpus row: erdos:561
    Site: none
    Review: none
    English statement: (Erdos problem #561)
      Let ns and ms be non-empty, positive, non-increasing sequences and let F1, F2 be the
      disjoint unions of stars with those numbers of leaves. Then the size Ramsey number
      Rhat(F1,F2) equals the sum over q = 2..|ns|+|ms| of l_q, where
      l_q = max { ns_i + ms_j - 1 : (i+1) + (j+1) = q }.
    Definitions: [xe1_size_ramsey_number F1 F2 m] - m is the least number of edges of a graph
      G such that every symmetric 2-colouring of the adjacency of G yields a copy of F1 on
      edges of the first colour or a copy of F2 on edges of the second (XE1.v);
      [xe1_star_forest_with_leaves G leaves] - the vertices of G partition into star centres
      and leaves realising the given leaf counts, with no edges between stars (XE1.v);
      [xe1_star_forest_formula ns ms value] - value is the sum of the terms
      [xe1_star_formula_term] (XE1.v); [xe1_positive_sequence],
      [xe1_nonincreasing_sequence] - pointwise positivity and monotonicity of a [seq nat]
      (XE1.v).
    Notes: indices are 0-based in the Rocq body and shifted by one in the formula term
      ([i.+1 + j.+1 = q]) to match the source's 1-based indexing. The subtraction
      [ns_i + ms_j - 1] is nat subtraction, harmless since the sequences are positive. *)
Definition erdos_561_statement : Prop :=
  forall (ns ms : seq nat) (F1 F2 : sgraph) (m formula : nat),
    0 < size ns -> 0 < size ms ->
    xe1_positive_sequence ns -> xe1_positive_sequence ms ->
    xe1_nonincreasing_sequence ns -> xe1_nonincreasing_sequence ms ->
    xe1_star_forest_with_leaves F1 ns ->
    xe1_star_forest_with_leaves F2 ms ->
    xe1_star_forest_formula ns ms formula ->
    xe1_size_ramsey_number F1 F2 m ->
    m = formula.

(** Corpus row: erdos:566
    Site: none
    Review: none
    English statement: (Erdos problem #566)
      If G is a graph in which every set of k vertices induces at most 2k - 3 edges (for
      every k), then there is a constant C such that every graph H with m edges and no
      isolated vertex satisfies R(G,H) <= C * m.
    Definitions: [xe1_every_k_set_sparse G k] - every k-element vertex set induces at most
      2k - 3 edges (XE1.v); [xe1_graph_ramsey_number G H R] - the least N forcing G in the
      graph or H in the complement (XE1.v); [xe1_no_isolated_vertices] - every vertex has a
      neighbour (XE1.v); [x4_edge_count] - number of edges (X4.v).
    Notes: C is quantified after G, so it may depend on G, matching the source's implicit
      constant. [2 * k - 3] is nat subtraction, so for k <= 1 the hypothesis says the induced
      subgraph has no edge, which is automatic. *)
Definition erdos_566_statement : Prop :=
  forall G : sgraph,
    (forall k : nat, xe1_every_k_set_sparse G k) ->
    exists C : nat,
      forall (H : sgraph) (m R : nat),
        x4_edge_count H = m -> xe1_no_isolated_vertices H ->
        xe1_graph_ramsey_number G H R ->
        R <= C * m.

(** Corpus row: erdos:567
    Site: none
    Review: none
    English statement: (Erdos problem #567)
      If G is the 3-dimensional hypercube Q_3, or K_{3,3}, or H_5 (the 5-cycle plus two
      vertex-disjoint chords), then there is a constant C such that every graph H with m
      edges and no isolated vertex satisfies R(G,H) <= C * m.
    Definitions: [xe1_hypercube 3] - Q_3 as iterated Cartesian product (XE1.v); [KB 3 3] -
      K_{3,3} (GTBase); [xe1_h5_graph G] - G has 5 vertices carrying a spanning cycle plus
      exactly two disjoint non-cycle edges (XE1.v); [xe1_graph_ramsey_number],
      [xe1_no_isolated_vertices] (XE1.v); [x4_edge_count] (X4.v).
    Notes: Q_3 and K_{3,3} are pinned by Rocq equality of the sgraph structure, whereas H_5
      is characterised up to isomorphism; the mixture is harmless here because the conclusion
      is isomorphism-invariant, but it is inconsistent vocabulary (ledger). *)
Definition erdos_567_statement : Prop :=
  forall G : sgraph,
    (G = xe1_hypercube 3 \/ G = KB 3 3 \/ xe1_h5_graph G) ->
    exists C : nat,
      forall (H : sgraph) (m R : nat),
        x4_edge_count H = m -> xe1_no_isolated_vertices H ->
        xe1_graph_ramsey_number G H R ->
        R <= C * m.

(** Corpus row: erdos:568
    Site: none
    Review: none
    English statement: (Erdos problem #568)
      If G is a graph such that R(G,T) <= C1 * n for every tree T on n vertices and
      R(G,K_n) <= C2 * n^2 for every n, then there is a constant C such that every graph H
      with m edges and no isolated vertex satisfies R(G,H) <= C * m.
    Definitions: [xe1_graph_ramsey_number G H R] - the least N forcing G in the graph or H in
      the complement (XE1.v); [xe1_tree] - connected forest (XE1.v);
      [xe1_no_isolated_vertices] (XE1.v); ['K_n] - complete graph (coq-graph-theory);
      [x4_edge_count] (X4.v).
    Notes: the two "much less than" hypotheses of the source are encoded as explicit linear
      and quadratic bounds with existentially quantified constants C1, C2. *)
Definition erdos_568_statement : Prop :=
  forall G : sgraph,
    (exists C1 : nat, forall (n R : nat) (T : sgraph),
      xe1_tree T -> #|T| = n -> xe1_graph_ramsey_number G T R -> R <= C1 * n) ->
    (exists C2 : nat, forall (n R : nat),
      xe1_graph_ramsey_number G 'K_n R -> R <= C2 * n ^ 2) ->
    exists C : nat, forall (H : sgraph) (m R : nat),
      x4_edge_count H = m -> xe1_no_isolated_vertices H ->
      xe1_graph_ramsey_number G H R ->
      R <= C * m.

(** Corpus row: erdos:619
    Site: none
    Review: none
    English statement: (Erdos problem #619)
      There is a positive rational constant c/d (0 < c < d) such that for every connected
      triangle-free graph G on n vertices, the least number h of edges that must be added to
      G to make it have diameter at most 4 while staying triangle-free satisfies
      d * h < (d - c) * n, i.e. h < (1 - c/d) * n.
    Definitions: [xe1_triangle_free_diameter_completion_number G r h] - h is the least size
      of a set F of non-edges of G such that adding F ([xe1_add_edges]) keeps the graph
      triangle-free and makes every vertex reachable within r steps
      ([xe1_diameter_at_most], via [ball]) (XE1.v); [triangle_free], [connected] - GTBase /
      coq-graph-theory; [x4_edge_set] - the edges as 2-element sets (X4.v).
    Notes: the real constant c is encoded as the rational c/d over nat with 0 < c < d. The
      source restricts h_r to triangle-free G; the Rocq body carries [triangle_free G] as an
      explicit hypothesis, and the completion predicate itself requires the completed graph to
      remain triangle-free. *)
Definition erdos_619_statement : Prop :=
  exists c d : nat,
    0 < c /\ c < d /\
    forall (G : sgraph) (n h : nat),
      connected [set: G] -> #|G| = n -> triangle_free G ->
      xe1_triangle_free_diameter_completion_number G 4 h ->
      d * h < (d - c) * n.

(** Corpus row: erdos:766
    Site: none
    Review: none
    English statement: (Erdos problem #766)
      For all k < l with 4(l+1) <= k^2, there is N such that for every n >= N the quantity
      f(n;k,l) = min { ex(n;F) : F has k vertices and l edges } is strictly increasing in l,
      i.e. f(n;k,l) < f(n;k,l+1).
    Definitions: [xe1_turan_number_for_graph F n m] - m is the maximum number of edges of an
      F-free graph on n vertices, F-freeness being the negation of [xe1_subgraph_of] (XE1.v);
      [xe1_min_turan_over_size_edges k l n a] - a is the minimum of that Turan number over
      all graphs F with k vertices and l edges (XE1.v); [x4_edge_count] - number of edges
      (X4.v).
    Notes: the source's range k < l <= k^2/4 is encoded as k < l together with
      4 * (l+1) <= k^2, which is the condition needed for both l and l+1 to lie in the range.
      Only the second (monotonicity) question of the source is formalised; "give good
      estimates" has no Prop form. *)
Definition erdos_766_statement : Prop :=
  forall k l : nat, k < l -> 4 * l.+1 <= k ^ 2 ->
    exists N : nat,
      forall n a b : nat,
        N <= n ->
        xe1_min_turan_over_size_edges k l n a ->
        xe1_min_turan_over_size_edges k l.+1 n b ->
        a < b.

(** Corpus row: erdos:802
    Site: none
    Review: none
    English statement: (Erdos problem #802)
      For every r there is a constant C > 0 such that every K_r-free graph G on n vertices
      whose degree sum is at most t * n (average degree at most t) has an independent set A
      with C * t * |A| >= n * floor(log_2 t), i.e. |A| >= (log t / t) * n / C.
    Definitions: [xe1_subgraph_of 'K_r G] - K_r embeds in G, so its negation is K_r-freeness
      (XE1.v); [xe1_stable_set A] - no two vertices of A are adjacent (XE1.v);
      [trunc_log 2 t] - MathComp floor of log base 2.
    Notes: the hypothesis is average degree AT MOST t, written as the degree-sum bound
      [\sum_v #|N(v)| <= t * #|G|]; encoding it as a LOWER bound on the average degree would
      be wrong, since log t / t is decreasing and a graph of much larger degree would make
      the target unattainable. The logarithm is [trunc_log 2] (floor-log2, as in D2pr.v);
      [logn 2] is the 2-adic valuation, a different object that vanishes on odd t. The
      implicit constant of the source is inverted into the multiplier C on the left. *)
Definition erdos_802_statement : Prop :=
  forall r : nat, exists C : nat,
    0 < C /\
    forall (G : sgraph) (n t : nat),
      ~ xe1_subgraph_of 'K_r G ->
      #|G| = n ->
      \sum_(v in G) #|N(v)| <= t * #|G| ->
      exists A : {set G},
        xe1_stable_set A /\ C * t * #|A| >= n * trunc_log 2 t.

(** Corpus row: erdos:812
    Site: none
    Review: none
    English statement: (Erdos problem #812)
      Both of the following hold for the diagonal Ramsey numbers R(n) = R(K_n,K_n): there are
      positive naturals cnum, cden and a threshold N with cden * R(n+1) >= (cden + cnum) * R(n)
      for all n >= N (that is, R(n+1)/R(n) >= 1 + cnum/cden); and there are positive naturals
      Cnum, Cden and a threshold N with Cden * R(n) + Cnum * n^2 <= Cden * R(n+1) for all
      n >= N (that is, R(n+1) - R(n) >= (Cnum/Cden) * n^2).
    Definitions: [xe1_graph_ramsey_number 'K_n 'K_n R] - R is the least N such that every
      graph on N vertices contains K_n or its complement does (XE1.v).
    Notes: the source asks the two questions separately; the Rocq body asserts their
      conjunction, which is therefore at least as strong as either. Real constants are
      encoded as ratios of positive naturals. *)
Definition erdos_812_statement : Prop :=
  (exists cnum cden N : nat, 0 < cnum /\ 0 < cden /\
    forall n Rn Rn1 : nat,
      N <= n ->
      xe1_graph_ramsey_number 'K_n 'K_n Rn ->
      xe1_graph_ramsey_number 'K_n.+1 'K_n.+1 Rn1 ->
      cden * Rn1 >= (cden + cnum) * Rn) /\
  (exists Cnum Cden N : nat, 0 < Cnum /\ 0 < Cden /\
    forall n Rn Rn1 : nat,
      N <= n ->
      xe1_graph_ramsey_number 'K_n 'K_n Rn ->
      xe1_graph_ramsey_number 'K_n.+1 'K_n.+1 Rn1 ->
      Cden * Rn + Cnum * n ^ 2 <= Cden * Rn1).

(** Corpus row: erdos:813
    Site: none
    Review: none
    English statement: (Erdos problem #813)
      There are positive rationals c1 = a1/b1 and c2 = a2/b2 with 2*a2 < b2, constants
      C1, C2 > 0 and a threshold N such that for all n >= N, the largest h with the property
      that every graph on n vertices in which every 7 vertices contain a triangle has a
      clique of size at least h satisfies n^(b1+3*a1) <= C1 * h^(3*b1) and
      h^(2*b2) <= C2 * n^(b2-2*a2); equivalently n^{1/3+c1} << h << n^{1/2-c2}.
    Definitions: [xe1_every_7_set_has_triangle G] - every 7-element vertex set contains a
      triangle ([x4_triangle_set], X4.v) (XE1.v);
      [xe1_seven_triangle_clique_guarantee n h] - h is the largest value for which every such
      graph on n vertices has a clique of size at least h (XE1.v);
      [xe1_between_rational_power_bounds] - the two power inequalities above (XE1.v);
      [clique] - coq-graph-theory.
    Notes: real exponents are encoded as ratios a/b of positive naturals and the inequalities
      are raised to a common integral power to stay in nat; 2*a2 < b2 keeps the exponent
      b2 - 2*a2 positive, so the nat subtraction is safe. *)
Definition erdos_813_statement : Prop :=
  exists a1 b1 a2 b2 C1 C2 N : nat,
    0 < a1 /\ 0 < b1 /\ 0 < a2 /\ 0 < b2 /\
    0 < C1 /\ 0 < C2 /\ 2 * a2 < b2 /\
    forall (n h : nat),
      N <= n ->
      xe1_seven_triangle_clique_guarantee n h ->
      xe1_between_rational_power_bounds n h a1 b1 a2 b2 C1 C2.

(** Corpus row: erdos:85
    Site: none
    Review: none
    English statement: (Erdos problem #85)
      There is a threshold N such that for all n >= max(N,4), if f(n) is the least minimum
      degree forcing a C_4 in every graph on n vertices, then f(n) <= f(n+1).
    Definitions: [xe1_c4_forcing_min_degree n f] - f is least such that every graph on n
      vertices with all degrees at least f contains a 4-cycle as a subgraph (XE1.v);
      [xe1_min_degree_at_least] (XE1.v); [xe1_subgraph_of] - injective edge-preserving map
      (XE1.v); [cycle_graph 4] - GTBase.
    Notes: "for all large n" is an existential threshold N, and the source's standing
      hypothesis n >= 4 is kept as a separate assumption. *)
Definition erdos_85_statement : Prop :=
  exists N : nat,
    forall n fn fn1 : nat,
      N <= n -> 4 <= n ->
      xe1_c4_forcing_min_degree n fn ->
      xe1_c4_forcing_min_degree n.+1 fn1 ->
      fn <= fn1.

(** Corpus row: erdos:87
    Site: none
    Review: none
    English statement: (Erdos problem #87)
      There are positive naturals cnum, cden and a threshold N such that for every k >= N and
      every graph G with chromatic number exactly k, the diagonal Ramsey number R(G) and the
      usual Ramsey number R(k) = R(K_k,K_k) satisfy cden * R(G) >= cnum * R(k), i.e.
      R(G) >= (cnum/cden) * R(k).
    Definitions: [xe1_diagonal_ramsey_number G R] - [xe1_graph_ramsey_number G G R], the
      least N forcing G in the graph or in its complement (XE1.v); [chi] - chromatic number
      of the whole vertex set (coq-graph-theory).
    Notes: the source asks two questions; the Rocq body formalises only the second, stronger
      one (a uniform constant c with R(G) > c R(k)), and states it with >= rather than >.
      That is deliberate - the stronger form implies the (1-eps)^k form - but it is a
      divergence from the literal source text (ledger). *)
Definition erdos_87_statement : Prop :=
  exists cnum cden N : nat,
    0 < cnum /\ 0 < cden /\
    forall (k RG RK : nat) (G : sgraph),
      N <= k ->
      χ([set: G]) = k ->
      xe1_diagonal_ramsey_number G RG ->
      xe1_graph_ramsey_number 'K_k 'K_k RK ->
      cden * RG >= cnum * RK.

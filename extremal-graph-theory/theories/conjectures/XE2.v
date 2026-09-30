(** * Extremal.conjectures.XE2 -- Erdos solved clean/bounded rows *)

From GTBase Require Export base.
From Extremal.conjectures Require Import X4 XE1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition xe2_tri_edges (G : sgraph) (T : {set G}) : {set {set G}} :=
  [set e : {set G} | (e \subset T) && (#|e| == 2)].

Definition xe2_edge_disjoint_triangles (G : sgraph) (ts : seq {set G}) : Prop :=
  uniq ts /\
  (forall T : {set G}, T \in ts -> x4_triangle_set T) /\
  forall T U : {set G}, T \in ts -> U \in ts -> T != U ->
    [disjoint xe2_tri_edges T & xe2_tri_edges U].

Definition xe2_superlinear_edge_threshold
    (eps_num eps_den n m : nat) : Prop :=
  n ^ (eps_den + eps_num) <= m ^ eps_den.

Definition xe2_saturated_planar (G : sgraph) : Prop :=
  3 < #|G| /\ wagner_planar G /\ x4_edge_count G = 3 * #|G| - 6.

Definition xe2_paths_cover_vertices (G : sgraph) (m : nat) (P : 'I_m -> seq G) : Prop :=
  forall v : G, exists i : 'I_m, v \in P i.

Definition xe2_path_in_graph (G : sgraph) (p : seq G) : Prop :=
  if p is x :: q then path (--) x q else true.

Definition xe2_monochromatic_path
    (G : sgraph) (col : rel G) (b : bool) (p : seq G) : Prop :=
  if p is x :: q then
    uniq (x :: q) /\
    path (--) x q /\
    forall e : G * G, e \in zip p (behead p) -> col e.1 e.2 = b
  else false.

Definition xe2_induced_ramsey_number (H : sgraph) (m : nat) : Prop :=
  (exists G : sgraph,
      #|G| = m /\
      forall col : rel G, symmetric col ->
        exists (b : bool) (f : H -> G),
          injective f /\
          (forall x y : H, x -- y -> f x -- f y /\ col (f x) (f y) = b) /\
          forall x y : H, x != y -> ~~ (x -- y) -> ~~ (f x -- f y)) /\
  forall m' : nat,
    (exists G : sgraph,
      #|G| = m' /\
      forall col : rel G, symmetric col ->
        exists (b : bool) (f : H -> G),
          injective f /\
          (forall x y : H, x -- y -> f x -- f y /\ col (f x) (f y) = b) /\
          forall x y : H, x != y -> ~~ (x -- y) -> ~~ (f x -- f y)) -> m <= m'.

Definition xe2_bipartite_plus_bounded_degree (G : sgraph) (d : nat) : Prop :=
  exists F : {set {set G}},
    F \subset x4_edge_set G /\
    bipartite (@xe1_delete_edges G F) /\
    forall v : G, #|[set e in F | v \in e]| < d.

Definition xe2_diameter_critical_two (G : sgraph) : Prop :=
  xe1_diameter_at_most G 2 /\
  ~ xe1_diameter_at_most G 1 /\
  forall e : {set G}, e \in x4_edge_set G ->
    ~ xe1_diameter_at_most (@xe1_delete_edges G [set e]) 2.

Definition xe2_path_length3 (G : sgraph) (x y : G) : Prop :=
  exists a b : G, uniq [:: x; a; b; y] /\ x -- a /\ a -- b /\ b -- y.

Definition xe2_bipartition_sizes (G : sgraph) (a b : nat) : Prop :=
  exists A B : {set G},
    [disjoint A & B] /\
    A :|: B = [set: G] /\
    #|A| = a /\
    #|B| = b /\
    forall x y : G, x -- y ->
      (x \in A /\ y \in B) \/ (x \in B /\ y \in A).

Definition xe2_cube_square_floor (n a : nat) : Prop :=
  a ^ 3 <= n ^ 2 /\ forall b : nat, b ^ 3 <= n ^ 2 -> b <= a.

Definition xe2_min_degree (G : sgraph) (d : nat) : Prop :=
  (exists v : G, #|N(v)| = d) /\
  forall v : G, d <= #|N(v)|.

Definition xe2_cycle (G : sgraph) (c : seq G) : Prop :=
  ucycle (--) c /\ 2 < size c.

Definition xe2_cycle_diagonal_count (G : sgraph) (c : seq G) : nat :=
  #|[set p : G * G |
      [&& p.1 \in c, p.2 \in c, (enum_rank p.1 < enum_rank p.2)%N,
          p.1 -- p.2 & ~~ x4_consecutive_in_cycle c p.1 p.2]]|.

Definition xe2_incident_cycle_chord_count (G : sgraph) (c : seq G) (v : G) : nat :=
  #|[set u : G |
      [&& u \in c, v \in c, u != v, v -- u
        & ~~ x4_consecutive_in_cycle c v u]]|.

Definition xe2_no_cycle_with_incident_chords (G : sgraph) (k : nat) : Prop :=
  forall c : seq G, xe2_cycle c ->
    forall v : G, v \in c -> xe2_incident_cycle_chord_count c v < k.

Definition xe2_incident_chord_extremal (k n m : nat) : Prop :=
  (exists G : sgraph,
      #|G| = n /\ x4_edge_count G = m /\
      xe2_no_cycle_with_incident_chords G k) /\
  forall m' : nat,
    (exists G : sgraph,
      #|G| = n /\ x4_edge_count G = m' /\
      xe2_no_cycle_with_incident_chords G k) ->
    m' <= m.

Definition xe2_internal_path_vertices (G : sgraph) (x y : G) (p : seq G) : {set G} :=
  [set v : G | [&& v \in p, v != x & v != y]].

Definition xe2_paths_internally_disjoint
    (G : sgraph) (m : nat) (x y : G) (P : 'I_m -> seq G) : Prop :=
  forall i j : 'I_m, i != j ->
    [disjoint xe2_internal_path_vertices x y (P i)
            & xe2_internal_path_vertices x y (P j)].

Definition xe2_path_edge_set (G : sgraph) (p : seq G) : {set {set G}} :=
  [set e : {set G} |
      [exists xy : G * G, (xy \in zip p (behead p)) && (e == [set xy.1; xy.2])]].

Definition xe2_paths_edge_disjoint
    (G : sgraph) (m : nat) (P : 'I_m -> seq G) : Prop :=
  forall i j : 'I_m, i != j ->
    [disjoint xe2_path_edge_set (P i) & xe2_path_edge_set (P j)].

(** Corpus row: erdos:1009
    Site: none
    Review: none
    English statement: (Erdos problem #1009)
      For every positive rational c = cnum/cden there is a natural number f such that every
      graph G on n vertices with at least floor(n^2/4) + k edges, where cden * k < cnum * n
      (i.e. k < c * n), contains a list of pairwise edge-disjoint triangles of length at
      least k - f.
    Definitions: [xe2_edge_disjoint_triangles ts] - ts is a duplicate-free list of triangle
      vertex sets ([x4_triangle_set], X4.v) whose edge sets ([xe2_tri_edges]) are pairwise
      disjoint (XE2.v); [x4_edge_count] - number of edges (X4.v).
    Notes: the real constant c is a ratio of positive naturals, and the conclusion
      k - f(c) <= |ts| is written k <= |ts| + f to avoid nat subtraction. f depends only on
      c, as in the source. *)
Definition erdos_1009_statement : Prop :=
  forall cnum cden : nat, 0 < cnum -> 0 < cden -> exists f : nat,
    forall (n k : nat) (G : sgraph),
      #|G| = n ->
      x4_edge_count G >= (n ^ 2) %/ 4 + k ->
      cden * k < cnum * n ->
      exists ts : seq {set G},
        xe2_edge_disjoint_triangles ts /\ k <= size ts + f.

(** Corpus row: erdos:1018
    Site: none
    Review: none
    English statement: (Erdos problem #1018)
      For every positive rational eps = eps_num/eps_den there are constants C and N such that
      every graph G on n >= N vertices with at least n^(1+eps) edges contains a non-planar
      subgraph on at most C vertices.
    Definitions: [xe2_superlinear_edge_threshold eps_num eps_den n m] - the inequality
      n^(eps_den + eps_num) <= m^eps_den, i.e. n^(1+eps) <= m, raised to an integral power to
      stay in nat (XE2.v); [xe1_subgraph_of H G] - injective edge-preserving map H -> G
      (XE1.v); [wagner_planar] - planarity in Wagner's form, no K_5 and no K_{3,3} minor
      (GTBase); [x4_edge_count] (X4.v).
    Notes: the witness H is an abstract graph embedded in G rather than a vertex subset of G,
      so "subgraph" is the not-necessarily-induced notion; a non-planar subgraph of G on at
      most C vertices is what the source asks for. *)
Definition erdos_1018_statement : Prop :=
  forall eps_num eps_den : nat,
    0 < eps_num -> 0 < eps_den ->
    exists C N : nat,
      forall (n : nat) (G : sgraph),
        N <= n -> #|G| = n ->
        xe2_superlinear_edge_threshold eps_num eps_den n (x4_edge_count G) ->
        exists H : sgraph,
          xe1_subgraph_of H G /\ #|H| <= C /\ ~ wagner_planar H.

(** Corpus row: erdos:1019
    Site: none
    Review: none
    English statement: (Erdos problem #1019)
      Every graph G on n vertices with exactly floor(n^2/4) + floor((n+1)/2) edges contains a
      saturated planar subgraph on more than 3 vertices, where saturated means planar with
      the maximum possible 3 * |V| - 6 edges.
    Definitions: [xe2_saturated_planar H] - H has more than 3 vertices, is Wagner-planar and
      has exactly 3 * |V(H)| - 6 edges (XE2.v); [xe1_subgraph_of] - injective edge-preserving
      map (XE1.v); [wagner_planar] - GTBase; [x4_edge_count] (X4.v).
    Notes: the edge count is an exact equality, as in the source. The subtraction in
      3 * |V(H)| - 6 is nat subtraction, harmless because |V(H)| > 3 is required first. *)
Definition erdos_1019_statement : Prop :=
  forall (n : nat) (G : sgraph),
    #|G| = n ->
    x4_edge_count G = (n ^ 2) %/ 4 + (n.+1 %/ 2) ->
    exists H : sgraph, xe1_subgraph_of H G /\ xe2_saturated_planar H.

(** Corpus row: erdos:1080
    Site: none
    Review: none
    English statement: (Erdos problem #1080)
      There is a positive rational constant c = cnum/cden such that every bipartite graph G
      on n vertices one of whose two classes has exactly floor(n^(2/3)) vertices and which
      has at least c * n edges contains a 6-cycle as a subgraph.
    Definitions: [xe2_cube_square_floor n a] - a^3 <= n^2 and a is largest with that
      property, i.e. a = floor(n^(2/3)) (XE2.v); [xe2_bipartition_sizes G a b] - the vertices
      of G split into two disjoint sets of sizes a and b covering V(G) with every edge
      crossing between them (XE2.v); [xe1_subgraph_of] (XE1.v); [cycle_graph 6] - GTBase;
      [x4_edge_count] (X4.v).
    Notes: bipartiteness is not assumed separately - it follows from
      [xe2_bipartition_sizes], which also fixes the size of the small class. *)
Definition erdos_1080_statement : Prop :=
  exists cnum cden : nat,
    0 < cnum /\ 0 < cden /\
    forall (n : nat) (G : sgraph),
      #|G| = n ->
      (exists a b : nat, xe2_cube_square_floor n a /\ xe2_bipartition_sizes G a b) ->
      cden * x4_edge_count G >= cnum * n ->
      xe1_subgraph_of (cycle_graph 6) G.

(** Corpus row: erdos:22
    Site: none
    Review: none
    English statement: (Erdos problem #22)
      For every positive rational eps = eps_num/eps_den there is N such that for every n >= N
      there is a graph G on n vertices with at least n^2/8 edges (written 8 * e(G) >= n^2)
      that contains no K_4 and in which every independent set A satisfies |A| <= eps * n.
    Definitions: [xe1_subgraph_of 'K_4 G] - K_4 embeds in G, so its negation is K_4-freeness
      (XE1.v); [xe1_stable_set A] - no two vertices of A are adjacent (XE1.v);
      [x4_edge_count] (X4.v).
    Notes: eps is a ratio of positive naturals and the bound on independent sets is cleared
      of denominators as eps_den * |A| <= eps_num * n. *)
Definition erdos_22_statement : Prop :=
  forall eps_num eps_den : nat,
    0 < eps_num -> 0 < eps_den ->
    exists N : nat,
      forall n : nat, N <= n ->
        exists G : sgraph,
          #|G| = n /\
          8 * x4_edge_count G >= n ^ 2 /\
          ~ xe1_subgraph_of 'K_4 G /\
          forall A : {set G}, xe1_stable_set A -> eps_den * #|A| <= eps_num * n.

(** Corpus row: erdos:518
    Site: none
    Review: none
    English statement: (Erdos problem #518)
      For every n there is m with m^2 <= n such that in every symmetric 2-colouring of the
      edges of the complete graph on n vertices there are one colour b and m monochromatic
      paths of colour b that together cover all n vertices.
    Definitions: [xe2_monochromatic_path G col b p] - p is a non-empty duplicate-free list
      forming a walk in G all of whose consecutive pairs get colour b (XE2.v);
      [xe2_paths_cover_vertices G m P] - every vertex lies on some P i (XE2.v); ['K_n] -
      complete graph (coq-graph-theory).
    Notes: the source asks for sqrt(n) paths; the Rocq body only bounds the number of paths
      by sqrt(n) from above (exists m with m^2 <= n) rather than pinning m = floor(sqrt n).
      Since covering by m paths implies covering by any larger number (paths may repeat),
      the two readings coincide, the hardest instance being m = floor(sqrt n). *)
Definition erdos_518_statement : Prop :=
  forall n : nat, exists m : nat, m ^ 2 <= n /\
    forall col : rel 'I_n,
      symmetric col ->
      exists (b : bool) (P : 'I_m -> seq 'I_n),
        (forall i : 'I_m, @xe2_monochromatic_path 'K_n col b (P i)) /\
        @xe2_paths_cover_vertices 'K_n m P.

(** Corpus row: erdos:547
    Site: none
    Review: none
    English statement: (Erdos problem #547)
      For every tree T on n >= 2 vertices, the diagonal Ramsey number R(T) = R(T,T) is at
      most 2n - 2.
    Definitions: [xe1_tree T] - the vertex set of T is a forest and is connected (XE1.v);
      [xe1_diagonal_ramsey_number T R] - R is the least N such that every graph on N vertices
      contains T or its complement does (XE1.v).
    Notes: guard [2 <= n]: for n = 1 the one-vertex graph is a tree with R = 1, but
      2 * 1 - 2 = 0 in nat, so the bound would be false there. A tree "on n vertices" in the
      conjecture means n >= 2. *)
Definition erdos_547_statement : Prop :=
  forall (n R : nat) (T : sgraph),
    2 <= n ->
    xe1_tree T -> #|T| = n ->
    xe1_diagonal_ramsey_number T R ->
    R <= 2 * n - 2.

(** Corpus row: erdos:549
    Site: none
    Review: none
    English statement: (Erdos problem #549)
      If T is a tree whose bipartition classes have sizes k and 2k, then its diagonal Ramsey
      number is exactly 4k - 1.
    Definitions: [xe1_tree T] - connected forest (XE1.v); [xe2_bipartition_sizes T k (2*k)] -
      the vertices of T split into two disjoint classes of sizes k and 2k covering V(T) with
      every edge crossing (XE2.v); [xe1_diagonal_ramsey_number] (XE1.v).
    Notes: no lower guard on k is stated; at k = 0 the hypotheses force the empty tree, for
      which the body's 4 * 0 - 1 evaluates to 0 in nat and matches the (degenerate) Ramsey
      number, so the instance is consistent rather than false. *)
Definition erdos_549_statement : Prop :=
  forall (k R : nat) (T : sgraph),
    xe1_tree T -> xe2_bipartition_sizes T k (2 * k) ->
    xe1_diagonal_ramsey_number T R ->
    R = 4 * k - 1.

(** Corpus row: erdos:559
    Site: none
    Review: none
    English statement: (Erdos problem #559)
      For every d there is a constant C such that every graph G on n vertices with maximum
      degree at most d has size Ramsey number Rhat(G) = Rhat(G,G) at most C * n.
    Definitions: [xe1_size_ramsey_number G G m] - m is the least number of edges of a graph H
      such that every symmetric 2-colouring of the adjacency of H yields a copy of G in one
      of the two colour classes (XE1.v); [Delta G] - maximum degree (GTBase).
    Notes: the source's implicit constant depending on d is made explicit as C quantified
      after d and uniform in G and n. *)
Definition erdos_559_statement : Prop :=
  forall d : nat, exists C : nat,
    forall (G : sgraph) (n m : nat),
      #|G| = n -> Delta G <= d ->
      xe1_size_ramsey_number G G m ->
      m <= C * n.

(** Corpus row: erdos:565
    Site: none
    Review: none
    English statement: (Erdos problem #565)
      There is a constant C such that every graph G on n vertices has induced Ramsey number
      R*(G) at most 2^(C*n), where R*(G) is the least m for which some graph H on m vertices
      forces, under every symmetric 2-colouring of its edges, a monochromatic INDUCED copy
      of G.
    Definitions: [xe2_induced_ramsey_number G m] - the minimality predicate above, the copy
      being an injective map f preserving edges with their common colour and mapping
      non-adjacent distinct vertices to non-adjacent ones (XE2.v).
    Notes: the 2^{O(n)} of the source is encoded as 2^(C*n) with a single absolute C. *)
Definition erdos_565_statement : Prop :=
  exists C : nat,
    forall (G : sgraph) (n m : nat),
      #|G| = n ->
      xe2_induced_ramsey_number G m ->
      m <= 2 ^ (C * n).

(** Corpus row: erdos:570
    Site: none
    Review: none
    English statement: (Erdos problem #570)
      For every k >= 3 there is M such that for every graph H with m >= M edges and no
      isolated vertex, the Ramsey number R(C_k, H) is at most 2m + floor((k-1)/2).
    Definitions: [xe1_graph_ramsey_number (cycle_graph k) H R] - R is the least N forcing a
      k-cycle in a graph on N vertices or a copy of H in its complement (XE1.v);
      [xe1_no_isolated_vertices] - every vertex has a neighbour (XE1.v); [cycle_graph] -
      GTBase; [x4_edge_count] (X4.v).
    Notes: floor((k-1)/2) is [(k - 1) %/ 2]; the nat subtraction is safe because k >= 3. *)
Definition erdos_570_statement : Prop :=
  forall k : nat, 3 <= k ->
    exists M : nat,
      forall (H : sgraph) (m R : nat),
        M <= m ->
        x4_edge_count H = m -> xe1_no_isolated_vertices H ->
        xe1_graph_ramsey_number (cycle_graph k) H R ->
        R <= 2 * m + ((k - 1) %/ 2).

(** Corpus row: erdos:613
    Site: none
    Review: none
    English statement: (Erdos problem #613)
      For every n >= 3, every graph G with exactly binomial(2n+1,2) - binomial(n,2) - 1 edges
      is the union of a bipartite graph and a graph of maximum degree less than n: some set F
      of edges of G has all degrees below n and deleting F leaves a bipartite graph.
    Definitions: [xe2_bipartite_plus_bounded_degree G d] - existence of such an edge set F,
      using [xe1_delete_edges] (XE1.v) for the deletion and [x4_edge_set] (X4.v) for the
      edges as 2-element sets (XE2.v); [bipartite] - GTBase.
    Notes: the number of vertices of G is left free, as in the source; only the edge count is
      pinned. The degree of a vertex in F is counted as the number of edges of F containing
      it. *)
Definition erdos_613_statement : Prop :=
  forall (n : nat) (G : sgraph),
    3 <= n ->
    x4_edge_count G = 'C(2 * n + 1, 2) - 'C(n, 2) - 1 ->
    xe2_bipartite_plus_bounded_degree G n.

(** Corpus row: erdos:73
    Site: none
    Review: none
    English statement: (Erdos problem #73)
      For every k there is a constant C such that every graph G in which every vertex set S
      contains an independent subset A with 2|A| + k >= |S| (i.e. an independent set of size
      at least (|S| - k)/2) admits a set X of at most C vertices whose removal leaves a
      bipartite graph.
    Definitions: [xe1_stable_set A] - no two vertices of A adjacent (XE1.v); [induced (~: X)]
      - the subgraph induced on the complement of X (coq-graph-theory); [bipartite] - GTBase.
    Notes: the source quantifies over all subgraphs H; the Rocq body quantifies over vertex
      subsets S, i.e. induced subgraphs, which is equivalent for this hypothesis since
      removing edges can only enlarge independent sets. The bound (n-k)/2 is cleared of the
      division as 2 * |A| + k >= |S|. C depends on k only. *)
Definition erdos_73_statement : Prop :=
  forall k : nat, exists C : nat,
    forall G : sgraph,
      (forall S : {set G}, exists A : {set G},
          A \subset S /\ xe1_stable_set A /\ 2 * #|A| + k >= #|S|) ->
      exists X : {set G}, #|X| <= C /\ bipartite (induced (~: X)).

(** Corpus row: erdos:742
    Site: none
    Review: none
    English statement: (Erdos problem #742)
      Every graph G on n vertices of diameter exactly 2 in which deleting any single edge
      raises the diameter above 2 has at most n^2/4 edges (written 4 * e(G) <= n^2).
    Definitions: [xe2_diameter_critical_two G] - every pair of vertices is within distance 2,
      some pair is not within distance 1, and for every edge e the graph with e deleted has a
      pair at distance more than 2 (XE2.v); [xe1_diameter_at_most G r] - every vertex lies in
      the ball of radius r around every vertex (XE1.v); [xe1_delete_edges] (XE1.v);
      [x4_edge_set], [x4_edge_count] (X4.v).
    Notes: "diameter 2" is read as exactly 2, which is why the clause
      [~ xe1_diameter_at_most G 1] is present; it rules out complete graphs, for which the
      criticality clause would be vacuous. *)
Definition erdos_742_statement : Prop :=
  forall (n : nat) (G : sgraph),
    #|G| = n ->
    xe2_diameter_critical_two G ->
    4 * x4_edge_count G <= n ^ 2.

(** Corpus row: erdos:767
    Site: none
    Review: none
    English statement: (Erdos problem #767)
      For every k there is N such that for every n >= N, the maximum number g_k(n) of edges
      of a graph on n vertices containing no cycle with k chords incident to a single vertex
      of that cycle equals (k+1) * n - (k+1)^2.
    Definitions: [xe2_no_cycle_with_incident_chords G k] - for every cycle c of G and every
      vertex v on c, the number of chords of c at v is less than k (XE2.v);
      [xe2_incident_cycle_chord_count c v] - the number of neighbours of v on c that are not
      consecutive with v on c (XE2.v, using [x4_consecutive_in_cycle] from X4.v);
      [xe2_cycle c] - a uniform cycle ([ucycle]) of length more than 2 (XE2.v);
      [xe2_incident_chord_extremal k n m] - m is the maximum edge count over such graphs on n
      vertices (XE2.v).
    Notes: "a cycle with k chords incident to a vertex" is forbidden, hence the strict bound
      chord count < k. The subtraction in (k+1)*n - (k+1)^2 is nat subtraction; for n < k+1
      it would truncate to 0, which is why the threshold N is there. *)
Definition erdos_767_statement : Prop :=
  forall k : nat, exists N : nat,
    forall (n m : nat),
      N <= n ->
      xe2_incident_chord_extremal k n m ->
      m = (k + 1) * n - (k + 1) ^ 2.

(** Corpus row: erdos:800
    Site: none
    Review: none
    English statement: (Erdos problem #800)
      There is an absolute constant C such that every graph G on n vertices with no two
      adjacent vertices both of degree at least 3 has diagonal Ramsey number R(G) <= C * n.
    Definitions: [xe1_diagonal_ramsey_number G R] - R is the least N such that every graph on
      N vertices contains G or its complement does (XE1.v); [N(x)] - neighbourhood
      (coq-graph-theory).
    Notes: C is quantified outermost, matching the source's "the implied constant is
      absolute". *)
Definition erdos_800_statement : Prop :=
  exists C : nat,
    forall (G : sgraph) (n R : nat),
      #|G| = n ->
      (forall x y : G, x -- y -> #|N(x)| < 3 \/ #|N(y)| < 3) ->
      xe1_diagonal_ramsey_number G R ->
      R <= C * n.

(** Corpus row: erdos:801
    Site: none
    Review: none
    English statement: (Erdos problem #801)
      There are constants C > 0 and N such that every graph G on n >= N vertices with no
      independent set larger than s = floor(sqrt n) has a vertex set S of size at most s
      inducing at least (s * floor(log_2 n)) / C edges.
    Definitions: [xe1_sqrt_floor n s] - s^2 <= n and s is largest with that property (XE1.v);
      [xe1_stable_set] - independent set (XE1.v); [trunc_log 2] - MathComp floor of log base
      2; [induced S] - induced subgraph (coq-graph-theory); [x4_edge_count] (X4.v).
    Notes: the source's ">= n^{1/2} vertices" threshold is the floor s, and its implicit
      constant is inverted into the multiplier C on the left of the edge bound. *)
Definition erdos_801_statement : Prop :=
  exists C N : nat,
    0 < C /\
    forall (G : sgraph) (n s : nat),
      N <= n ->
      #|G| = n ->
      xe1_sqrt_floor n s ->
      (forall A : {set G}, xe1_stable_set A -> #|A| <= s) ->
      exists S : {set G},
        #|S| <= s /\ C * x4_edge_count (induced S) >= s * trunc_log 2 n.

(** Corpus row: erdos:803
    Site: none
    Review: none
    English statement: (Erdos problem #803)
      There are absolute constants D and C such that for every m >= 1 there is N with: every
      graph G on n >= N vertices with at least n * floor(log_2 n) edges contains a subgraph H
      on exactly m vertices which is D-balanced (its maximum degree is at most D times its
      minimum degree) and has at least (m * floor(log_2 m)) / C edges.
    Definitions: [xe2_min_degree H d] - d is attained by some vertex and bounds all degrees
      from below (XE2.v); [Delta H] - maximum degree (GTBase); [xe1_subgraph_of] - injective
      edge-preserving map (XE1.v); [trunc_log 2] - MathComp floor of log base 2;
      [x4_edge_count] (X4.v).
    Notes: [trunc_log 2] (MathComp floor-log2) is the intended logarithm; [logn 2] is the
      2-adic valuation. The [1 <= m] guard matches "for every m >= 1": at m = 0 the required
      H would be the empty graph, which cannot satisfy the minimum-degree clause
      ([xe2_min_degree] needs a vertex), making the m = 0 instance vacuously unsatisfiable
      and the whole statement false. D and C are quantified outermost, so they are absolute,
      as the source requires. *)
Definition erdos_803_statement : Prop :=
  exists D C : nat,
    forall m : nat, 1 <= m -> exists N : nat,
      forall (n : nat) (G : sgraph),
        N <= n -> #|G| = n -> n * trunc_log 2 n <= x4_edge_count G ->
        exists H : sgraph,
          xe1_subgraph_of H G /\ #|H| = m /\
          (exists d : nat, xe2_min_degree H d /\ Delta H <= D * d) /\
          C * x4_edge_count H >= m * trunc_log 2 m.

(** Corpus row: erdos:814
    Site: none
    Review: none
    English statement: (Erdos problem #814)
      For every k >= 2 there is a positive rational c = c/d (0 < c < d) such that every graph
      G on n >= k-1 vertices with exactly (k-1)*(n-k+2) + binomial(k-2,2) + 1 edges has a
      non-empty vertex set S with |S| <= (1 - c/d) * n such that every vertex of the induced
      subgraph on S has degree at least k there.
    Definitions: [induced S] - induced subgraph (coq-graph-theory); [x4_edge_count] (X4.v).
    Notes: the constant c_k of the source is a ratio of naturals c/d with 0 < c < d, so the
      size bound reads d * |S| <= (d - c) * n. The non-emptiness clause 0 < |S| is an added
      guard (the empty set would otherwise satisfy the minimum-degree clause vacuously) and
      makes the statement strictly stronger than a literal reading. The edge count is parsed
      as (k-1)*((n-k)+2) with nat subtraction: at the boundary n = k-1 this gives
      (k-1)*2 + C(k-2,2) + 1 where the intended value is (k-1)*1 + C(k-2,2) + 1, so that
      single instance constrains a different family (recorded in the ledger). *)
Definition erdos_814_statement : Prop :=
  forall k : nat, 2 <= k ->
    exists c d : nat,
      0 < c /\ c < d /\
      forall (n : nat) (G : sgraph),
        k - 1 <= n ->
        #|G| = n ->
        x4_edge_count G =
          (k - 1) * (n - k + 2) + 'C(k - 2, 2) + 1 ->
        exists S : {set G},
          0 < #|S| /\
          d * #|S| <= (d - c) * n /\
          forall v : induced S, k <= #|N(v)|.

(** Corpus row: erdos:816
    Site: none
    Review: none
    English statement: (Erdos problem #816)
      Every graph G on exactly 2n+1 vertices with exactly n^2+n+1 edges has two distinct
      vertices of equal degree joined by a path of length 3.
    Definitions: [xe2_path_length3 G x y] - there are a, b making x, a, b, y four distinct
      vertices with x-a, a-b and b-y edges (XE2.v); [x4_edge_count] (X4.v).
    Notes: "path of length 3" is three edges through four distinct vertices, which the
      uniqueness clause enforces. *)
Definition erdos_816_statement : Prop :=
  forall (n : nat) (G : sgraph),
    #|G| = 2 * n + 1 ->
    x4_edge_count G = n ^ 2 + n + 1 ->
    exists x y : G,
      x != y /\ #|N(x)| = #|N(y)| /\ @xe2_path_length3 G x y.

(** Corpus row: erdos:915
    Site: none
    Review: none
    English statement: (Erdos problem #915)
      Every graph G with exactly 1 + n*(m-1) vertices and exactly 1 + n*binomial(m,2) edges
      has two distinct vertices x, y joined by m paths from x to y that are pairwise
      internally vertex-disjoint and pairwise edge-disjoint.
    Definitions: [xe2_paths_internally_disjoint x y P] - the internal vertex sets
      ([xe2_internal_path_vertices], the vertices of a path other than x and y) of distinct
      paths are disjoint (XE2.v); [xe2_paths_edge_disjoint P] - the edge sets
      ([xe2_path_edge_set]) of distinct paths are disjoint (XE2.v); paths are lists starting
      at x, ending at y and following adjacency ([path (--)]).
    Notes: the source says "m disjoint paths"; the body asks for both internal vertex
      disjointness and edge disjointness, which is strictly stronger (it also forbids two
      copies of the single edge x-y). Nat subtraction in m-1 makes the m = 0 instance
      vacuous. *)
Definition erdos_915_statement : Prop :=
  forall (n m : nat) (G : sgraph),
    #|G| = 1 + n * (m - 1) ->
    x4_edge_count G = 1 + n * 'C(m, 2) ->
    exists x y : G, exists P : 'I_m -> seq G,
      x != y /\
      (forall i : 'I_m,
        if P i is z :: p then z = x /\ last z p = y /\ path (--) z p else False) /\
      xe2_paths_internally_disjoint x y P /\
      xe2_paths_edge_disjoint P.

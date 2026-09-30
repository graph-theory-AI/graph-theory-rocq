(** * Packing.conjectures.U9 — milestone U9 (namespace Packing, plan v4)

    Statement-only formalizations (axiom-free: no Conjecture/Axiom/Parameter/
    Admitted) of thirteen open problems on packings, partitions, transversals and
    connectivity.

    CARRIERS ARE CHOSEN PER ROW (no blanket [sgraph]), following each row's
    [rocq_idiom] / [selected_proposition]:

      - simple-graph (sgraph) rows: P3-partition (Row 1), triangle packing vs.
        transversal (Row 2), friendly partitions (Row 3), BEC packing (Row 5),
        Lovász path removal (Row 6), Jones (Row 7, PLANAR-gated), odd-cycle
        transversal (Row 8), matching-cut & girth (Row 9), hypercube matchings
        (Row 11), weak saturation (Row 12);
      - multigraph (mgraph = [graph unit unit], with the raw [edge]/[walk]
        /[edges_at]/[source]/[target] API) rows, where the object level is EDGE
        SETS: partitioning edge-connectivity (Row 4), Kriesel trees (Row 10),
        T-join packing (Row 13).

    IMPORT ORDER: [mgraph] is imported BEFORE [base] (base re-exports the sgraph
    vocabulary [sgraph]/[x -- y]/[N(x)]/[connected]/[clique]/[ucycle]/[ucycleb] and
    owns [Delta] (Δ), [regular], [girth_geq]); putting coq-graph-theory's [mgraph]
    first avoids its DIRECTED [line_graph] shadowing base's undirected one (we do
    not use [line_graph] here, but keep the federation-wide ordering invariant).

    REUSED FROM base (NOT redefined): [Delta] (= max-degree Δ, Row 5), [regular]
    (= cubic / r-regular, Rows 1,3), [girth_geq] (Row 9), [clique] (triangles),
    [connected] (induced connectivity), [ucycle]/[ucycleb] (cycles), [N(_)].

    AREA primitives introduced here (packing/partition specific): [is_P3] /
    P3-partition, [is_triangle] / [tri_edges] / triangle-packing /
    triangle-edge-transversal, [friendly_partition] / [all_but_finitely_many_regular],
    [uwalk] (undirected multigraph walk) / [edge_conn_via] / [edge_conn_subset]
    (edge-set-partition-connectivity), [pack]
    (graph-packing), [is_induced_path] (induced-path) / [k_connected] /
    [k_connected_on] (k-connectivity, cross-area @MOVE-to-base candidate),
    [hits_all_cycles] / [is_min_fvs] (feedback-vertex-set) / [cycle_packing] /
    [is_max_cycle_packing] (cycle-packing), [del_bipartite] (edge-odd-cycle-
    transversal) / [triangle_free], [matching_cut] / [avg_deg_lt] (average-degree),
    [acyclic_mg] / [edge_disjoint_uv_paths] / [tree_contains_T] (edge-disjoint
    Steiner trees), [hypercube] (hypercube-graph) / [is_matching_edges] /
    [matching-extension], [copy_Q3_through] / [weakly_saturates] / [is_wsat]
    (weak-saturation-number), [cut_mg] / [is_tjoin] (t-join) / T-cut / graft.

    PLANARITY (Row 7, Jones, [requires_planarity=true]): planarity is the base-
    provided combinatorial predicate [wagner_planar G := ~ minor G 'K_5 /\
    ~ minor G (KB 3 3)] (no K5 / no K3,3 minor).  By Wagner's theorem this IS
    planarity, so Row 7 is now FAITHFUL and Four-Colour-free; [wagner_planar] is
    used opaquely (we do not import [minor]).  The former abstract [planar : sgraph
    -> Prop] placeholder is gone.  All thirteen rows model their statements fully.

    NAMING: predicates use the [is_] prefix ([is_P3], [is_triangle], [is_min_fvs],
    [is_matching_edges], [is_tjoin], [is_wsat]); a trailing [G] ([edge_setG],
    [hamiltonian_cycleG], [cycle_edgesG]) is purely a clash-avoidance suffix (it
    dodges shadowing of upstream names), NOT an arity marker. *)

From GraphTheory Require Import mgraph.
From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ================================================================= *)
(** ** Shared simple-graph primitives *)

(** A path of length 2 (a [P3]): three distinct vertices [x - b - y] with centre
    [b] adjacent to the two ends [x], [y]. *)
Definition is_P3 (G : sgraph) (S : {set G}) : Prop :=
  exists b x y : G,
    [/\ b -- x, b -- y, x != y & S = [set x; b; y]].

(** A triangle: a 3-clique. *)
Definition is_triangle (G : sgraph) (T : {set G}) : Prop :=
  clique T /\ #|T| = 3.

(** The (unordered) edge set of a vertex set [T]: its 2-element subsets.  For a
    clique these are exactly the edges spanned by [T]. *)
Definition tri_edges (G : sgraph) (T : {set G}) : {set {set G}} :=
  [set e : {set G} | (e \subset T) && (#|e| == 2)].

(** The whole-graph edge set (each unordered adjacent pair). *)
Definition edge_setG (G : sgraph) : {set {set G}} :=
  [set e : {set G} | [exists x, exists y, (x -- y) && (e == [set x; y])]].

(** Bipartite after deleting the edge set [S]: a 2-colouring with no
    surviving (non-[S]) edge monochromatic.  "Deleting [S] destroys every odd
    cycle" ⟺ the remaining graph is bipartite. *)
Definition del_bipartite (G : sgraph) (S : {set {set G}}) : Prop :=
  exists A : {set G},
    forall x y : G, x -- y -> [set x; y] \notin S -> (x \in A) != (y \in A).

(** Triangle-free: no 3-clique. *)
(* [triangle_free] now from graph-theory-base (vertex-triple form, equivalent to ~ is_triangle). *)

(** ** k-connectivity (Whitney form, separator-free).  [@MOVE-to-base]: also used
    by hamiltonicity-theory/U2; promote to base when a second area is wired. *)
(* [k_connected] now from graph-theory-base. *)

(** k-connectivity of the induced subgraph on [U] (deletions taken from [U]). *)
Definition k_connected_on (G : sgraph) (U : {set G}) (k : nat) : Prop :=
  (k < #|U|) /\ forall S : {set G}, #|S| < k -> connected (U :\: S).

(** Adjacency of two vertices that are consecutive on the seq [p] (for [uniq p]). *)
Definition consec (G : sgraph) (p : seq G) (a b : G) : bool :=
  ((index a p).+1 == index b p) || ((index b p).+1 == index a p).

(** A simple [x]–[y] path encoded as a vertex seq: nonempty, starts at [x], ends
    at [y], a consecutive-adjacency walk. *)
Definition spath (G : sgraph) (x y : G) (p : seq G) : bool :=
  [&& p != [::], head x p == x, last x p == y & sorted (--) p].

(** An INDUCED [x]–[y] path: a simple path with no chords (any two of its vertices
    adjacent in [G] are consecutive on the path). *)
Definition is_induced_path (G : sgraph) (x y : G) (p : seq G) : Prop :=
  [/\ spath x y p, uniq p
    & {in p &, forall a b : G, a -- b -> consec p a b}].

(** A friendly partition (into [A] and its complement): every vertex has at least
    as many neighbours in its own class as in the other; both classes nonempty. *)
Definition friendly_partition (G : sgraph) (A : {set G}) : Prop :=
  [/\ A != set0, A != [set: G]
    & forall v : G,
        (v \in A -> #|N(v) :&: (~: A)| <= #|N(v) :&: A|) /\
        (v \notin A -> #|N(v) :&: A| <= #|N(v) :&: (~: A)|)].

(** "All but finitely many [r]-regular graphs satisfy [P]": some order threshold
    [N] beyond which every [r]-regular graph satisfies [P].  (Finitely many graphs
    of each order ⇒ this is the faithful "cofinite" reading.) *)
Definition all_but_finitely_many_regular (r : nat) (P : sgraph -> Prop) : Prop :=
  exists N : nat, forall G : sgraph, regular G r -> N < #|G| -> P G.

(** Two same-order graphs PACK: a bijection placing [G1] onto [G2]'s vertices with
    no edge of [G1] landing on an edge of [G2] (edge-disjoint placement). *)
Definition pack (G1 G2 : sgraph) : Prop :=
  exists f : G1 -> G2,
    bijective f /\ forall x y : G1, x -- y -> ~~ (f x -- f y).

(** A matching-cut: a bipartition [{A, ~A}] (both nonempty) whose crossing edges
    form a matching — every vertex has at most one neighbour on the other side. *)
Definition matching_cut (G : sgraph) : Prop :=
  exists A : {set G},
    [/\ A != set0, A != [set: G]
      & forall v : G,
          (v \in A -> #|N(v) :&: (~: A)| <= 1) /\
          (v \notin A -> #|N(v) :&: A| <= 1)].

(** Average degree strictly below [d]: ∑deg < d·n (avoids fractions). *)
Definition avg_deg_lt (G : sgraph) (d : nat) : Prop :=
  (\sum_(v : G) #|N(v)|) < d * #|G|.

(** ** Feedback vertex sets and cycle packings *)

(** [X] meets every genuine cycle (size > 2); i.e. [G - X] is acyclic. *)
Definition hits_all_cycles (G : sgraph) (X : {set G}) : Prop :=
  forall c : seq G, ucycle (--) c -> 2 < size c -> exists2 v : G, v \in c & v \in X.

(** [m] is the minimum feedback-vertex-set size cc(G). *)
Definition is_min_fvs (G : sgraph) (m : nat) : Prop :=
  (exists X : {set G}, hits_all_cycles X /\ #|X| = m) /\
  (forall X : {set G}, hits_all_cycles X -> m <= #|X|).

(** A cycle packing: a list of genuine cycles, pairwise vertex-disjoint (each
    vertex on at most one of them). *)
Definition cycle_packing (G : sgraph) (cs : seq (seq G)) : Prop :=
  (forall c : seq G, c \in cs -> ucycle (--) c /\ 2 < size c) /\
  (forall v : G, count (fun c => v \in c) cs <= 1).

(** [m] is the maximum cycle-packing size cp(G). *)
Definition is_max_cycle_packing (G : sgraph) (m : nat) : Prop :=
  (exists cs : seq (seq G), cycle_packing cs /\ size cs = m) /\
  (forall cs : seq (seq G), cycle_packing cs -> size cs <= m).

(** ** Hamiltonicity on simple graphs (Row 11).  [@MOVE-to-base]: cross-area
    (hamiltonicity-theory/U2 owns the same notion) — promote when a 2nd consumer
    is wired, mirroring the [k_connected] precedent. *)
Definition hamiltonian_cycleG (G : sgraph) (c : seq G) : bool :=
  ucycleb (--) c && (size c == #|G|).
Arguments hamiltonian_cycleG : clear implicits.

Definition cycle_edgesG (G : sgraph) (c : seq G) : {set {set G}} :=
  [set [set x; next c x] | x in [set z | z \in c]].
Arguments cycle_edgesG : clear implicits.

(** A set of edges that is a matching: each element is a genuine edge, and every
    vertex lies in at most one of them. *)
Definition is_matching_edges (G : sgraph) (M : {set {set G}}) : Prop :=
  (forall e : {set G}, e \in M -> exists x y : G, x -- y /\ e = [set x; y]) /\
  (forall v : G, #|[set e in M | v \in e]| <= 1).

(** ** The hypercube graph Q_d (Hamming graph on d-bit strings) *)
Section Hypercube.
Variable d : nat.
Definition hc_rel : rel (d.-tuple bool) :=
  fun x y => #|[set i : 'I_d | tnth x i != tnth y i]| == 1.
Lemma hc_sym : symmetric hc_rel.
Proof.
move=> x y; rewrite /hc_rel.
have -> : [set i : 'I_d | tnth x i != tnth y i]
        = [set i : 'I_d | tnth y i != tnth x i]
  by apply/setP=> i; rewrite !inE eq_sym.
by [].
Qed.
Lemma hc_irrefl : irreflexive hc_rel.
Proof.
move=> x; rewrite /hc_rel.
have -> : [set i : 'I_d | tnth x i != tnth x i] = set0
  by apply/setP=> i; rewrite !inE eqxx.
by rewrite cards0.
Qed.
Definition hypercube : sgraph := SGraph hc_sym hc_irrefl.
End Hypercube.

(** ** Weak saturation of Q_3 in K_n (Row 12)

    Vertices of K_n are ['I_n]; a "graph on K_n" is an edge set
    [E : {set {set 'I_n}}] of 2-subsets.  A copy of [Q_3] in [E] is an injective
    embedding of [hypercube 3] mapping its edges into [E]. *)

(** A copy of Q_3 inside the edge set [E] that USES the edge [e]
    (i.e. some Q_3-edge maps onto [e]). *)
Definition copy_Q3_through (n : nat) (E : {set {set 'I_n}}) (e : {set 'I_n}) : Prop :=
  exists f : hypercube 3 -> 'I_n,
    [/\ injective f,
        (forall x y : hypercube 3, x -- y -> [set f x; f y] \in E)
      & (exists x y : hypercube 3, x -- y /\ [set f x; f y] = e)].

(** [F] is weakly Q_3-saturating in K_n: [F] is a graph on K_n, and its missing
    edges can be enumerated [s] so that adding each [s_i] (to [F] together with all
    earlier additions, including [s_i]) completes a new Q_3 copy through [s_i]. *)
Definition weakly_saturates (n : nat) (F : {set {set 'I_n}}) : Prop :=
  (forall e : {set 'I_n}, e \in F -> #|e| == 2) /\
  exists s : seq {set 'I_n},
    [/\ uniq s,
        (forall e : {set 'I_n}, (e \in s) = ((#|e| == 2) && (e \notin F)))
      & (forall i : nat, i < size s ->
           copy_Q3_through (F :|: [set x in take i.+1 s]) (nth set0 s i))].

(** [m] is the weak-saturation number wsat(K_n, Q_3): least edge count of a weakly
    Q_3-saturating graph. *)
Definition is_wsat (n : nat) (m : nat) : Prop :=
  (exists F : {set {set 'I_n}}, weakly_saturates F /\ #|F| = m) /\
  (forall F : {set {set 'I_n}}, weakly_saturates F -> m <= #|F|).

(** ================================================================= *)
(** ** Shared multigraph primitives (edge-set object level) *)

(** An UNDIRECTED walk in a multigraph: each step may traverse an edge in either
    orientation (the library [walk] only goes [source -> target], which on the
    DIRECTED carrier [mgraph = graph unit unit] would encode directed/strong
    reachability — wrong for the undirected "edge-connected graph" of Row 4). *)
(* [uwalk] (undirected multigraph walk) now from graph-theory-base. *)

(** Connectivity using only the edges of [E]: any two vertices joined by an
    UNDIRECTED [E]-walk (undirected edge-connectivity, faithful to Row 4). *)
Definition edge_conn_via (G : mgraph) (E : {set edge G}) : Prop :=
  forall x y : G, exists w : seq (edge G),
    uwalk x y w /\ all (fun e => e \in E) w.

(** The spanning subgraph [(V, E)] is [a]-edge-connected: deleting fewer than [a]
    of its edges keeps it (spanning-)connected. *)
Definition edge_conn_subset (G : mgraph) (E : {set edge G}) (a : nat) : Prop :=
  forall F : {set edge G}, F \subset E -> #|F| < a -> edge_conn_via (E :\: F).

(** A forest / acyclic edge set: every nonempty subset has a vertex of odd degree
    (equivalently, trivial binary cycle space). *)
Definition acyclic_mg (G : mgraph) (H : {set edge G}) : Prop :=
  forall C : {set edge G}, C \subset H -> C != set0 ->
    exists v : G, odd #|edges_at v :&: C|.

(** [m] pairwise edge-disjoint [u]–[v] walks (an [m]-flow of edge-disjoint paths). *)
Definition edge_disjoint_uv_paths (G : mgraph) (u v : G) (m : nat) : Prop :=
  exists ws : seq (seq (edge G)),
    [/\ size ws = m,
        (forall w : seq (edge G), w \in ws -> walk u v w)
      & (forall e : edge G, count (fun w => e \in w) ws <= 1)].

(** A tree (acyclic edge set) that contains / connects [T]: every two vertices of
    [T] are joined by an [H]-walk. *)
Definition tree_contains_T (G : mgraph) (T : {set G}) (H : {set edge G}) : Prop :=
  acyclic_mg H /\
  (forall x y : G, x \in T -> y \in T ->
     exists w : seq (edge G), walk x y w /\ all (fun e => e \in H) w).

(** The edge cut of a vertex set [S]: edges with exactly one endpoint in [S]. *)
Definition cut_mg (G : mgraph) (S : {set G}) : {set edge G} :=
  [set e | (source e \in S) (+) (target e \in S)].

(** A [T]-join: an edge set whose odd-degree vertices are exactly [T]. *)
Definition is_tjoin (G : mgraph) (T : {set G}) (J : {set edge G}) : Prop :=
  forall v : G, odd #|edges_at v :&: J| = (v \in T).

(** ================================================================= *)
(** Corpus row: opg:partition_of_a_cubic_3_connected_graphs_into_paths_of_length_2
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/partition_of_a_cubic_3_connected_graphs_into_paths_of_length_2/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/partition_of_a_cubic_3_connected_graphs_into_paths_of_length_2.json
    English statement: (Open Problem Garden, "Partition of a cubic 3-connected graphs
      into paths of length 2")
      For every k >= 1 and every simple graph G: if G is 3-regular, 3-connected and has
      exactly 3k vertices, then there is a family P of vertex sets that partitions
      V(G), every member of which is a path on three vertices (a path of length 2), and
      P has exactly k members.
    Definitions: [is_P3 S] — S = {x, b, y} with b adjacent to both x and y and x != y
      (this file); [regular G 3] — cubic, [k_connected G 3] — Whitney 3-connectivity,
      which carries the guard 3 < |V(G)| (both GTBase base); [partition] — MathComp
      finset partition of the vertex set.
    Notes: the blocks of the partition are exactly the k paths. The guard 0 < k
      excludes the degenerate empty partition. *)
Definition partition_of_a_cubic_3_connected_graphs_into_paths_o_statement : Prop :=
  forall (k : nat) (G : sgraph),
    0 < k -> regular G 3 -> k_connected G 3 -> #|G| = 3 * k ->
    exists P : {set {set G}},
      [/\ partition P [set: G],
          (forall S : {set G}, S \in P -> is_P3 S)
        & #|P| = k].

(** Corpus row: opg:triangle_packing_vs_triangle_edge_transversal
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/triangle_packing_vs_triangle_edge_transversal/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/triangle_packing_vs_triangle_edge_transversal.json
    English statement: (Open Problem Garden, "Triangle-packing vs triangle
      edge-transversal")
      For every natural number k and every simple graph G: if every set P of triangles
      of G whose edge sets are pairwise disjoint has at most k members, then there is a
      set S of at most 2k two-element vertex sets such that every triangle of G has one
      of its three edges in S.
    Definitions: [is_triangle T] — T is a clique with exactly three vertices (this
      file); [tri_edges T] — the two-element subsets of T, which for a clique are
      exactly the edges it spans (this file); [clique] — coq-graph-theory sgraph.v.
    Notes: the packing hypothesis quantifies over sets of pairwise edge-disjoint
      triangles (not lists), so repetitions cannot inflate a packing. The transversal S
      is an arbitrary set of two-element vertex sets rather than a subset of E(G);
      since only its intersections with triangle edge sets are used, non-edges in S
      only waste the budget 2k, so this reading is at least as strong as the source. *)
Definition triangle_packing_vs_triangle_edge_transversal_statement : Prop :=
  forall (k : nat) (G : sgraph),
    (forall P : {set {set G}},
       (forall T : {set G}, T \in P -> is_triangle T) ->
       {in P &, forall T1 T2 : {set G},
          T1 != T2 -> [disjoint tri_edges T1 & tri_edges T2]} ->
       #|P| <= k) ->
    exists S : {set {set G}},
      #|S| <= 2 * k /\
      (forall T : {set G}, is_triangle T ->
         exists2 e : {set G}, e \in tri_edges T & e \in S).

(** Corpus row: opg:friendly_partitions
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/friendly_partitions/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/friendly_partitions.json
    English statement: (Open Problem Garden, "Friendly partitions")
      For every r there is an order threshold N such that every r-regular simple graph
      with more than N vertices has a friendly partition: a vertex set A, neither empty
      nor the whole vertex set, such that every vertex of A has at least as many
      neighbours inside A as outside it, and every vertex outside A has at least as
      many neighbours outside A as inside it.
    Definitions: [friendly_partition A] — the three conjuncts just described (this
      file); [all_but_finitely_many_regular r P] — there is an N such that every
      r-regular G with N < |V(G)| satisfies P (this file); [regular] — GTBase base.
    Notes: "all but finitely many r-regular graphs" is read as cofinite in the order:
      there are finitely many graphs of each order, so an order threshold is the
      faithful reading. *)
Definition friendly_partitions_statement : Prop :=
  forall r : nat,
    all_but_finitely_many_regular r
      (fun G => exists A : {set G}, friendly_partition A).

(** Corpus row: opg:partitioning_edge_connectivity
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/partitioning_edge_connectivity/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/partitioning_edge_connectivity.json
    English statement: (Open Problem Garden, "Partitioning edge-connectivity")
      For all a and b and every multigraph G with at least one vertex: if G is
      (a+b+2)-edge-connected, then its edge set splits into two disjoint parts A and B
      covering every edge such that the spanning subgraph (V, A) is a-edge-connected
      and the spanning subgraph (V, B) is b-edge-connected.
    Definitions: [edge_conn_via E] — every two vertices are joined by an undirected
      walk using only edges of E (this file); [edge_conn_subset E a] — deleting fewer
      than a edges of E leaves the spanning subgraph on the remaining edges connected
      (this file); [uwalk] — undirected multigraph walk (GTBase base); [mgraph],
      [edge], [source]/[target] — coq-graph-theory mgraph.v.
    Notes: the carrier is a multigraph at the edge-set level. An undirected walk is
      used instead of the library's [walk], which on the directed carrier
      [mgraph = graph unit unit] would encode strong reachability rather than the
      undirected edge-connectivity the row is about. Guard 0 < |V(G)|. *)
Definition partitioning_edge_connectivity_statement : Prop :=
  forall (a b : nat) (G : mgraph),
    0 < #|G| -> edge_conn_subset [set: edge G] (a + b + 2) ->
    exists A B : {set edge G},
      [/\ A :|: B = [set: edge G], [disjoint A & B],
          edge_conn_subset A a & edge_conn_subset B b].

(** Corpus row: opg:the_bollobas_eldridge_catlin_conjecture_on_graph_packing
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/the_bollobas_eldridge_catlin_conjecture_on_graph_packing/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/the_bollobas_eldridge_catlin_conjecture_on_graph_packing.json
    English statement: (Bollobas, Eldridge and Catlin, "The Bollobas-Eldridge-Catlin
      Conjecture on graph packing")
      For every n and all simple graphs G1 and G2 with exactly n vertices each: if
      (Delta(G1)+1) * (Delta(G2)+1) < n+1, then G1 and G2 pack, that is, there is a
      bijection f from V(G1) to V(G2) such that no edge of G1 is mapped onto an edge
      of G2.
    Definitions: [pack G1 G2] — a bijection f with f x not adjacent to f y whenever
      x -- y (this file); [Delta] — maximum degree (GTBase base).
    Notes: the common order n is imposed by two separate cardinality hypotheses rather
      than by a shared vertex type. *)
Definition the_bollobas_eldridge_catlin_conjecture_on_graph_pac_statement : Prop :=
  forall (n : nat) (G1 G2 : sgraph),
    #|G1| = n -> #|G2| = n ->
    (Delta G1 + 1) * (Delta G2 + 1) < n + 1 ->
    pack G1 G2.

(** Corpus row: opg:lovasz_path_removal_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/lovasz_path_removal_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/lovasz_path_removal_conjecture.json
    English statement: (Lovasz, "Lovasz Path Removal Conjecture")
      There is a function f on natural numbers such that for every k, every simple
      graph G and all distinct vertices x and y of G: if G is f(k)-connected, then
      there is an induced path p from x to y such that the set of vertices of G not on
      p is k-connected.
    Definitions: [consec p a b] — a and b are consecutive on the sequence p (this
      file); [spath x y p] — a nonempty vertex sequence starting at x, ending at y,
      with consecutive entries adjacent (this file); [is_induced_path x y p] — such a
      path with distinct vertices and no chords, i.e. any two of its vertices adjacent
      in G are consecutive on p (this file); [k_connected_on U k] — k < |U| and U minus
      any set of fewer than k vertices is connected (this file); [k_connected] —
      Whitney k-connectivity (GTBase base).
    Notes: "G - V(P) is k-connected" is rendered on the complement vertex set through
      [k_connected_on] rather than on an induced-subgraph object; the constraint
      k < |U| inside [k_connected_on] is part of the conclusion. *)
Definition lovasz_path_removal_statement : Prop :=
  exists f : nat -> nat,
    forall (k : nat) (G : sgraph) (x y : G),
      x != y -> k_connected G (f k) ->
      exists p : seq G,
        is_induced_path x y p /\
        k_connected_on ([set: G] :\: [set z in p]) k.

(** Corpus row: opg:jones_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/jones_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/jones_conjecture.json
    English statement: (Jones, "Jones' conjecture")
      For every simple graph G and all natural numbers ccn and cpn: if G is planar, ccn
      is the least size of a feedback vertex set of G (a vertex set meeting every cycle
      of length greater than 2), and cpn is the greatest number of pairwise
      vertex-disjoint such cycles in G, then ccn <= 2 * cpn.
    Definitions: [hits_all_cycles X] — X meets every cycle of length greater than 2
      (this file); [is_min_fvs G m] / [is_max_cycle_packing G m] — relational minimum /
      maximum, i.e. a witness attaining m plus the corresponding bound on all witnesses
      (this file); [cycle_packing cs] — a list of cycles of length greater than 2 with
      every vertex on at most one of them (this file); [wagner_planar G] — no K5 minor
      and no K3,3 minor (GTBase base); [ucycle] — MathComp / coq-graph-theory.
    Notes: planarity is the Wagner minor characterisation, used opaquely, so the row is
      faithful and Four-Colour-free (the former abstract [planar : sgraph -> Prop]
      placeholder is gone). Stating cc and cp relationally avoids having to prove that
      the extrema exist. The corpus row is marked partial: the bound is known for
      planar graphs, which is exactly the case the body states. *)
Definition jones_statement : Prop :=
  forall (G : sgraph) (ccn cpn : nat),
    wagner_planar G -> is_min_fvs G ccn -> is_max_cycle_packing G cpn ->
    ccn <= 2 * cpn.

(** Corpus row: opg:odd_cycle_transversal_in_triangle_free_graphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/odd_cycle_transversal_in_triangle_free_graphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/odd_cycle_transversal_in_triangle_free_graphs.json
    English statement: (Open Problem Garden, "Odd-cycle transversal in triangle-free
      graphs")
      For every triangle-free simple graph G there is a set S of edges of G with at most
      floor(|V(G)|^2 / 25) members whose deletion leaves a bipartite graph: there is a
      vertex set A such that every edge of G outside S has exactly one endpoint in A.
    Definitions: [edge_setG G] — the two-element vertex sets {x, y} with x -- y (this
      file); [del_bipartite S] — there is an A with (x in A) != (y in A) for every edge
      {x, y} not in S (this file); [triangle_free] — no three pairwise adjacent
      vertices (GTBase base).
    Notes: "deleting S destroys every odd cycle" is rendered as "the remaining graph is
      bipartite", which is equivalent; n^2/25 is MathComp floor division. *)
Definition odd_cycle_transversal_in_triangle_free_graphs_statement : Prop :=
  forall G : sgraph,
    triangle_free G ->
    exists S : {set {set G}},
      [/\ S \subset edge_setG G,
          #|S| <= (#|G| ^ 2) %/ 25
        & del_bipartite S].

(** Corpus row: opg:matching_cut_and_girth
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/matching_cut_and_girth/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/matching_cut_and_girth.json
    English statement: (Open Problem Garden, "Matching cut and girth")
      For every d there is a g such that every simple graph G with at least one vertex,
      average degree smaller than d, and girth at least g has a matching-cut: a vertex
      set A, neither empty nor the whole vertex set, such that every vertex of A has at
      most one neighbour outside A and every vertex outside A has at most one neighbour
      in A.
    Definitions: [avg_deg_lt G d] — the sum of the degrees is strictly less than
      d * |V(G)| (this file, fraction-free); [matching_cut G] — the bipartition
      condition just described (this file); [girth_geq] — GTBase base.
    Notes: the average-degree bound is cross-multiplied to avoid rationals; guard
      0 < |V(G)| keeps that reading faithful. *)
Definition matching_cut_and_girth_statement : Prop :=
  forall d : nat, exists g : nat,
    forall G : sgraph,
      0 < #|G| -> avg_deg_lt G d -> girth_geq G g -> matching_cut G.

(** Corpus row: opg:kriesells_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/kriesells_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/kriesells_conjecture.json
    English statement: (Kriesell, "Kriesell's Conjecture")
      For every multigraph G with at least one vertex, every vertex set T and every
      k >= 1: if every pair u, v of vertices of T is joined by 2k pairwise edge-disjoint
      u-v walks, then there are k pairwise edge-disjoint trees (acyclic edge sets) each
      of which connects all of T.
    Definitions: [edge_disjoint_uv_paths u v m] — a list of m walks from u to v with
      every edge on at most one of them (this file); [acyclic_mg H] — every nonempty
      subset of H has a vertex of odd degree inside it, i.e. trivial binary cycle space
      (this file); [tree_contains_T T H] — H is acyclic and any two vertices of T are
      joined by a walk inside H (this file); [walk], [edges_at] — coq-graph-theory
      mgraph.v.
    Notes: guard 0 < k excludes the trivially satisfiable k = 0 (empty list of trees);
      guard 0 < |V(G)| excludes the empty multigraph. Edge-disjointness of the k trees
      is expressed as "every edge lies in at most one member of the list". *)
Definition kriesells_statement : Prop :=
  forall (G : mgraph) (T : {set G}) (k : nat),
    0 < #|G| -> 0 < k ->
    (forall u v : G, u \in T -> v \in T -> edge_disjoint_uv_paths u v (2 * k)) ->
    exists Ts : seq {set edge G},
      [/\ size Ts = k,
          (forall Ti : {set edge G}, Ti \in Ts -> tree_contains_T T Ti)
        & (forall e : edge G, count (fun Ti : {set edge G} => e \in Ti) Ts <= 1)].

(** Corpus row: opg:matchings_extends_to_hamilton_cycles_in_hypercubes
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/matchings_extends_to_hamilton_cycles_in_hypercubes/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/matchings_extends_to_hamilton_cycles_in_hypercubes.json
    English statement: (Open Problem Garden, "Matchings extend to Hamiltonian cycles in
      hypercubes")
      For every d >= 2 and every set M of edges of the d-dimensional hypercube that is a
      matching, there is a Hamiltonian cycle of the hypercube whose edge set contains M.
    Definitions: [hypercube d] — the graph on d-bit tuples in which two tuples are
      adjacent exactly when they differ in one coordinate (this file); [is_matching_edges
      M] — every member of M is a genuine edge and every vertex lies in at most one
      member (this file); [hamiltonian_cycleG G c] — c is a uniq cycle of length |V(G)|
      (this file, from MathComp's [ucycleb]); [cycle_edgesG G c] — the edges {x, next c
      x} for x on c (this file).
    Notes: guard 2 <= d, since the hypercubes of dimension 0 and 1 have no Hamiltonian
      cycle. *)
Definition matchings_extends_to_hamilton_cycles_in_hypercubes_statement : Prop :=
  forall (d : nat) (M : {set {set hypercube d}}),
    2 <= d -> is_matching_edges M ->
    exists c : seq (hypercube d),
      hamiltonian_cycleG (hypercube d) c /\
      M \subset cycle_edgesG (hypercube d) c.

(** Corpus row: opg:weak_saturation_of_the_cube_in_the_clique
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/weak_saturation_of_the_cube_in_the_clique/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/weak_saturation_of_the_cube_in_the_clique.json
    English statement: (Open Problem Garden, "Weak saturation of the cube in the
      clique")
      For every n >= 8 the weak saturation number wsat(K_n, Q_3) is well defined: there
      is a natural number m that is the least number of edges of a graph on n vertices
      which weakly saturates the 3-dimensional cube in K_n.
    Definitions: [copy_Q3_through E e] — an injective map of the vertices of
      [hypercube 3] into 'I_n sending every cube edge into E, one of them onto e (this
      file); [weakly_saturates n F] — F is a set of two-element subsets of 'I_n and the
      missing two-subsets can be enumerated without repetition so that adding each one
      (together with all earlier additions) completes a new cube copy through it (this
      file); [is_wsat n m] — some weakly saturating F has exactly m edges and every
      weakly saturating F has at least m (this file); [hypercube] — this file.
    Notes: PROXY ENCODING. The source is a "Determine wsat(K_n, Q_3)" problem with no
      proposition to prove; it is formalised as well-definedness of the quantity (the
      minimum exists), not as a closed-form value, so the Rocq statement is weaker than
      a determination of wsat. Guard 8 <= n, since Q_3 has eight vertices. *)
Definition weak_saturation_of_the_cube_in_the_clique_statement : Prop :=
  forall n : nat, 8 <= n -> exists m : nat, is_wsat n m.

(** Corpus row: opg:packing_t_joins
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/packing_t_joins/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/packing_t_joins.json
    English statement: (Open Problem Garden, "Packing T-joins")
      There is a fixed constant c such that for every multigraph G with at least one
      vertex, every nonempty vertex set T of even size and every k: if every vertex set
      S with |S intersect T| odd has an edge cut of at least k edges, then there are
      pairwise edge-disjoint T-joins J_0, ..., J_{m-1} with 2k <= 3(m + c), that is,
      m >= (2/3)k - c.
    Definitions: [cut_mg S] — the edges with exactly one endpoint in S (this file);
      [is_tjoin T J] — an edge set whose odd-degree vertices are exactly those of T
      (this file); [edges_at] — coq-graph-theory mgraph.v.
    Notes: the constant c is existentially quantified before all the universals, as in
      the source. The bound m >= (2/3)k - c is rendered fraction-free and without
      truncated subtraction as 2k <= 3(m + c). Guard 0 < |T| excludes the degenerate
      empty graft, where the cut hypothesis is vacuous and a repeated empty T-join
      would satisfy the bound trivially. *)
Definition packing_t_joins_statement : Prop :=
  exists c : nat,
    forall (G : mgraph) (T : {set G}) (k : nat),
      0 < #|G| -> 0 < #|T| -> ~~ odd #|T| ->
      (forall S : {set G}, odd #|S :&: T| -> k <= #|cut_mg S|) ->
      exists (Js : seq {set edge G}) (m : nat),
        [/\ size Js = m,
            (forall J : {set edge G}, J \in Js -> is_tjoin T J),
            (forall e : edge G, count (fun J : {set edge G} => e \in J) Js <= 1)
          & 2 * k <= 3 * (m + c)].

(** * Extremal.conjectures.X4 -- v2 milestone X4, clean extremal wave

    This file states the first clean X4 sub-batch: finite Ramsey/Folkman rows
    and Turan/triangle-supersaturation rows whose source statements can be
    expressed with the existing finite [sgraph] vocabulary.  Asymptotic
    density rows and rows needing heavier paper-local primitives are deferred. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import sgraph minor.
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local extremal vocabulary *******************************************)

Definition x4_edge_count (G : sgraph) : nat :=
  #|[set p : G * G |
      (p.1 -- p.2) && ((enum_rank p.1) < (enum_rank p.2))%N]|.

Definition x4_mono_complete_copy
    (m q : nat) (H : sgraph) (col : 'I_m -> 'I_m -> 'I_q) : Prop :=
  exists c : 'I_q, exists f : H -> 'I_m,
    injective f /\ forall x y : H, x -- y -> col (f x) (f y) = c.

Definition x4_complete_arrow (q m : nat) (H : sgraph) : Prop :=
  forall col : 'I_m -> 'I_m -> 'I_q,
    (forall x y : 'I_m, col x y = col y x) ->
    @x4_mono_complete_copy m q H col.

Definition x4_red_blue_copy
    (m : nat) (Hred Hblue : sgraph) (col : rel 'I_m) : Prop :=
  (exists f : Hred -> 'I_m,
     injective f /\ forall x y : Hred, x -- y -> col (f x) (f y) = true) \/
  (exists f : Hblue -> 'I_m,
     injective f /\ forall x y : Hblue, x -- y -> col (f x) (f y) = false).

Definition x4_two_colour_arrow (m : nat) (Hred Hblue : sgraph) : Prop :=
  forall col : rel 'I_m, symmetric col -> x4_red_blue_copy Hred Hblue col.

Definition x4_ramsey_two (Hred Hblue : sgraph) (r : nat) : Prop :=
  x4_two_colour_arrow r Hred Hblue /\
  forall m : nat, x4_two_colour_arrow m Hred Hblue -> r <= m.

Definition x4_mono_subgraph_copy
    (q : nat) (G H : sgraph) (col : G -> G -> 'I_q) : Prop :=
  exists c : 'I_q, exists f : H -> G,
    injective f /\
    forall x y : H, x -- y -> (f x -- f y) /\ col (f x) (f y) = c.

Definition x4_graph_arrow (q : nat) (G H : sgraph) : Prop :=
  forall col : G -> G -> 'I_q,
    (forall x y : G, col x y = col y x) ->
    @x4_mono_subgraph_copy q G H col.

Definition x4_palette_on
    (V C : finType) (col : V -> V -> C) (S : {set V}) : {set C} :=
  [set c : C | [exists x : V, [exists y : V,
      [&& x \in S, y \in S, x != y & col x y == c]]]].

Definition x4_edge_in_mono_triangle
    (n : nat) (col : rel 'I_n) (x y : 'I_n) : bool :=
  [exists z : 'I_n,
      [&& z != x, z != y, col x z == col x y & col y z == col x y]].

Definition x4_edges_not_in_mono_triangle (n : nat) (col : rel 'I_n) : nat :=
  #|[set p : 'I_n * 'I_n |
      ((val p.1) < (val p.2))%N && ~~ x4_edge_in_mono_triangle col p.1 p.2]|.

Section X4Book.
Variables (k n : nat).

Definition x4_book_rel : rel ('I_k + 'I_n) :=
  fun x y =>
    match x, y with
    | inl a, inl b => a != b
    | inl _, inr _ => true
    | inr _, inl _ => true
    | inr _, inr _ => false
    end.

Lemma x4_book_rel_sym : symmetric x4_book_rel.
Proof. by case=> a; case=> b //=; rewrite eq_sym. Qed.

Lemma x4_book_rel_irrefl : irreflexive x4_book_rel.
Proof. by case=> a //=; rewrite eqxx. Qed.

Definition x4_book_graph : sgraph :=
  SGraph x4_book_rel_sym x4_book_rel_irrefl.

End X4Book.

Definition x4_K_free (G : sgraph) (t : nat) : Prop := ~ subgraph 'K_t G.

Definition x4_turan_number (r n m : nat) : Prop :=
  (exists G : sgraph,
     [/\ #|G| = n, x4_edge_count G = m & x4_K_free G (r.+1)]) /\
  forall m' : nat,
    (exists G : sgraph,
       [/\ #|G| = n, x4_edge_count G = m' & x4_K_free G (r.+1)]) ->
    m' <= m.

Definition x4_degree_sum (G : sgraph) (S : {set G}) : nat :=
  \sum_(v in S) #|N(v)|.

Definition x4_triangle_set (G : sgraph) (T : {set G}) : bool :=
  (#|T| == 3) && cliqueb T.

Definition x4_triangle_count (G : sgraph) : nat :=
  #|[set T : {set G} | x4_triangle_set T]|.

Definition x4_consecutive_in_cycle (G : sgraph) (c : seq G) (u v : G) : bool :=
  ((u, v) \in zip c (rot 1 c)) || ((v, u) \in zip c (rot 1 c)).

Definition x4_edge_in_c5 (G : sgraph) (x y : G) : bool :=
  [exists c : 5.-tuple G,
      [&& ucycleb (--) (val c), x \in val c, y \in val c
        & x4_consecutive_in_cycle (val c) x y]].

Definition x4_c5_edge_count (G : sgraph) : nat :=
  #|[set p : G * G |
      [&& (p.1 -- p.2), ((enum_rank p.1) < (enum_rank p.2))%N
        & x4_edge_in_c5 p.1 p.2]]|.

Definition x4_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

Definition x4_at_most_one_triangle_edge (G : sgraph) (F : {set {set G}}) : Prop :=
  F \subset x4_edge_set G /\
  forall T : {set G},
    x4_triangle_set T -> #|[set e in F | e \subset T]| <= 1.

Definition x4_hits_every_triangle (G : sgraph) (F : {set {set G}}) : Prop :=
  F \subset x4_edge_set G /\
  forall T : {set G},
    x4_triangle_set T -> exists e : {set G}, e \in F /\ e \subset T.

Definition x4_alpha1 (G : sgraph) (a : nat) : Prop :=
  (exists F : {set {set G}}, x4_at_most_one_triangle_edge F /\ #|F| = a) /\
  forall b : nat,
    (exists F : {set {set G}}, x4_at_most_one_triangle_edge F /\ #|F| = b) ->
    b <= a.

Definition x4_tau1 (G : sgraph) (t : nat) : Prop :=
  (exists F : {set {set G}}, x4_hits_every_triangle F /\ #|F| = t) /\
  forall b : nat,
    (exists F : {set {set G}}, x4_hits_every_triangle F /\ #|F| = b) ->
    t <= b.

(** Corpus row: erdos:551
    Site: none
    Review: none
    English statement: (Erdos problem #551)
      For all k >= n >= 3 except the single case n = k = 3, the two-colour Ramsey number of
      the k-cycle against the complete graph on n vertices is exactly (k-1)(n-1) + 1.
    Definitions: [x4_ramsey_two Hred Hblue r] - r is the least m such that every symmetric
      2-colouring of the edges of the complete graph on m vertices contains a copy of Hred in
      the first colour or a copy of Hblue in the second, copies being injective maps sending
      edges to monochromatic pairs ([x4_two_colour_arrow], [x4_red_blue_copy]) (X4.v);
      [cycle_graph k] - GTBase; ['K_n] - complete graph (coq-graph-theory).
    Notes: the exception of the source is written [n != 3 \/ k != 3]. Both subtractions are
      nat subtractions, harmless because n >= 3 and k >= n. *)
Definition cycle_clique_ramsey_formula_statement : Prop :=
  forall k n : nat,
    n <= k -> 3 <= n -> (n != 3 \/ k != 3) ->
    x4_ramsey_two (cycle_graph k) 'K_n ((k - 1) * (n - 1) + 1).

(** Corpus row: erdos:556
    Site: none
    Review: none
    English statement: (Erdos problem #556)
      There is a threshold n0 such that for every n >= n0, every symmetric 3-colouring of the
      edges of the complete graph on 4n - 3 vertices contains a monochromatic copy of the
      n-cycle; that is, R_3(C_n) <= 4n - 3 for all large n.
    Definitions: [x4_complete_arrow q m H] - every symmetric colouring of the pairs of 'I_m
      by 'I_q admits a colour c and an injective map H -> 'I_m sending every edge of H to a
      pair of colour c ([x4_mono_complete_copy]) (X4.v); [cycle_graph n] - GTBase.
    Notes: the solved bound R_3(C_n) <= 4n-3 (Kohayakawa-Simonovits-Skokan et al.) holds only
      for n sufficiently large; it is FALSE for small n (e.g. n = 3, where C_3 = K_3 and
      R_3(K_3) = 17 > 9 = 4*3-3). Hence the faithful encoding of the asymptotic theorem is
      "there is a threshold n0 beyond which the bound holds", which is weaker than the
      literal source text. *)
Definition three_colour_cycle_ramsey_bound_statement : Prop :=
  exists n0 : nat, forall n : nat, n0 <= n ->
    x4_complete_arrow 3 (4 * n - 3) (cycle_graph n).

(** Corpus row: erdos:582
    Site: none
    Review: none
    English statement: (Erdos problem #582)
      There exists a finite graph G containing no K_4 such that every symmetric 2-colouring
      of the edges of G contains a monochromatic triangle.
    Definitions: [x4_K_free G t] - K_t does not embed in G, using coq-graph-theory's
      [subgraph] (X4.v); [x4_graph_arrow q G H] - every symmetric q-colouring of the pairs of
      vertices of G admits a colour and an injective map H -> G sending edges of H to edges
      of G of that colour ([x4_mono_subgraph_copy]) (X4.v).
    Notes: the colouring is defined on all pairs of vertices of G, but only its values on
      edges of G matter, since the monochromatic copy is required to use edges of G. *)
Definition folkman_k4_free_triangle_arrow_statement : Prop :=
  exists G : sgraph, x4_K_free G 4 /\ x4_graph_arrow 2 G 'K_3.

(** Corpus row: erdos:617
    Site: none
    Review: none
    English statement: (Erdos problem #617)
      For every r >= 3 and every symmetric r-colouring of the edges of the complete graph on
      r^2 + 1 vertices there is a set S of r+1 vertices such that fewer than r colours occur
      on the edges inside S, i.e. at least one colour is missing on the induced K_{r+1}.
    Definitions: [x4_palette_on col S] - the set of colours realised by col on ordered pairs
      of distinct vertices of S (X4.v).
    Notes: the colouring is a function on ordered pairs constrained to be symmetric, and the
      palette ignores the diagonal, so colours of "loops" do not count. *)
Definition missing_colour_complete_edge_colouring_statement : Prop :=
  forall r : nat, 3 <= r ->
    forall col : 'I_(r * r + 1) -> 'I_(r * r + 1) -> 'I_r,
      (forall x y : 'I_(r * r + 1), col x y = col y x) ->
      exists S : {set 'I_(r * r + 1)},
        #|S| = r.+1 /\ #|x4_palette_on col S| < r.

(** Corpus row: erdos:639
    Site: none
    Review: none
    English statement: (Erdos problem #639)
      For every n and every symmetric 2-colouring of the edges of the complete graph on n
      vertices, the number of edges lying in no monochromatic triangle is at most n^2/4
      (written 4 * count <= n * n).
    Definitions: [x4_edges_not_in_mono_triangle n col] - the number of ordered pairs (x,y) of
      'I_n with x < y such that no third vertex z makes the triangle x,y,z monochromatic in
      col ([x4_edge_in_mono_triangle]) (X4.v).
    Notes: the pairs are counted once each via the [val p.1 < val p.2] guard, so the count is
      over unordered edges of the complete graph. *)
Definition monochromatic_triangle_edge_bound_statement : Prop :=
  forall n : nat, forall col : rel 'I_n,
    symmetric col ->
    4 * x4_edges_not_in_mono_triangle col <= n * n.

(** Corpus row: erdos:924
    Site: none
    Review: none
    English statement: (Erdos problem #924)
      For all k >= 2 and l >= 3 there is a finite graph G containing no K_{l+1} such that
      every symmetric k-colouring of the edges of G contains a monochromatic copy of K_l.
    Definitions: [x4_K_free G t] - K_t does not embed in G (X4.v); [x4_graph_arrow q G H] -
      every symmetric q-colouring of the pairs of vertices of G yields a monochromatic copy
      of H on edges of G (X4.v).
    Notes: this is the general Folkman statement; erdos:582 above is the case k = 2, l = 3. *)
Definition folkman_clique_arrow_statement : Prop :=
  forall k l : nat, 2 <= k -> 3 <= l ->
    exists G : sgraph,
      x4_K_free G (l.+1) /\ x4_graph_arrow k G 'K_l.

(** Corpus row: studies:std_thomason_s_conjecture_on_book_ramsey_numbers
    Site: none
    Review: none
    English statement: (Thomason, Thomason's Conjecture on Book Ramsey Numbers)
      For all n, k >= 1, every symmetric 2-colouring of the edges of the complete graph on
      2^k * (n + k - 2) + 2 vertices contains a monochromatic copy of the book B_n^(k) (a
      k-clique spine all of whose vertices are joined to each of n independent pages); that
      is, r(B_n^(k)) <= 2^k(n+k-2) + 2.
    Definitions: [x4_book_graph k n] - the book graph on 'I_k + 'I_n whose spine 'I_k is a
      clique, whose pages 'I_n are pairwise non-adjacent, and with every spine vertex
      adjacent to every page (X4.v); [x4_complete_arrow q m H] - every symmetric q-colouring
      of the pairs of 'I_m contains a monochromatic copy of H (X4.v).
    Notes: this row comes from the studies slice of the corpus, which has no site or review
      page. [n + k - 2] is nat subtraction, harmless in the stated range 0 < n, 0 < k (it
      truncates to 0 only at n = k = 1, where the bound is still correct). *)
Definition thomason_book_ramsey_bound_statement : Prop :=
  forall n k : nat, 0 < n -> 0 < k ->
    x4_complete_arrow 2 (2 ^ k * (n + k - 2) + 2) (x4_book_graph k n).

(** Corpus row: erdos:904
    Site: none
    Review: none
    English statement: (Erdos problem #904)
      For all r >= 2 and n >= r, if t_r(n) is the Turan number (the maximum number of edges
      of a K_{r+1}-free graph on n vertices) then every graph G on n vertices with at least
      t_r(n) edges has a clique S on r vertices whose degree sum satisfies
      n * sum_{x in S} d(x) >= 2 * r * e(G), i.e. sum d(x) >= 2 r e(G) / n.
    Definitions: [x4_turan_number r n m] - m is the maximum edge count of a K_{r+1}-free
      graph on n vertices (X4.v); [x4_K_free G t] - K_t does not embed in G (X4.v);
      [x4_degree_sum G S] - the sum of the degrees of the vertices of S (X4.v);
      [x4_edge_count] - number of edges (X4.v); [clique] - coq-graph-theory.
    Notes: the Turan number is passed as a parameter constrained by the extremal predicate
      rather than computed. The division by n is cleared by multiplying through. *)
Definition turan_degree_sum_clique_statement : Prop :=
  forall r n tr : nat, 2 <= r -> r <= n ->
    x4_turan_number r n tr ->
    forall G : sgraph, #|G| = n -> tr <= x4_edge_count G ->
      exists S : {set G},
        #|S| = r /\ clique S /\
        2 * r * x4_edge_count G <= n * x4_degree_sum S.

(** Corpus row: erdos:905
    Site: none
    Review: none
    English statement: (Erdos problem #905)
      Every graph G on n vertices with more than n^2/4 edges (written n * n < 4 * e(G)) has
      an edge x-y whose endpoints have at least n/6 common neighbours (written
      n <= 6 * |N(x) inter N(y)|), i.e. an edge lying in at least n/6 triangles.
    Definitions: [x4_edge_count] - number of edges (X4.v); [N(x)] - neighbourhood
      (coq-graph-theory).
    Notes: "an edge in at least n/6 triangles" is encoded as the number of common neighbours
      of its two endpoints, which is exactly the number of triangles through that edge. Both
      inequalities are cross-multiplied to stay in nat. *)
Definition book_triangle_edge_statement : Prop :=
  forall G : sgraph, forall n : nat,
    #|G| = n -> n * n < 4 * x4_edge_count G ->
    exists x y : G, x -- y /\ n <= 6 * #|N(x) :&: N(y)|.

(** Corpus row: erdos:608
    Site: none
    Review: none
    English statement: (Erdos problem #608)
      Every graph G on n vertices with more than n^2/4 edges has at least (2/9) * n^2 edges
      that lie on a 5-cycle (written 2 * n * n <= 9 * c5count).
    Definitions: [x4_c5_edge_count G] - the number of unordered edges of G (counted via the
      [enum_rank p.1 < enum_rank p.2] guard) that lie on some 5-cycle,
      [x4_edge_in_c5] using a 5-tuple forming a uniform cycle ([ucycleb]) and
      [x4_consecutive_in_cycle] (X4.v); [x4_edge_count] (X4.v).
    Notes: both inequalities are cross-multiplied to stay in nat. A 5-cycle is witnessed by a
      5-tuple of vertices; [ucycleb] forces its entries to be distinct. *)
Definition c5_edge_count_above_turan_statement : Prop :=
  forall G : sgraph, forall n : nat,
    #|G| = n -> n * n < 4 * x4_edge_count G ->
    2 * n * n <= 9 * x4_c5_edge_count G.

(** Corpus row: erdos:621
    Site: none
    Review: none
    English statement: (Erdos problem #621)
      For every graph G on n vertices, alpha_1(G) + tau_1(G) <= n^2/4, where alpha_1(G) is
      the maximum size of an edge set containing at most one edge of every triangle and
      tau_1(G) is the minimum size of an edge set containing at least one edge of every
      triangle (written 4 * (a + t) <= n * n).
    Definitions: [x4_alpha1 G a] and [x4_tau1 G t] - the maximum resp. minimum above, over
      subsets of [x4_edge_set G] (the edges as 2-element vertex sets), via
      [x4_at_most_one_triangle_edge] and [x4_hits_every_triangle] (X4.v);
      [x4_triangle_set T] - T is a 3-element clique (X4.v).
    Notes: edges are 2-element vertex sets, so "an edge of the triangle T" is a member of F
      included in T. The inequality is cross-multiplied to stay in nat. *)
Definition triangle_alpha_tau_bound_statement : Prop :=
  forall G : sgraph, forall n a t : nat,
    #|G| = n -> x4_alpha1 G a -> x4_tau1 G t ->
    4 * (a + t) <= n * n.

(** Corpus row: erdos:1010
    Site: none
    Review: none
    English statement: (Erdos problem #1010)
      For every graph G on n vertices and every t < floor(n/2): if G has exactly
      floor(n^2/4) + t edges then G contains at least t * floor(n/2) triangles.
    Definitions: [x4_edge_count] - number of edges (X4.v); [x4_triangle_count G] - the number
      of 3-element cliques of G ([x4_triangle_set]) (X4.v).
    Notes: [n * n %/ 4] parses as [(n * n) %/ 4], i.e. floor(n^2/4). The edge count is an
      exact equality, as in the source. *)
Definition triangle_supersaturation_statement : Prop :=
  forall G : sgraph, forall n t : nat,
    #|G| = n -> t < n %/ 2 ->
    x4_edge_count G = n * n %/ 4 + t ->
    t * (n %/ 2) <= x4_triangle_count G.

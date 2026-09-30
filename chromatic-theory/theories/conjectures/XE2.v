(** * Chromatic.conjectures.XE2 -- Erdős solved clean/bounded rows *)

From Chromatic.conjectures Require Import XE1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local XE2 vocabulary ************************************************)

Definition xe2_odd_cycle_lengths_bounded (G : sgraph) (k : nat) : Prop :=
  exists L : seq nat,
    uniq L /\ size L <= k /\
    forall c : seq G, xe1_cycle c -> odd (size c) -> size c \in L.

Definition xe2_ab_choosable (G : sgraph) (a b : nat) : Prop :=
  forall (C : finType) (L : G -> {set C}),
    (forall v : G, #|L v| = a) ->
    exists S : G -> {set C},
      (forall v : G, S v \subset L v /\ #|S v| = b) /\
      forall x y : G, x -- y -> [disjoint S x & S y].

Definition xe2_complement_rel (G : sgraph) : rel G :=
  fun x y => (x != y) && ~~ (x -- y).

Lemma xe2_complement_sym (G : sgraph) : symmetric (@xe2_complement_rel G).
Proof. by move=> x y; rewrite /xe2_complement_rel eq_sym sgP. Qed.

Lemma xe2_complement_irrefl (G : sgraph) : irreflexive (@xe2_complement_rel G).
Proof. by move=> x; rewrite /xe2_complement_rel eqxx. Qed.

Definition xe2_complement_graph (G : sgraph) : sgraph :=
  SGraph (@xe2_complement_sym G) (@xe2_complement_irrefl G).

Definition xe2_sqrt_lower (n s : nat) : Prop :=
  s ^ 2 <= n /\ forall t : nat, t ^ 2 <= n -> t <= s.

Definition xe2_above_half_plus_rational_power
    (n cnum cden b : nat) : Prop :=
  n ^ (cden + 2 * cnum) < b ^ (2 * cden).

Definition xe2_cochromatic_colouring (G : sgraph) (k : nat) : Prop :=
  exists col : G -> 'I_k,
    forall i : 'I_k,
      let S := [set v : G | col v == i] in
      clique S \/ xe1_stable_set S.

Definition xe2_cochromatic_number (G : sgraph) (k : nat) : Prop :=
  xe2_cochromatic_colouring G k /\
  forall j : nat, xe2_cochromatic_colouring G j -> k <= j.

Definition xe2_max_cochromatic_on_n (n z : nat) : Prop :=
  (exists G : sgraph, #|G| = n /\ xe2_cochromatic_number G z) /\
  forall z' : nat,
    (exists G : sgraph, #|G| = n /\ xe2_cochromatic_number G z') -> z' <= z.

Definition xe2_cycle_lengths_separated (G : sgraph) (gap : nat) : Prop :=
  forall c d : seq G,
    xe1_cycle c -> xe1_cycle d -> size c != size d ->
    gap <= (size c - size d) + (size d - size c).

Definition xe2_triangles_plus_hamilton_cycle (G : sgraph) (n : nat) : Prop :=
  exists (T : 'I_n -> {set G}) (c : seq G),
    #|G| = 3 * n /\
    (forall i : 'I_n, clique (T i) /\ #|T i| = 3) /\
    (forall i j : 'I_n, i != j -> [disjoint T i & T j]) /\
    ucycle (--) c /\
    size c = 3 * n /\
    (forall v : G, v \in c) /\
    (forall (i : 'I_n) (x y : G),
        x \in T i -> y \in T i -> x != y ->
        ~~ xe1_consecutive_in_cycle c x y) /\
    forall x y : G, x -- y ->
      (exists i : 'I_n, x \in T i /\ y \in T i) \/
      xe1_consecutive_in_cycle c x y.

(** ** XE2 statements ******************************************************)

(** Corpus row: erdos:1091
    Site: none
    Review: none
    English statement: (Erdos Problems #1091)
      Two conjuncts. First, every finite simple graph with no complete subgraph on 4 vertices and
      chromatic number 4 contains an odd cycle with at least two diagonals. Second, there is an
      unbounded function f from naturals to naturals such that for every r, every graph with no
      complete subgraph on 4 vertices, chromatic number 4, and all induced subgraphs on at most r
      vertices of chromatic number at most 3, contains an odd cycle with at least f(r) diagonals.
    Definitions: [xe1_odd_cycle_with_diagonals G d] - some cycle of odd length has at least d
      diagonals (XE1.v); [xe1_cycle_diagonal_count c] - the number of adjacent vertex pairs on c
      that are not consecutive on c, counted once per unordered pair via [enum_rank] ordering
      (XE1.v); [xe1_induced_subgraph_chi_le G r b] - every vertex set of size at most r induces a
      subgraph of chromatic number at most b (XE1.v); [xe1_unbounded f] - f takes arbitrarily large
      values (XE1.v); [xe1_subgraph_of 'K_4 G] - K4 embeds in G (XE1.v).
    Notes: This row has no site or review page in the corpus, hence the literal "none" above. The
      source's two questions are formalised as a CONJUNCTION, so the statement is the affirmative
      answer to both. "f(r) tends to infinity" is weakened to [xe1_unbounded f], which does not
      require monotone divergence; the source's subgraphs on at most r vertices are read as INDUCED
      subgraphs. *)
Definition erdos_1091_statement : Prop :=
  (forall G : sgraph,
    ~ xe1_subgraph_of 'K_4 G ->
    χ([set: G]) = 4 ->
    xe1_odd_cycle_with_diagonals G 2) /\
  exists f : nat -> nat,
    xe1_unbounded f /\
    forall (r : nat) (G : sgraph),
      ~ xe1_subgraph_of 'K_4 G ->
      χ([set: G]) = 4 ->
      xe1_induced_subgraph_chi_le G r 3 ->
      xe1_odd_cycle_with_diagonals G (f r).

(** Corpus row: erdos:58
    Site: none
    Review: none
    English statement: (Erdos Problems #58)
      For every finite simple graph G and every k, if the odd cycles of G have at most k different
      lengths, then the chromatic number of G is at most 2k+2, and it equals 2k+2 exactly when G
      contains a complete subgraph on 2k+2 vertices.
    Definitions: [xe2_odd_cycle_lengths_bounded G k] - there is a duplicate-free list of at most k
      naturals containing the length of every odd cycle of G (this file); [xe1_cycle c] - a [ucycle]
      of size greater than 2 (XE1.v); [xe1_subgraph_of H G] - H embeds into G by an injective
      adjacency-preserving map (XE1.v).
    Notes: This row has no site or review page in the corpus, hence the literal "none" above. The
      equality case is stated as an if-and-only-if, as in the source. Cycles are lists of vertices,
      so their length is the number of vertices, and the [2 < size] guard of [xe1_cycle] rules out
      the degenerate closed walks. *)
Definition erdos_58_statement : Prop :=
  forall (G : sgraph) (k : nat),
    xe2_odd_cycle_lengths_bounded G k ->
    χ([set: G]) <= 2 * k + 2 /\
    (χ([set: G]) = 2 * k + 2 <-> xe1_subgraph_of 'K_(2 * k + 2) G).

(** Corpus row: erdos:630
    Site: none
    Review: none
    English statement: (Erdos Problems #630)
      Every finite simple graph that is planar and bipartite is 3-choosable: for every assignment of
      lists of at least 3 colours to its vertices there is a proper colouring picking each vertex's
      colour from its own list.
    Definitions: [wagner_planar G] - G has neither K5 nor K3,3 as a minor, which by Wagner's
      theorem is planarity (GTBase base/theories/base.v); [bipartite G] - there is a 2-colouring
      with no monochromatic edge (base.v); [choosable G 3] - every list assignment with all lists of
      size at least 3 admits a proper colouring from the lists (base.v).
    Notes: This row has no site or review page in the corpus, hence the literal "none" above. The
      corpus row is a QUESTION; the Rocq body is its affirmative reading. [choosable] requires lists
      of size AT LEAST 3, which is equivalent to the usual definition with lists of size exactly 3. *)
Definition erdos_630_statement : Prop :=
  forall G : sgraph,
    wagner_planar G -> bipartite G -> choosable G 3.

(** Corpus row: erdos:632
    Site: none
    Review: none
    English statement: (Erdos Problems #632)
      For every finite simple graph G, all a and b, and every m >= 1, if G is (a,b)-choosable then G
      is (a*m, b*m)-choosable.
    Definitions: [xe2_ab_choosable G a b] - for every assignment of lists of exactly a colours
      from an arbitrary finite palette there are b-element subsets of the lists, one per vertex,
      that are disjoint for adjacent vertices (this file).
    Notes: This row has no site or review page in the corpus, hence the literal "none" above.
      Lists have size exactly a and the chosen subsets size exactly b, as in the source. *)
Definition erdos_632_statement : Prop :=
  forall (G : sgraph) (a b m : nat),
    1 <= m ->
    xe2_ab_choosable G a b ->
    xe2_ab_choosable G (a * m) (b * m).

(** Corpus row: erdos:751
    Site: none
    Review: none
    English statement: (Erdos Problems #751)
      For all gap and g there exists a finite simple graph G with chromatic number exactly 4, girth
      at least g, and such that any two cycles of G of different lengths have lengths differing by
      at least gap.
    Definitions: [xe2_cycle_lengths_separated G gap] - for any two cycles of different sizes, the
      sum of the two truncated differences of their sizes, which is the absolute difference, is at
      least gap (this file); [xe1_cycle] (XE1.v); [girth_geq] (GTBase base/theories/base.v).
    Notes: This row has no site or review page in the corpus, hence the literal "none" above. The
      source asks two questions, whether the minimum gap between consecutive cycle lengths can be
      arbitrarily large and whether this can happen with large girth; the Rocq body answers both at
      once by quantifying over gap and g together. Separation of ALL pairs of distinct cycle lengths
      is equivalent to separation of consecutive ones. *)
Definition erdos_751_statement : Prop :=
  forall gap g : nat,
    exists G : sgraph,
      χ([set: G]) = 4 /\
      girth_geq G g /\
      xe2_cycle_lengths_separated G gap.

(** Corpus row: erdos:753
    Site: none
    Review: none
    English statement: (Erdos Problems #753)
      There is a positive rational constant c, given as a pair of positive naturals cnum and cden
      with c = cnum/cden, such that for every finite simple graph G on n > 0 vertices with choice
      number chG and whose complement has choice number chGc, the sum chG + chGc exceeds n raised to
      the power 1/2 + c.
    Definitions: [xe2_above_half_plus_rational_power n cnum cden b] - the inequality n^(cden +
      2*cnum) < b^(2*cden), which is the cross-multiplied, root-free form of b > n^(1/2 + cnum/cden)
      (this file); [xe2_complement_graph G] - the complement graph (this file); [is_choice_number]
      (GTBase base/theories/base.v).
    Notes: This row has no site or review page in the corpus, hence the literal "none" above. The
      real constant c > 0 of the source is restricted to a positive RATIONAL, represented by its
      numerator and denominator, so that the inequality can be stated over the naturals by raising
      both sides to the power 2*cden; this is no loss, since any real c admits a smaller positive
      rational. *)
Definition erdos_753_statement : Prop :=
  exists cnum cden : nat,
    0 < cnum /\ 0 < cden /\
    forall (G : sgraph) (n chG chGc : nat),
      #|G| = n ->
      0 < n ->
      is_choice_number G chG ->
      is_choice_number (xe2_complement_graph G) chGc ->
      xe2_above_half_plus_rational_power n cnum cden (chG + chGc).

(** Corpus row: erdos:758
    Site: none
    Review: none
    English statement: (Erdos Problems #758)
      The maximum cochromatic number over all finite simple graphs on 12 vertices is 4; that is,
      some graph on 12 vertices has cochromatic number 4 and no graph on 12 vertices has a larger
      one.
    Definitions: [xe2_max_cochromatic_on_n n z] - some graph on n vertices has cochromatic number
      z, and every cochromatic number realised on n vertices is at most z (this file);
      [xe2_cochromatic_number G k] - k is the least number of colour classes each inducing a clique
      or a stable set (this file); [xe1_stable_set] (XE1.v).
    Notes: This row has no site or review page in the corpus, hence the literal "none" above. The
      source asks to determine z(n) for small n and in particular whether z(12) = 4; the Rocq body
      encodes exactly the special case z(12) = 4, not the general determination. *)
Definition erdos_758_statement : Prop :=
  xe2_max_cochromatic_on_n 12 4.

(** Corpus row: erdos:762
    Site: none
    Review: none
    English statement: (Erdos Problems #762)
      Every finite simple graph G containing no complete subgraph on 5 vertices and whose
      cochromatic number z is at least 4 satisfies chi(G) <= z + 2.
    Definitions: [xe2_cochromatic_number G z] - z is the least number of colour classes each of
      which induces a clique or a stable set (this file); [xe1_subgraph_of 'K_5 G] - K5 embeds into
      G (XE1.v).
    Notes: This row has no site or review page in the corpus, hence the literal "none" above. The
      corpus row is a QUESTION; the Rocq body is its affirmative reading. "Has no K_5" is encoded as
      the negation of a subgraph embedding, which for complete graphs coincides with omega(G) < 5. *)
Definition erdos_762_statement : Prop :=
  forall (G : sgraph) (z : nat),
    ~ xe1_subgraph_of 'K_5 G ->
    xe2_cochromatic_number G z ->
    4 <= z ->
    χ([set: G]) <= z + 2.

(** Corpus row: erdos:842
    Site: none
    Review: none
    English statement: (Erdos Problems #842)
      Every finite simple graph on 3n vertices that consists of n pairwise disjoint triangles
      together with a Hamiltonian cycle all of whose edges are new, and which has no other edges,
      has chromatic number at most 3.
    Definitions: [xe2_triangles_plus_hamilton_cycle G n] - there are n pairwise disjoint 3-element
      cliques covering the 3n vertices and a [ucycle] of length 3n through all vertices, such that
      no two vertices of the same triangle are consecutive on the cycle and every edge of G is
      either inside a triangle or consecutive on the cycle (this file); [xe1_consecutive_in_cycle]
      (XE1.v).
    Notes: This row has no site or review page in the corpus, hence the literal "none" above. The
      corpus row is a QUESTION; the Rocq body is its affirmative reading. "With all new edges" is
      captured by the clause forbidding two vertices of one triangle from being consecutive on the
      Hamiltonian cycle, and the final clause makes the edge set exactly the triangle edges plus the
      cycle edges. *)
Definition erdos_842_statement : Prop :=
  forall (n : nat) (G : sgraph),
    xe2_triangles_plus_hamilton_cycle G n ->
    χ([set: G]) <= 3.

(** Corpus row: erdos:922
    Site: none
    Review: none
    English statement: (Erdos Problems #922)
      For every k and every finite simple graph G such that every induced subgraph, given by a
      vertex set S, contains a stable subset A of S with 2*|A| + k >= |S|, i.e. |A| >= (|S| - k)/2,
      the chromatic number of G is at most k + 2.
    Definitions: [xe1_stable_set A] - no two vertices of A are adjacent (XE1.v).
    Notes: This row has no site or review page in the corpus, hence the literal "none" above. The
      source's "every subgraph H contains an independent set of size at least (n-k)/2" is read as
      every INDUCED subgraph, which is the standard reading since adding edges only shrinks
      independent sets; the inequality is cleared of the division to avoid nat rounding, and 2*|A| +
      k >= |S| is exactly |A| >= (|S| - k)/2 over the rationals. *)
Definition erdos_922_statement : Prop :=
  forall (k : nat) (G : sgraph),
    (forall S : {set G}, exists A : {set G},
        A \subset S /\ xe1_stable_set A /\
        2 * #|A| + k >= #|S|) ->
    χ([set: G]) <= k + 2.

(** Corpus row: erdos:923
    Site: none
    Review: none
    English statement: (Erdos Problems #923)
      For every k there is a bound f such that every finite simple graph with chromatic number at
      least f contains a triangle-free subgraph with chromatic number at least k.
    Definitions: [xe1_subgraph_of H G] - H embeds into G by an injective adjacency-preserving map,
      so the subgraph need not be induced (XE1.v); [triangle_free] (GTBase base/theories/base.v).
    Notes: This row has no site or review page in the corpus, hence the literal "none" above. The
      corpus row is a QUESTION; the Rocq body is its affirmative reading, with the bound f chosen
      after k and before G. *)
Definition erdos_923_statement : Prop :=
  forall k : nat, exists f : nat,
    forall G : sgraph,
      f <= χ([set: G]) ->
      exists H : sgraph,
        xe1_subgraph_of H G /\ triangle_free H /\ k <= χ([set: H]).

(** * Hypergraph.conjectures.X6 -- v2 milestone X6, clean hypergraph rows *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local hypergraph vocabulary *****************************************)

Definition x6_uniform (T : finType) (E : {set {set T}}) (r : nat) : Prop :=
  forall e : {set T}, e \in E -> #|e| = r.

Definition x6_r_partite_uniform
    (T : finType) (r : nat) (part : T -> 'I_r) (E : {set {set T}}) : Prop :=
  forall e : {set T}, e \in E ->
    forall j : 'I_r, #|[set v in e | part v == j]| = 1.

Definition x6_matching (T : finType) (M E : {set {set T}}) : Prop :=
  M \subset E /\
  {in M &, forall e f : {set T}, e != f -> [disjoint e & f]}.

Definition x6_matching_number (T : finType) (E : {set {set T}}) (nu : nat) : Prop :=
  (exists M : {set {set T}}, x6_matching M E /\ #|M| = nu) /\
  (forall M : {set {set T}}, x6_matching M E -> #|M| <= nu).

Definition x6_no_k_matching (T : finType) (E : {set {set T}}) (k : nat) : Prop :=
  forall M : {set {set T}}, x6_matching M E -> #|M| < k.

Definition x6_extremal_no_k_matching (n r k m : nat) : Prop :=
  (exists (T : finType) (E : {set {set T}}),
     [/\ #|T| = n, x6_uniform E r, #|E| = m & x6_no_k_matching E k]) /\
  forall m' : nat,
    (exists (T : finType) (E : {set {set T}}),
       [/\ #|T| = n, x6_uniform E r, #|E| = m' & x6_no_k_matching E k]) ->
    m' <= m.

Definition x6_delete_vertices (T : finType) (E : {set {set T}}) (X : {set T})
  : {set {set T}} :=
  [set e in E | [disjoint e & X]].

Definition x6_edges_on (T : finType) (E : {set {set T}}) (S : {set T}) : nat :=
  #|[set e in E | e \subset S]|.

Definition x6_hg_degree (T : finType) (E : {set {set T}}) (v : T) : nat :=
  #|[set e in E | v \in e]|.

Definition x6_proper_coloring
    (T C : finType) (E : {set {set T}}) (col : T -> C) : Prop :=
  forall e : {set T}, e \in E ->
    exists x y : T, [/\ x \in e, y \in e & col x != col y].

Definition x6_chromatic_number (T : finType) (E : {set {set T}}) (k : nat) : Prop :=
  (exists col : T -> 'I_k, x6_proper_coloring E col) /\
  forall k' : nat, (exists col : T -> 'I_k', x6_proper_coloring E col) -> k <= k'.

Definition x6_vertex_delete (T : finType) (E : {set {set T}}) (v : T)
  : {set {set T}} :=
  [set e in E | v \notin e].

Definition x6_edge_delete (T : finType) (E : {set {set T}}) (e : {set T})
  : {set {set T}} :=
  E :\ e.

Definition x6_chromatic_edge_critical (T : finType) (E : {set {set T}}) (k : nat)
  : Prop :=
  x6_chromatic_number E k /\
  forall e : {set T}, e \in E -> x6_chromatic_number (x6_edge_delete E e) k.-1.

(** ** X6 statements *******************************************************)

(** Corpus row: studies:std_lov_sz_conjecture_on_r_partite_hypergraph_matchi
    Site: none
    Review: none
    English statement: (Lovasz, conjecture on r-partite hypergraph matchings)
      Every r-partite r-uniform hypergraph with r at least 2 and at least one hyperedge
      contains r-1 vertices whose deletion strictly reduces the matching number.
    Definitions: [x6_r_partite_uniform part E] - every hyperedge meets each of the r parts, given
      by the vertex map part, in exactly one vertex (hypergraph-theory/theories/conjectures/X6.v);
      [x6_matching M E] - M is a subfamily of E whose hyperedges are pairwise disjoint (same
      file); [x6_matching_number E nu] - nu is attained by some matching and bounds the size of
      every matching (same file); [x6_delete_vertices E X] - the hyperedges of E that avoid X,
      i.e. the hypergraph obtained by deleting the vertices of X (same file).
    Notes: r-uniformity follows from meeting each part exactly once, so it is not a separate
      hypothesis.  The guards [1 < r] and [E != set0] are non-vacuity guards added on top of the
      source text: the source says "with at least one edge", which is [E != set0], while
      [1 < r] excludes r <= 1, where deleting r - 1 = 0 vertices could not reduce anything.
      The conclusion asks the deleted set to have exactly r-1 vertices.  The corpus records this
      row as open, but the sibling arXiv row of Clow, Haxell and Mohar is a counterexample to
      it; the body is the faithful reading of the row as recorded (the statement leg tracks
      faithfulness, not truth). *)
Definition lovasz_r_partite_matching_deletion_statement : Prop :=
  forall (r : nat) (T : finType) (part : T -> 'I_r) (E : {set {set T}})
         (nu : nat),
    1 < r ->
    E != set0 ->
    x6_r_partite_uniform part E ->
    x6_matching_number E nu ->
    exists X : {set T}, #|X| = r - 1 /\
      exists nu' : nat,
        x6_matching_number (x6_delete_vertices E X) nu' /\ nu' < nu.

(** Corpus row: arxiv:2505.05339#02
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2505.05339__02/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2505.05339__02.json
    English statement: (Clow, Haxell and Mohar 2025, "A Counterexample to a Conjecture of
      Lovasz", Conjecture 4.3)
      For every r-partite r-uniform hypergraph with r at least 2 and at least one hyperedge
      there is a k with 1 <= k <= r-1 such that the hypergraph contains k(r-1) vertices whose
      deletion reduces the matching number by at least k.
    Definitions: [x6_r_partite_uniform part E], [x6_matching M E], [x6_matching_number E nu],
      [x6_delete_vertices E X] - as in the previous row (hypergraph-theory/theories/conjectures/X6.v).
    Notes: "reduces the matching number by at least k" is stated without subtraction, as
      nu' + k <= nu where nu' is the matching number after deletion.  The guards [1 < r] and
      [E != set0] are non-vacuity guards not present in the source text; without a hyperedge
      the matching number is 0 and nothing can be reduced.  This is the proposed weakening of
      the (now disproved) Lovasz conjecture of the previous row that still implies Ryser's
      conjecture. *)
Definition r_partite_matching_deletion_tradeoff_statement : Prop :=
  forall (r : nat) (T : finType) (part : T -> 'I_r) (E : {set {set T}})
         (nu : nat),
    1 < r ->
    E != set0 ->
    x6_r_partite_uniform part E ->
    x6_matching_number E nu ->
    exists (k : nat) (X : {set T}),
      1 <= k /\ k <= r - 1 /\
      #|X| = k * (r - 1) /\
      exists nu' : nat,
        x6_matching_number (x6_delete_vertices E X) nu' /\ nu' + k <= nu.

(** Corpus row: erdos:1020
    Site: none
    Review: none
    English statement: (Erdos problem #1020, the Erdos matching conjecture)
      Let f(n; r, k) be the maximum number of hyperedges of an r-uniform hypergraph on n
      vertices containing no k pairwise disjoint hyperedges.  For all r at least 3, k at least 1
      and n at least rk-1, f(n; r, k) is the larger of the binomial coefficient (rk-1 choose r)
      and (n choose r) minus (n-k+1 choose r).
    Definitions: [x6_uniform E r] - every hyperedge has exactly r vertices (hypergraph-theory/theories/conjectures/X6.v);
      [x6_matching M E] - a subfamily of pairwise disjoint hyperedges (same file);
      [x6_no_k_matching E k] - every matching of E has fewer than k hyperedges (same file);
      [x6_extremal_no_k_matching n r k m] - m is attained by some r-uniform hypergraph on n
      vertices with no k pairwise disjoint hyperedges, and bounds the hyperedge count of every
      such hypergraph (same file).
    Notes: the maximum f(n; r, k) is captured by an "attained and maximal" pair rather than by a
      maximum operator, and m is a universally quantified number characterised by that pair.
      The guard n >= rk-1 together with k >= 1 keeps n - k + 1 out of natural truncation, so the
      binomial coefficient is the intended one. *)
Definition erdos_matching_extremal_formula_statement : Prop :=
  forall n r k m : nat,
    3 <= r -> 1 <= k ->
    r * k - 1 <= n ->
    x6_extremal_no_k_matching n r k m ->
    m = maxn 'C(r * k - 1, r) ('C(n, r) - 'C(n - k + 1, r)).

(** Corpus row: erdos:794
    Site: none
    Review: none
    English statement: (Erdos problem #794)
      Every 3-uniform hypergraph on 3n vertices with at least n^3 + 1 hyperedges contains either
      a set of 4 vertices spanning at least 3 hyperedges, or a set of 5 vertices spanning at
      least 7 hyperedges.
    Definitions: [x6_uniform E 3] - every hyperedge has exactly 3 vertices (hypergraph-theory/theories/conjectures/X6.v);
      [x6_edges_on E S] - the number of hyperedges of E contained in the vertex set S (same
      file).
    Notes: "a subgraph on 4 vertices with 3 edges" is read as a 4-element vertex set containing
      AT LEAST 3 hyperedges (and similarly for 5 and 7), which is the faithful reading of
      "contains".  The corpus records this row as solved. *)
Definition three_uniform_hypergraph_dense_small_configuration_statement : Prop :=
  forall (n : nat) (T : finType) (E : {set {set T}}),
    x6_uniform E 3 ->
    #|T| = 3 * n ->
    n ^ 3 + 1 <= #|E| ->
    (exists S : {set T}, #|S| = 4 /\ 3 <= x6_edges_on E S) \/
    (exists S : {set T}, #|S| = 5 /\ 7 <= x6_edges_on E S).

(** Corpus row: erdos:834
    Site: none
    Review: none
    English statement: (Erdos problem #834)
      There exists a 3-uniform hypergraph that is 3-critical - its chromatic number is 3 and
      deleting any single hyperedge leaves chromatic number 2 - and in which every vertex lies
      in at least seven hyperedges.
    Definitions: [x6_uniform E 3] (hypergraph-theory/theories/conjectures/X6.v);
      [x6_proper_coloring E col] - every hyperedge contains two vertices of different colours,
      i.e. no hyperedge is monochromatic (same file); [x6_chromatic_number E k] - k is the least
      number of colours admitting a proper colouring (same file); [x6_edge_delete E e] - E with
      the hyperedge e removed (same file); [x6_chromatic_edge_critical E k] - the chromatic
      number is k and removing any hyperedge leaves chromatic number k-1 (same file);
      [x6_hg_degree E v] - the number of hyperedges containing v (same file).
    Notes: the statement is an existence claim, so the whole burden is on exhibiting a witness.
      "3-critical" is read as chromatic-edge-critical with chromatic number 3.  The criticality
      clause demands the chromatic number to become EXACTLY k-1 = 2 after removing any
      hyperedge, marginally stronger than the usual "strictly less than k"; at k = 3 the two
      agree unless the remaining family is 1-colourable.  The corpus records this row as
      solved. *)
Definition critical_three_uniform_min_degree_seven_statement : Prop :=
  exists (T : finType) (E : {set {set T}}),
    x6_uniform E 3 /\
    x6_chromatic_edge_critical E 3 /\
    (forall v : T, 7 <= x6_hg_degree E v).

(** Corpus row: erdos:835
    Site: none
    Review: none
    English statement: (Erdos problem #835)
      There is a k greater than 2 such that the k-element subsets of a 2k-element set can be
      coloured with k+1 colours so that for every (k+1)-element subset A, all k+1 colours appear
      among the k-element subsets of A.
    Definitions: standard
    Notes: the colouring is a function from ALL subsets of the 2k-element ground set to the
      k+1 colours, but only its values on k-element subsets are constrained, which matches the
      problem.  "All k+1 colours appear" is stated as: for every colour there is a k-element
      subset of A carrying it. *)
Definition subset_kneser_full_palette_statement : Prop :=
  exists k : nat,
    2 < k /\
    exists col : {set 'I_(2 * k)} -> 'I_(k.+1),
      forall A : {set 'I_(2 * k)}, #|A| = k.+1 ->
        forall c : 'I_(k.+1),
          exists B : {set 'I_(2 * k)}, B \subset A /\ #|B| = k /\ col B = c.

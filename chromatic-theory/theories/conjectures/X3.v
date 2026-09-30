(** * Chromatic.conjectures.X3 -- v2 milestone X3, clean chi-boundedness wave

    This file states the first clean X3 sub-batch: undirected chi-boundedness /
    Gyarfas-Sumner rows whose source statements use standard finite graph
    vocabulary or definitions already recovered in the manifest context.  B3
    paper-local terms and the tournament out-neighbourhood followup are
    intentionally deferred. *)

From Chromatic.conjectures Require Import U8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local finite-graph vocabulary ****************************************)

(** Consecutive vertices on a listed cycle/path, stated without [nth] defaults
    so the definitions also behave over empty carriers. *)
Definition x3_consecutive_in_cycle (G : sgraph) (c : seq G) (u v : G) : Prop :=
  ((u, v) \in zip c (rot 1 c)) \/ ((v, u) \in zip c (rot 1 c)).

Definition x3_consecutive_in_path (G : sgraph) (p : seq G) (u v : G) : Prop :=
  ((u, v) \in zip p (behead p)) \/ ((v, u) \in zip p (behead p)).

(** A hole is an induced cycle of length at least four.  [ucycle] supplies the
    closed walk and vertex uniqueness; the final clause rules out chords. *)
Definition x3_hole (G : sgraph) (c : seq G) : Prop :=
  [/\ ucycle (--) c, 3 < size c &
      forall u v : G,
        u \in c -> v \in c -> u != v -> u -- v ->
        x3_consecutive_in_cycle c u v].

Definition x3_has_hole_length (G : sgraph) (L : nat) : Prop :=
  exists c : seq G, x3_hole c /\ size c = L.

Definition x3_holes_of_consecutive_lengths (G : sgraph) (ell : nat) : Prop :=
  exists t : nat,
    forall i : nat, 1 <= i -> i <= ell -> x3_has_hole_length G (t + i).

Definition x3_proper_colouring (G : sgraph) (C : finType) (col : G -> C) : Prop :=
  forall u v : G, u -- v -> col u != col v.

Definition x3_rainbow_hole_run
    (G : sgraph) (C : finType) (col : G -> C) (s : nat) : Prop :=
  exists (c : seq G) (r : nat),
    x3_hole c /\ s <= size c /\ uniq (map col (take s (rot r c))).

Definition x3_stable_set (G : sgraph) (S : {set G}) : Prop :=
  forall u v : G, u \in S -> v \in S -> u -- v -> False.

Definition x3_path_vertices (G : sgraph) (p : seq G) : {set G} :=
  [set v | v \in p].

Definition x3_induced_path (G : sgraph) (p : seq G) : Prop :=
  [/\ uniq p,
      (if p is u :: q then path (--) u q else true)
    & forall u v : G,
        u \in p -> v \in p -> u != v -> u -- v ->
        x3_consecutive_in_path p u v].

Definition x3_family_covers_vertices
    (G : sgraph) (I : finType) (A : I -> {set G}) : Prop :=
  forall v : G, exists i : I, v \in A i.

Definition x3_uniquely_covers_path_vertex
    (G : sgraph) (I : finType) (A : I -> {set G}) (p : seq G) (v : G) : Prop :=
  exists i : I, A i :&: x3_path_vertices p = [set v].

Definition x3_anticomplete (G : sgraph) (A B : {set G}) : Prop :=
  [disjoint A & B] /\
  forall a b : G, a \in A -> b \in B -> a -- b -> False.

Definition x3_bounded_chromatic (F : sgraph -> Prop) : Prop :=
  exists c : nat, forall G : sgraph, F G -> χ([set: G]) <= c.

Definition x3_complete_graph (G : sgraph) : Prop := clique [set: G].

Definition x3_two_forbidden_class (F1 F2 G : sgraph) : Prop :=
  ~ has_induced F1 G /\ ~ has_induced F2 G.

Definition x3_iso (G H : sgraph) : Prop := inhabited (G ≃ H).

Definition x3_iso_closed (F : sgraph -> Prop) : Prop :=
  forall G H : sgraph, x3_iso G H -> F G -> F H.

Definition x3_hereditary_class (F : sgraph -> Prop) : Prop :=
  x3_iso_closed F /\ forall (G : sgraph) (S : {set G}), F G -> F (induced S).

Fixpoint x3_poly_eval (p : seq nat) (x : nat) : nat :=
  if p is a :: q then a + x * x3_poly_eval q x else 0.

Definition x3_polynomially_chi_bounded (F : sgraph -> Prop) : Prop :=
  exists p : seq nat,
    forall G : sgraph, F G -> χ([set: G]) <= x3_poly_eval p (ω([set: G])).

Definition x3_positive_integer_set (F : nat -> Prop) : Prop :=
  forall n : nat, F n -> 0 < n.

Definition x3_infinite_integer_set (F : nat -> Prop) : Prop :=
  forall n : nat, exists m : nat, n <= m /\ F m.

Definition x3_bounded_gaps (F : nat -> Prop) : Prop :=
  exists b : nat,
    0 < b /\ forall n : nat, exists m : nat, n <= m /\ m < n + b /\ F m.

Definition x3_k_constricting (F : nat -> Prop) (k : nat) : Prop :=
  exists n : nat,
    forall G : sgraph,
      n <= χ([set: G]) ->
      k <= ω([set: G]) \/ exists L : nat, F L /\ x3_has_hole_length G L.

Definition x3_constricting (F : nat -> Prop) : Prop :=
  forall k : nat, x3_k_constricting F k.

Definition x3_complement_rel (G : sgraph) : rel G :=
  fun u v => (u != v) && ~~ (u -- v).

Lemma x3_complement_sym (G : sgraph) : symmetric (@x3_complement_rel G).
Proof. by move=> u v; rewrite /x3_complement_rel eq_sym sgP. Qed.

Lemma x3_complement_irrefl (G : sgraph) : irreflexive (@x3_complement_rel G).
Proof. by move=> u; rewrite /x3_complement_rel eqxx. Qed.

Definition x3_complement_graph (G : sgraph) : sgraph :=
  SGraph (@x3_complement_sym G) (@x3_complement_irrefl G).

Definition x3_complement_image (C : sgraph -> Prop) (G : sgraph) : Prop :=
  exists H : sgraph, C H /\ x3_iso G (x3_complement_graph H).

Definition x3_chi_omega_plus_bound (C : sgraph -> Prop) (c : nat) : Prop :=
  forall G : sgraph, C G ->
    forall S : {set G}, χ([set: induced S]) <= ω([set: induced S]) + c.

Definition x3_alpha_omega_large_class (G : sgraph) : Prop :=
  forall S : {set G},
    #|S| <= α([set: induced S]) * ω([set: induced S]) + 1.

Definition x3_triangle_free_induced_subgraphs_chi_le3 (G : sgraph) : Prop :=
  forall S : {set G}, triangle_free (induced S) -> χ([set: induced S]) <= 3.

(** ** X3 statements *******************************************************)

(** Corpus row: arxiv:1509.06563#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1509.06563__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1509.06563__00.json
    English statement: (Scott and Seymour 2018, informal conjecture generalising Theorem 1.3, arXiv:1509.06563)
      For all integers nu > 0 and k >= 3 there exists n such that every finite simple graph G whose
      clique number is less than k and whose chromatic number is at least n has, for some t, a hole
      of length t + i for every i with 1 <= i <= nu.
    Definitions: [x3_hole c] - c is a [ucycle] of size greater than 3 whose only adjacent pairs
      are consecutive on it, i.e. an induced cycle of length at least 4 (this file);
      [x3_has_hole_length G L] - G has a hole with exactly L vertices (this file);
      [x3_holes_of_consecutive_lengths G ell] - for some t, G has holes of all the lengths t+1, ...,
      t+ell (this file); [x3_consecutive_in_cycle] - the two vertices are consecutive on the listed
      cycle, defined through [zip c (rot 1 c)] to avoid [nth] defaults (this file).
    Notes: "G has no clique of cardinality k" is encoded as omega(G) < k, and "chromatic number at
      least n" as n <= chi(G). The quantifier order of the source is preserved: n is chosen after nu
      and k but before G. *)
Definition bounded_clique_consecutive_hole_lengths_statement : Prop :=
  forall nu k : nat, 0 < nu -> 3 <= k ->
    exists n : nat,
      forall G : sgraph,
        ω([set: G]) < k -> n <= χ([set: G]) ->
        x3_holes_of_consecutive_lengths G nu.

(** Corpus row: arxiv:1509.06563#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1509.06563__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1509.06563__01.json
    English statement: (Scott and Seymour 2018, Conjecture 1.5, arXiv:1509.06563)
      Every set F of positive integers that is infinite and has bounded gaps is constricting, that
      is, for every k there exists n such that every finite simple graph with chromatic number at
      least n has clique number at least k or a hole whose length belongs to F.
    Definitions: [x3_positive_integer_set F] - every member of F is positive (this file);
      [x3_infinite_integer_set F] - F has members above every bound, which for a set of naturals is
      infiniteness (this file); [x3_bounded_gaps F] - some b > 0 is such that every window of length
      b contains a member of F (this file); [x3_k_constricting F k] and [x3_constricting F] - the
      definitions recovered from the paper's context, k-constricting for every k (this file);
      [x3_has_hole_length] (this file).
    Notes: The notion "k-constricting" is not in the source's conjecture sentence but in its
      surrounding context, which the corpus row records in context_text; it is reproduced here.
      "Contains a clique with k vertices" is encoded as k <= omega(G). Sets of integers are modelled
      as predicates [nat -> Prop]. *)
Definition bounded_gaps_sets_are_constricting_statement : Prop :=
  forall F : nat -> Prop,
    x3_positive_integer_set F ->
    x3_infinite_integer_set F ->
    x3_bounded_gaps F ->
    x3_constricting F.

(** Corpus row: arxiv:1702.01094#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1702.01094__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1702.01094__00.json
    English statement: (Scott and Seymour 2017, Question in the conclusion, arXiv:1702.01094)
      For all s and kappa there exists n such that for every finite simple graph G with clique
      number at most kappa and chromatic number at least n, and every proper colouring of G by an
      arbitrary finite palette, G has a hole with at least s vertices in which some s consecutive
      vertices receive pairwise distinct colours.
    Definitions: [x3_rainbow_hole_run col s] - there are a hole c with at least s vertices and a
      rotation offset r such that the first s colours of the rotated list are pairwise distinct
      (this file); [x3_proper_colouring col] - adjacent vertices get different colours (this file);
      [x3_hole] (this file).
    Notes: The corpus row is a QUESTION; the Rocq body is its affirmative reading. "Some set of s
      consecutive vertices of the hole is rainbow" is realised by rotating the hole's vertex list
      and taking its first s entries, which is exactly a cyclic window of length s. The palette is
      an arbitrary finType quantified inside the statement. *)
Definition rainbow_consecutive_vertices_in_hole_statement : Prop :=
  forall s kappa : nat, exists n : nat,
    forall (G : sgraph) (C : finType) (col : G -> C),
      ω([set: G]) <= kappa ->
      n <= χ([set: G]) ->
      x3_proper_colouring col ->
      x3_rainbow_hole_run col s.

(** Corpus row: arxiv:1702.01094#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1702.01094__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1702.01094__01.json
    English statement: (Scott and Seymour 2017, Question in the conclusion, arXiv:1702.01094)
      For every s there exists n such that for every triangle-free finite simple graph G with
      chromatic number at least n and every finite family of stable sets whose union is the whole
      vertex set, G has an induced path on exactly s vertices such that for each vertex v of the
      path some member X of the family meets the path exactly in v.
    Definitions: [x3_stable_set S] - no two vertices of S are adjacent (this file);
      [x3_family_covers_vertices A] - every vertex lies in some member of the family (this file);
      [x3_induced_path p] - p is a list of distinct vertices forming a path in which only
      consecutive vertices are adjacent (this file); [x3_path_vertices p] - the set of vertices of p
      (this file); [x3_uniquely_covers_path_vertex A p v] - some member of the family intersects the
      vertex set of p exactly in the singleton v (this file); [triangle_free] (GTBase
      base/theories/base.v).
    Notes: The source's "very large chromatic number" is made explicit by the existential n,
      chosen after s and before G. The family of stable sets is indexed by an arbitrary finType,
      which is not a restriction here since the ground set is finite and hence carries only finitely
      many subsets. The path is required to have EXACTLY s vertices, as in the source's "s-vertex
      induced path". *)
Definition stable_cover_unique_induced_path_statement : Prop :=
  forall s : nat, exists n : nat,
    forall (G : sgraph) (I : finType) (A : I -> {set G}),
      triangle_free G ->
      n <= χ([set: G]) ->
      (forall i : I, x3_stable_set (A i)) ->
      x3_family_covers_vertices A ->
      exists p : seq G,
        size p = s /\
        x3_induced_path p /\
        forall v : G, v \in p -> x3_uniquely_covers_path_vertex A p v.

(** Corpus row: arxiv:1705.04609#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1705.04609__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1705.04609__00.json
    English statement: (Scott and Seymour 2018, Conjecture 1.8, arXiv:1705.04609)
      For all integers kappa and ell there exists c such that every finite simple graph with
      chromatic number greater than c contains a complete subgraph on kappa vertices or holes of ell
      consecutive lengths.
    Definitions: [x3_holes_of_consecutive_lengths G ell] - for some t, G has holes of all lengths
      t+1, ..., t+ell (this file); [x3_hole] - induced cycle of length at least 4 (this file).
    Notes: "Contains a complete subgraph on kappa vertices" is encoded as kappa <= omega(G), and
      "chromatic number greater than c" as c < chi(G), matching the source's strict inequality. *)
Definition clique_or_consecutive_holes_statement : Prop :=
  forall kappa ell : nat, exists c : nat,
    forall G : sgraph,
      c < χ([set: G]) ->
      kappa <= ω([set: G]) \/ x3_holes_of_consecutive_lengths G ell.

(** Corpus row: arxiv:1910.00697#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1910.00697__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1910.00697__00.json
    English statement: (Esperet's problem as recorded by Bonamy and Pilipczuk 2020, arXiv:1910.00697)
      There exists a class of finite simple graphs, closed under isomorphism and under taking
      induced subgraphs, that is chi-bounded but not polynomially chi-bounded: no polynomial with
      natural coefficients p satisfies chi(G) <= p(omega(G)) for every member G of the class.
    Definitions: [x3_hereditary_class F] - F is closed under isomorphism and under [induced]
      subgraphs (this file); [x3_polynomially_chi_bounded F] - some coefficient list p has chi(G) <=
      [x3_poly_eval p (omega(G))] for all members (this file); [x3_poly_eval] - Horner evaluation of
      a coefficient list (this file); [chi_bounded F] - some f : nat -> nat bounds chi by f of omega
      on the class (U8.v).
    Notes: Polynomials are represented as lists of NATURAL coefficients; this is no restriction
      for an upper bound of this shape, since any real-coefficient polynomial bound is dominated by
      one with natural coefficients. Corpus status: this question was answered affirmatively by
      Brianski, Davies and Walczak 2022; the row is nevertheless kept as a statement-only definition
      and is not proved here. *)
Definition hereditary_chi_bounded_not_polynomial_statement : Prop :=
  exists F : sgraph -> Prop,
    x3_hereditary_class F /\
    chi_bounded F /\
    ~ x3_polynomially_chi_bounded F.

(** Corpus row: arxiv:2110.00278#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2110.00278__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2110.00278__00.json
    English statement: (Scott, Seymour and Spirkl 2022, Conjecture 1.3, arXiv:2110.00278)
      For every finite simple graph H that is a forest there exists c > 0 such that every graph G
      with no induced subgraph isomorphic to H satisfies chi(G) <= omega(G) raised to the power c.
    Definitions: [has_induced H G] - some vertex set of G induces a graph isomorphic to H (U8.v);
      [is_forest [set: H]] - H has no cycle (coq-graph-theory sgraph.v, re-exported by GTBase
      base.v).
    Notes: The exponent c is a POSITIVE NATURAL, while the source allows a positive real; this is
      equivalent for a bound of this form, since rounding a real exponent up preserves the
      inequality on the naturals involved. The quantifier order is preserved: c depends on H only. *)
Definition polynomial_gyarfas_sumner_statement : Prop :=
  forall H : sgraph, is_forest [set: H] ->
    exists c : nat,
      0 < c /\
      forall G : sgraph,
        ~ has_induced H G ->
        χ([set: G]) <= (ω([set: G])) ^ c.

(** Corpus row: arxiv:2201.08204#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2201.08204__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2201.08204__00.json
    English statement: (Davies, recorded as Question 3.1 by Carbonero, Hompe, Moore and Spirkl 2022, arXiv:2201.08204)
      For every n there exists a finite simple graph G with chromatic number at least n, clique
      number exactly 3, and such that every triangle-free induced subgraph of G has chromatic number
      at most 3.
    Definitions: [x3_triangle_free_induced_subgraphs_chi_le3 G] - every induced subgraph of G that
      is triangle-free has chromatic number at most 3 (this file); [triangle_free] (GTBase
      base/theories/base.v); [induced S] (coq-graph-theory sgraph.v).
    Notes: The corpus row is a QUESTION, "Are there graphs with clique number 3 and arbitrarily
      large chromatic number whose triangle-free induced subgraphs all have chromatic number at most
      3?"; the Rocq body is its affirmative reading, with "arbitrarily large" rendered by the outer
      universal quantifier over n. *)
Definition omega3_large_chi_triangle_free_induced_subgraphs_statement : Prop :=
  forall n : nat, exists G : sgraph,
    n <= χ([set: G]) /\
    ω([set: G]) = 3 /\
    x3_triangle_free_induced_subgraphs_chi_le3 G.

(** Corpus row: erdos:1111
    Site: none
    Review: none
    English statement: (Erdos Problems #1111)
      For all t >= 1 and c >= 1 there exists d >= 1 such that every finite simple graph G with
      chromatic number at least d and clique number less than t has two disjoint vertex sets A and B
      with no edge between them and with chi(A) >= chi(B) >= c.
    Definitions: [x3_anticomplete A B] - A and B are disjoint and no vertex of A is adjacent to a
      vertex of B (this file); chi(A) is the subset-relative chromatic number of coq-graph-theory.
    Notes: This row has no site or review page in the corpus, hence the literal "none" above. The
      source's chi(A) >= chi(B) >= c is written as the conjunction c <= chi(B) and chi(B) <= chi(A). *)
Definition erdos_anticomplete_pairs_statement : Prop :=
  forall t c : nat, 1 <= t -> 1 <= c ->
    exists d : nat,
      1 <= d /\
      forall G : sgraph,
        d <= χ([set: G]) -> ω([set: G]) < t ->
        exists A B : {set G},
          x3_anticomplete A B /\
          c <= χ(B) /\ χ(B) <= χ(A).

(** Corpus row: studies:std_galvin_r_dl_conjecture
    Site: none
    Review: none
    English statement: (Galvin and Rodl, studies slice of the corpus)
      For all k and r there exists n such that every finite simple graph G with chromatic number at
      least n and clique number at most k has an induced subgraph H with chromatic number at least r
      and clique number exactly 2.
    Definitions: [induced S] - the subgraph induced on the vertex set S (coq-graph-theory
      sgraph.v); chi and omega are taken on the full vertex set of that induced subgraph.
    Notes: This row has no site or review page in the corpus, hence the literal "none" above.
      "Induced subgraph H" is realised by a vertex set S, and omega(H) = 2 means H has an edge but
      no triangle. *)
Definition galvin_rodl_induced_omega2_subgraph_statement : Prop :=
  forall k r : nat, exists n : nat,
    forall G : sgraph,
      n <= χ([set: G]) -> ω([set: G]) <= k ->
      exists S : {set G},
        r <= χ([set: induced S]) /\ ω([set: induced S]) = 2.

(** Corpus row: studies:std_gy_rf_s_complementation_conjecture
    Site: none
    Review: none
    English statement: (Gyarfas' Complementation Conjecture, studies slice of the corpus)
      For every c and every class C of finite simple graphs such that every induced subgraph H of
      every member of C satisfies chi(H) <= omega(H) + c, the class of graphs isomorphic to the
      complement of a member of C is chi-bounded.
    Definitions: [x3_chi_omega_plus_bound C c] - for every member G of C and every vertex set S,
      chi of the induced subgraph is at most omega of it plus c (this file); [x3_complement_graph G]
      - the complement graph, adjacency being non-equality together with non-adjacency (this file);
      [x3_complement_image C] - the class of graphs isomorphic to the complement of a member of C
      (this file); [x3_iso] - isomorphism wrapped in [inhabited] (this file); [chi_bounded] (U8.v).
    Notes: This row has no site or review page in the corpus, hence the literal "none" above.
      Taking the class of complements up to isomorphism, rather than the strict image, is what makes
      the class isomorphism-closed. *)
Definition gyarfas_complementation_chi_bounded_statement : Prop :=
  forall (c : nat) (C : sgraph -> Prop),
    x3_chi_omega_plus_bound C c ->
    chi_bounded (x3_complement_image C).

(** Corpus row: studies:std_gy_rf_s_conjecture_6_8_h_h_h_1_classes_are_bound
    Site: none
    Review: none
    English statement: (Gyarfas' Conjecture 6.8, studies slice of the corpus)
      The class of finite simple graphs G such that every induced subgraph H of G satisfies |V(H)|
      <= alpha(H) * omega(H) + 1 is chi-bounded.
    Definitions: [x3_alpha_omega_large_class G] - every vertex set S satisfies #|S| <= alpha *
      omega + 1 for the induced subgraph on S (this file); alpha and omega are the coq-graph-theory
      independence and clique numbers; [chi_bounded] (U8.v).
    Notes: This row has no site or review page in the corpus, hence the literal "none" above. The
      source inequality alpha(H) * omega(H) >= |V(H)| - 1 is rewritten as |V(H)| <= alpha(H) *
      omega(H) + 1 to avoid truncated nat subtraction; the two are equivalent over the naturals. *)
Definition gyarfas_alpha_omega_chi_bounded_statement : Prop :=
  chi_bounded x3_alpha_omega_large_class.

(** Corpus row: studies:std_gy_rf_s_sumner_conjecture
    Site: none
    Review: none
    English statement: (Gyarfas and Sumner, studies slice of the corpus)
      For all finite simple graphs F1 and F2, the class of graphs having neither an induced subgraph
      isomorphic to F1 nor one isomorphic to F2 has bounded chromatic number, i.e. a single constant
      bounds chi over the whole class, if and only if one of F1 and F2 is a complete graph and the
      other is a forest.
    Definitions: [x3_two_forbidden_class F1 F2 G] - G has no induced F1 and no induced F2 (this
      file); [x3_bounded_chromatic F] - one constant c bounds chi(G) for every member (this file);
      [x3_complete_graph G] - the whole vertex set is a [clique] (this file); [is_forest] (coq-
      graph-theory sgraph.v); [has_induced] (U8.v).
    Notes: This row has no site or review page in the corpus, hence the literal "none" above. The
      boundedness is ABSOLUTE, a single constant for the class, not chi-boundedness as a function of
      omega; that is what the source sentence says. The statement is an equivalence, so both
      directions are asserted. *)
Definition gyarfas_sumner_two_forbidden_statement : Prop :=
  forall F1 F2 : sgraph,
    x3_bounded_chromatic (x3_two_forbidden_class F1 F2) <->
    ((x3_complete_graph F1 /\ is_forest [set: F2]) \/
     (x3_complete_graph F2 /\ is_forest [set: F1])).

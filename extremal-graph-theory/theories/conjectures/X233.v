(** * Extremal.conjectures.X233 -- wave X233: six dense-or-sparse rows (2026-10-26)

    A six-row wave under the prospective contract of meta/faithfulness_policy.json (hard lint,
    classified local helpers, grounding certificates, an independent verifier).  Rows:
    arxiv:2105.07370#00 (union cover by eps-restricted sets), arxiv:2307.06455#00 (polynomial
    Nikiforov), arxiv:2111.00532#00 (pure pairs in a 3-blockade with no transversal triangle),
    arxiv:2311.05500#00 (universal graphs for bounded density), arxiv:2403.08303#00 (polynomial
    close Rodl), arxiv:2307.08361#00 (polynomial degree-bounding functions).  Shared vocabulary is
    reused: [induced_free G H] and [has_subgraph G H] and [edge_count G] (GTBase.common),
    [hereditary_class] (GTBase.graph_classes), [complete_between] and [anticomplete]
    (GTBase.set_pairs), [triangle_set] (GTBase.triangles), [horner_nat] (GTBase.poly_nat),
    [Delta G] the maximum degree (GTBase), [compl G] the complement and [induced S] the induced
    subgraph (coq-graph-theory).  No real numbers: every rational parameter is a pair of naturals
    and every existential exponent or constant a natural number, each reduction argued in the
    row's Notes.  The grounding certificates are in grounding_X233.v. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph.
From GTBase Require Import base common set_pairs triangles graph_classes poly_nat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x233 vocabulary ************************************************* *)

(** [X] is (a/b)-restricted: one of G[X] and its complement has maximum degree at most
    (a/b)|X| (arXiv:2105.07370 l.89-91; arXiv:2307.06455 l.489-490). *)
Definition x233_restricted (G : sgraph) (a b : nat) (X : {set G}) : Prop :=
  b * Delta (induced X) <= a * #|X| \/ b * Delta (@induced (compl G) X) <= a * #|X|.

(** The number of copies of [H] in [G], a copy being an isomorphism from [H] onto an induced
    subgraph of [G] (arXiv:2307.06455 l.162, l.498): the injective maps that preserve and
    reflect adjacency. *)
Definition x233_induced_copies (G H : sgraph) : nat :=
  #|[set f : {ffun H -> G} | injectiveb f && [forall x : H, [forall y : H, (f x -- f y) == (x -- y)]]]|.

(** A blockade of length 3: pairwise disjoint nonempty blocks (arXiv:2111.00532 l.89-90). *)
Definition x233_blockade (G : sgraph) (B : 'I_3 -> {set G}) : Prop :=
  (forall i : 'I_3, B i != set0) /\ (forall i j : 'I_3, i != j -> [disjoint B i & B j]).

(** Its width: the minimum cardinality of its blocks (l.90). *)
Definition x233_width (G : sgraph) (B : 'I_3 -> {set G}) : nat :=
  \big[minn/#|B ord0|]_(i < 3) #|B i|.

(** A B-transversal triangle: a triangle with exactly one vertex in each block (l.91-93). *)
Definition x233_transversal_triangle (G : sgraph) (B : 'I_3 -> {set G}) : Prop :=
  exists T : {set G}, triangle_set T /\ forall i : 'I_3, #|T :&: B i| = 1.

(** Density at most a/b: every subgraph has at most (a/b) times as many edges as vertices,
    i.e. b e(H[S]) <= a |S| for every vertex set S (arXiv:2311.05500 l.108-115). *)
Definition x233_max_density_at_most (H : sgraph) (a b : nat) : Prop :=
  forall S : {set H}, b * edge_count (induced S) <= a * #|S|.

(** [G] is (a/b)-close to [F]: adding or deleting at most (a/b) n^2 / 2 edges of [G] gives a
    graph in [F] (arXiv:2403.08303 l.325); the edits are counted as ordered pairs, twice each. *)
Definition x233_close (F : sgraph -> Prop) (G : sgraph) (a b : nat) : Prop :=
  exists (r : rel G) (rs : symmetric r) (ri : irreflexive r),
    F (SGraph rs ri) /\ b * #|[set p : G * G | (p.1 -- p.2) != r p.1 p.2]| <= a * #|G| ^ 2.

(** [S] is (a/b)-homogeneous: the edge density of G[S] is at most a/b or at least 1 - a/b
    (arXiv:2403.08303 l.257-258), cross-multiplied by C(|S|, 2). *)
Definition x233_homogeneous (G : sgraph) (a b : nat) (S : {set G}) : Prop :=
  b * edge_count (induced S) <= a * 'C(#|S|, 2) \/
  (b - a) * 'C(#|S|, 2) <= b * edge_count (induced S).

(** The biclique number tau(G): the largest s such that G contains a (not necessarily
    induced) K_{s,s} (arXiv:2307.08361 l.181); [complete_between A B] forces A and B disjoint. *)
Definition x233_biclique_number (G : sgraph) : nat :=
  \max_(s < #|G|.+1 | [exists A : {set G}, exists B : {set G},
                         [&& #|A| == s, #|B| == s & complete_between A B]]) s.

(** [F] is degree-bounded: some g : N -> N has d(G) <= g(tau(G)) on [F], with d(G) = 2e(G)/|G|
    the average degree (arXiv:2307.08361 l.181, l.213), cross-multiplied by |G|. *)
Definition x233_degree_bounded (F : sgraph -> Prop) : Prop :=
  exists g : nat -> nat, forall G : sgraph, F G -> 2 * edge_count G <= #|G| * g (x233_biclique_number G).

(** ** X233 statements ******************************************************* *)

(** Corpus row: arxiv:2105.07370#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2105.07370__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2105.07370__00.json
    English statement: (arXiv:2105.07370, Chudnovsky, Scott, Seymour and Spirkl, "Strengthening
      Rodl's theorem", the union variant after Theorem 1.4)
      For every graph H and every eps > 0 there is an integer N such that for every H-free graph
      G, V(G) is the union of at most N eps-restricted subsets (not necessarily pairwise
      disjoint); X is eps-restricted if one of G[X] and the complement of G restricted to X has
      maximum degree at most eps |X|.
    Definitions: [induced_free G H] - no vertex set of G induces a graph isomorphic to H
      (GTBase.common); [x233_restricted G a b X] - one of G[X], compl(G)[X] has maximum degree at
      most (a/b)|X| (this file); [Delta G] - maximum degree (GTBase); [compl G] - the complement
      and [induced X] - the induced subgraph (coq-graph-theory).
    Notes: the source is the e-print paper.tex (sha256 0d51926b...): H-free l.86-88,
      eps-restricted l.89-91, the row l.126-127.  At most N subsets are N indexed sets, repeats
      and empty sets allowed (the empty set is restricted).  eps = a/b is rational: an
      eps'-restricted set is eps-restricted when eps' <= eps (Delta <= eps'|X| <= eps|X|), so a
      rational eps' in (0, eps] and its N serve every real eps > 0.  For the null graph H no
      graph is H-free and the row is vacuous; no guard is needed.  STATUS: the row follows from
      the same paper's Theorem 1.4 (l.119-123, proved there): a partition of V(G) into at most N
      eps-restricted subsets is such a union.  The authors' remark (l.127) says the variant does
      not seem easy (to prove directly) and does not imply Theorem 1.4.  The pinned review says
      open; the status is Lancelot's bookkeeping (design finding F1). *)
Definition restricted_union_cover_statement : Prop :=
  forall (H : sgraph) (a b : nat), 0 < a -> 0 < b ->
    exists N : nat, forall G : sgraph, induced_free G H ->
      exists P : 'I_N -> {set G},
        (forall v : G, exists i : 'I_N, v \in P i) /\ (forall i : 'I_N, x233_restricted a b (P i)).

(** Corpus row: arxiv:2307.06455#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2307.06455__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2307.06455__00.json
    English statement: (arXiv:2307.06455, Nguyen, Scott and Seymour, "Induced subgraph density.
      IV", Conjecture 1.8, "polynomial Nikiforov")
      For every graph H there is d > 0 such that for every eps in (0, 1/2) and every graph G with
      ind_H(G) <= (eps^d |G|)^|H|, some eps-restricted subset of V(G) has size at least
      eps^d |G|; ind_H(G) is the number of copies of H in G, a copy being an isomorphism from H
      to an induced subgraph of G.
    Definitions: [x233_induced_copies G H] - the injective maps H -> G that preserve and reflect
      adjacency (this file); [x233_restricted G a b S] - as in arxiv:2105.07370#00 (this file).
    Notes: the source is the e-print density4.tex (sha256 804d8076...): copy and H-free
      l.162-163, eps-restricted l.489-490, ind_H l.498, the conjecture l.522-526 (the eighth
      numbered environment of section 1).  Copies are labelled: an automorphism of H gives a
      different copy.  eps = a/b with 0 < 2a < b and d is natural.  d: a larger d strengthens
      the hypothesis and weakens the conclusion, so some real d > 0 serves iff a natural one
      does.  eps: for a fixed G the restriction test Delta <= eps s (s <= |G|) changes only at the
      finitely many points j/s; a rational eps' strictly between eps and the next such point
      (and below 1/2) carries the hypothesis up (the threshold grows with eps) and the
      conclusion back (no jump point in (eps, eps']), so the rational form implies the real one,
      and conversely.  The thresholds cross-multiply exactly: ind <= (eps^d n)^h iff
      b^(dh) ind <= (a^d n)^h, and |S| >= eps^d n iff b^d |S| >= a^d n.  GUARD 0 < |H|: for the
      null graph ind_H(G) = 1 (the empty map) and (eps^d n)^0 = 1, so the hypothesis would hold
      for every G and the claim fail on random graphs; the paper's graphs are nonempty.  The
      pinned review says open (equivalent to Erdos-Hajnal by Bucic, Fox and Pham). *)
Definition polynomial_nikiforov_statement : Prop :=
  forall H : sgraph, 0 < #|H| ->
    exists d : nat, 0 < d /\
      forall (a b : nat) (G : sgraph), 0 < a -> 2 * a < b ->
        b ^ (d * #|H|) * x233_induced_copies G H <= (a ^ d * #|G|) ^ #|H| ->
        exists S : {set G}, x233_restricted a b S /\ a ^ d * #|G| <= b ^ d * #|S|.

(** Corpus row: arxiv:2111.00532#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2111.00532__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2111.00532__00.json
    English statement: (arXiv:2111.00532, Scott, Seymour and Spirkl, "Pure pairs. IX.
      Transversal trees", Question 1.3, affirmative form)
      There exist c, eps > 0 such that for every blockade B = (B_1, B_2, B_3) in a graph G, of
      width W, with no B-transversal triangle, there are distinct i, j and X subset of B_i,
      Y subset of B_j such that X, Y is a pure pair, |X| >= eps W and |Y| >= eps W^c.
    Definitions: [x233_blockade B] - three pairwise disjoint nonempty blocks (this file);
      [x233_width B] - the minimum block size (this file); [x233_transversal_triangle B] - a
      triangle with exactly one vertex in each block (this file); [triangle_set T] - T is a
      3-clique (GTBase.triangles); [complete_between X Y], [anticomplete X Y] - X complete to Y,
      X anticomplete to Y (GTBase.set_pairs).
    Notes: the source is the e-print paper-pure9.tex (sha256 5d338f15...): complete, anticomplete
      and pure pair l.82-85, blockade, width and transversal l.89-93, the Question l.130-135.
      RECORD TEXT: the pinned statement_text (from the PDF) ends "|X|, |Y| >= eps W^c", which is
      the Erdos-Hajnal-Pach theorem (l.113-121) for the triangle, a known result; the paper asks
      |X| >= eps W and |Y| >= eps W^c (l.133-134), and its Theorem 1.4 (l.150-156, cohesive
      (eps W, eps W^c)) with l.157 ("for k=3 is open and equivalent to" the Question) confirms
      the asymmetric form, which is encoded (as X58 for arXiv:1810.00058; design finding F2).
      c = 1/q and eps = 1/p lose nothing: if (c, eps) serves, so does every 0 < c' <= c,
      0 < eps' <= eps, since W >= 1 (blocks are nonempty) gives W^c' <= W^c; and
      eps W^(1/q) <= |Y| iff W <= (p |Y|)^q, eps W <= |X| iff W <= p |X|.  X and Y are disjoint
      because the blocks are; i, j range over ordered pairs, so the eps W side may be either
      block.  The pinned review says open. *)
Definition transversal_triangle_pure_pair_statement : Prop :=
  exists p q : nat, [/\ 0 < p, 0 < q &
    forall (G : sgraph) (B : 'I_3 -> {set G}),
      x233_blockade B -> ~ x233_transversal_triangle B ->
      exists (i j : 'I_3) (X Y : {set G}),
        [/\ i != j, X \subset B i, Y \subset B j,
            complete_between X Y || anticomplete X Y &
            x233_width B <= p * #|X| /\ x233_width B <= (p * #|Y|) ^ q]].

(** Corpus row: arxiv:2311.05500#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2311.05500__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2311.05500__00.json
    English statement: (arXiv:2311.05500, Alon, Dodson, Jackson, McCarty, Nenadov and Southern,
      "Universality for graphs with bounded density", Conjecture 1.1)
      For every rational d > 1 there is C = C(d) such that for every n there is a graph G with
      e(G) <= C n^(2 - 1/d) which is H_d(n)-universal: every graph with n vertices and density
      m(H) = max over subgraphs H' of e(H')/v(H') at most d is a (not necessarily induced)
      subgraph of G.
    Definitions: [x233_max_density_at_most H a b] - b e(H[S]) <= a |S| for every vertex set S
      (this file); [edge_count G] - the number of edges (GTBase.common); [has_subgraph G H] - H is
      a subgraph of G, an injective adjacency-preserving map (GTBase.common).
    Notes: the source is the e-print univden-arXiv-v2.tex (sha256 7f301cf9...): universal
      l.101-102, density and H_d(n) l.108-115, the conjecture l.124-131, why d > 1 l.144-146.
      d = a/b with 0 < b < a; C comes before n (C = C(d), l.130) and is natural (a larger C
      weakens the bound).  m(H) <= d iff b e(H[S]) <= a |S| for every S: a subgraph with vertex
      set S has at most e(H[S]) edges (S empty is harmless).  e(G) <= C n^(2 - 1/d) iff
      e(G)^a <= C^a n^(2a - b), since 2 - 1/d = (2a - b)/a > 0; the natural-number subtraction
      2a - b is exact under the guard b < a.  A non-reduced pair (ka, kb) gives the same
      conditions.  The pinned review says open. *)
Definition bounded_density_universal_graph_statement : Prop :=
  forall a b : nat, 0 < b -> b < a ->
    exists C : nat, forall n : nat, exists G : sgraph,
      edge_count G ^ a <= C ^ a * n ^ (2 * a - b) /\
      forall H : sgraph, #|H| = n -> x233_max_density_at_most H a b -> has_subgraph G H.

(** Corpus row: arxiv:2403.08303#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2403.08303__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2403.08303__00.json
    English statement: (arXiv:2403.08303, Bucic, Fox and Pham, "Equivalence between
      Erdos-Hajnal and polynomial Rodl and Nikiforov conjectures", Conjecture 10)
      For each proper hereditary family F of graphs there are C, d > 0 such that, for
      0 < eps < 1/2, every graph on n vertices which is eps^d-close to F contains an
      eps-homogeneous set of size at least eps^C n; G is alpha-close to F if adding or deleting
      at most alpha n^2/2 edges gives a graph in F, and S is eps-homogeneous if the edge density
      of G[S] is at most eps or at least 1 - eps.
    Definitions: [hereditary_class F] - F is closed under isomorphism and induced subgraphs
      (GTBase.graph_classes); [x233_close F G a b] - some symmetric irreflexive relation on V(G)
      giving a graph in F differs from G on at most (a/b)|G|^2 ordered pairs (this file);
      [x233_homogeneous G a b S] - b e(G[S]) <= a C(|S|,2) or (b - a) C(|S|,2) <= b e(G[S])
      (this file); [edge_count G] - the number of edges (GTBase.common).
    Notes: the source is the e-print main.tex (sha256 fc51ad74...): homogeneous l.245,
      eps-homogeneous l.257-258, hereditary l.301, alpha-close l.325, the conjecture l.327-329
      (the tenth numbered environment), Theorem 11 l.333-336 (the conjecture for F iff the
      Erdos-Hajnal property of F).  Proper means some graph is not in F.  The edited graph keeps
      V(G) (l.325); [hereditary_class] includes isomorphism closure, so no relabelling is needed.
      Ordered pairs count each edit twice, so at most alpha n^2/2 edits iff b * (ordered) <= a n^2
      for alpha = a/b.  eps = a/b with 0 < 2a < b, and C, d natural: a larger d strengthens the
      hypothesis, a larger C weakens the conclusion.  eps: for a fixed G every test compares an
      integer with eps times an integer at most n^2 (e <= eps m, e >= (1 - eps) m, m = C(s,2));
      it changes only at the finitely many points j/m and 1 - j/m, so a rational eps' strictly
      between eps and the next such point (and below 1/2) carries the hypothesis up and the
      conclusion back, and the rational form is equivalent to the real one.  For |S| <= 1 the
      density 0/0 is undefined and the cross-multiplied test holds; harmless, every two-vertex
      set having density 0 or 1.  The pinned review says open. *)
Definition polynomial_close_rodl_statement : Prop :=
  forall F : sgraph -> Prop, hereditary_class F -> (exists G0 : sgraph, ~ F G0) ->
    exists C d : nat, [/\ 0 < C, 0 < d &
      forall (a b : nat) (G : sgraph), 0 < a -> 2 * a < b ->
        x233_close F G (a ^ d) (b ^ d) ->
        exists S : {set G}, x233_homogeneous a b S /\ a ^ C * #|G| <= b ^ C * #|S|].

(** Corpus row: arxiv:2307.08361#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2307.08361__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2307.08361__00.json
    English statement: (arXiv:2307.08361, Du, Girao, Hunter, McCarty and Scott, "Induced
      C_4-free subgraphs with large average degree", the question after Corollary 1.4,
      affirmative form)
      Every hereditary degree-bounded class F has a polynomial degree-bounding function: a
      polynomial g with d(G) <= g(tau(G)) for every G in F, where d(G) is the average degree,
      tau(G) the largest s such that G contains a (not necessarily induced) K_{s,s}, and F is
      degree-bounded if some g : N -> N has d(G) <= g(tau(G)) for every G in F.
    Definitions: [hereditary_class F] - F is closed under isomorphism and induced subgraphs
      (GTBase.graph_classes); [x233_biclique_number G] - tau(G) (this file);
      [x233_degree_bounded F] - some g : nat -> nat with 2 e(G) <= |G| g(tau(G)) on F (this
      file); [horner_nat p x] - the polynomial with natural coefficient list p at x
      (GTBase.poly_nat); [edge_count G] - the number of edges (GTBase.common).
    Notes: the source is the e-print Inducedfourcycle.tex (sha256 77b41154...): hereditary
      l.177, degree-bounded and tau l.181, Corollary 1.4 l.189, the question l.192 ("It could
      still be true, however, that every hereditary degree-bounded class is polynomially
      degree-bounded"), d(G) = 2e(G)/|G| l.213.  d(G) <= x iff 2 e(G) <= |G| x (for |G| = 0, d is
      undefined and the test is 0 <= 0).  [complete_between A B] with |A| = |B| = s forces A, B
      disjoint, so it is a K_{s,s} subgraph.  A polynomial with real coefficients is dominated on
      N by one with natural coefficients, and conversely, so natural coefficient lists lose
      nothing.  The pinned review says solved (Girao and Hunter, 2025); no formal resolution
      is recorded. *)
Definition polynomial_degree_bounding_statement : Prop :=
  forall F : sgraph -> Prop, hereditary_class F -> x233_degree_bounded F ->
    exists p : seq nat, forall G : sgraph, F G ->
      2 * edge_count G <= #|G| * horner_nat p (x233_biclique_number G).

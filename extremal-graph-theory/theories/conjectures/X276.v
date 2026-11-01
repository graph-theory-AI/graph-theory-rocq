(** * Extremal.conjectures.X276 -- v2 rows: Erdos's problem on (k,r)-graphs, Hajebi's clique-cover conjecture *)

From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X276 statements *****************************************************)

(** Corpus row: studies:std_erd_s_problem_on_k_r_graphs
    Site: none
    Review: none
    English statement: (Erdos; studies slice of the corpus, records arXiv:1912.02342 and arXiv:2508.08703)
      Let k >= 4.  For every n let f_k(n) denote the largest integer r >= 1 such that there exists a (k,r)-graph on
      n vertices (f_k(n) := 0 if no such graph exists for any r >= 1).  Is it true that f_k(n) -> infinity for
      n -> infinity?
    Definitions: [χ(A)] - the chromatic number of the subgraph induced on A (coq-graph-theory coloring.v);
      [induced (~: [set v])] - G - v, the subgraph induced on the other vertices (coq-graph-theory); [E(G)] - the
      edge set of G (GTBase common.v); [del_edge_set G F] - G - F, the edges of F removed and the vertices kept
      (GTBase common.v).  As Skottova and Steiner define them (arXiv:2508.08703v1, main.tex l.197, l.199): a vertex
      or a set of edges is critical if its removal lowers the chromatic number, so a critical edge set need not be
      minimal; G is k-vertex-critical if chi(G) = k and every vertex is critical; a (k,r)-graph is a
      k-vertex-critical graph in which no set of at most r edges is critical.
    Notes: encoded as the affirmative answer, the corpus's precedent for question rows.  A (k,r)-graph is a
      (k,r')-graph for every r' <= r, and f_k(n) is finite (f_k(n) < (n - 1) / (k - 1), l.226-227), so for r >= 1
      f_k(n) >= r iff some (k,r)-graph has n vertices (the convention f_k(n) := 0 when there is none keeps this, so
      it cannot affect the limit), and f_k(n) -> infinity iff for every r all large n carry a (k,r)-graph: the body
      (r = 0 adds nothing, a (k,1)-graph being a (k,0)-graph).  Problem 1.1 (main.tex
      l.203-205) asks for every sufficiently large order, not along a sequence.  The last clause is "no set of at
      most r edges is critical": deleting edges never raises chi, so k <= chi(G - F) says chi does not drop.
      OPEN at the pin: Skottova and Steiner prove f_k(n) = Omega(n^(1/3)) for every fixed k >= 5 (Theorem 1.2,
      l.214-217), "leaving only k = 4 open" (l.210); k = 4 contains Dirac's conjecture (r = 1, l.187, l.197).
      Related: erdos:944 (chromatic XE1) asks for some (k,r)-graph for every k >= 4 and r >= 1, which this row
      implies (a candidate edge, not in this wave); arxiv:2508.08703#00 (chromatic X7) is the same paper's 6-regular
      (4,1)-graph question.  XE1's [xe1_vertex_critical], [xe1_edge_critical_set] and
      [xe1_all_edge_critical_sets_large] (chromatic-theory XE1.v l.60-67) are these conditions; extremal-graph-theory
      cannot import Chromatic, so the body inlines them with GTBase's [induced] and [del_edge_set], and the three
      stay candidates for a post-RC library family (vertex-critical graphs, critical edge sets).  The pinned
      extraction of the record 1912.02342 (bounded VC-dimension and the Schur-Erdos conjecture) has no (k,r)-graph
      entry; the attachment is for a separate literature item, as is anything else on the row's status. *)
Definition erdos_kr_graphs_unbounded_statement : Prop :=
  forall k : nat, 4 <= k -> forall r : nat, exists n0 : nat, forall n : nat, n0 <= n ->
    exists G : sgraph, #|G| = n /\
      [/\ χ([set: G]) = k,
          forall v : G, χ([set: induced (~: [set v])]) < k &
          forall F : {set {set G}}, F \subset E(G) -> #|F| <= r -> k <= χ([set: del_edge_set G F])].

(** Corpus row: studies:std_hajebi_s_conjecture
    Site: none
    Review: none
    English statement: (Hajebi; studies slice of the corpus, record arXiv:2211.12065)
      For every integer t >= 1 there exists eps > 0 such that every K_{t,t}-free graph G has a clique cover of size
      O(|G|^(2 - eps)).
    Definitions: ['K_t,t] - the complete bipartite graph K_{t,t} on 'I_t + 'I_t (coq-graph-theory);
      [induced_free G H] - no induced subgraph of G is isomorphic to H (GTBase common.v); [cliqueb A] - the
      vertices of A are pairwise adjacent (coq-graph-theory).  As Nguyen, Scott, Seymour and Thomasse define them
      (arXiv:2211.12065v1, main.tex l.91-93, l.100): a clique X covers an edge uv if u and v are in X; a clique
      cover of G is a collection of cliques covering all the EDGES of G, its size the number of cliques; H-free
      means no INDUCED copy of H.
    Notes: encoded as stated, with eps = 1 / q for a positive integer q and the O-constant C: the bound
      #|cover| <= C^(1/q) |G|^(2 - 1/q), raised to the power q.  Every eps > 0 has some 1 / q <= eps, and a smaller
      eps only weakens the bound, so a reciprocal integer loses nothing; a real constant D gives C = ceil(D^q).  The
      constant is uniform over all graphs, which loses nothing either: a bound for large |G| extends to the
      finitely many smaller orders, since every graph has a clique cover of size at most |G|^2 / 4 (l.95-99).  The
      empty graph has the empty cover (0 <= C * 0).  The cover is a set of vertex sets: cliques may overlap, and a
      repeated clique never helps.  "K_{t,t}-free" is INDUCED (l.100), and only that reading is a question: a graph
      with no K_{t,t} SUBGRAPH has O(|G|^(2 - 1/t)) edges (Kovari, Sos and Turan), and one clique per edge covers
      them, eps = 1 / t.  TRUE at the pin: "Our main result is a proof of" Conjecture 1.5 (l.147-150), Theorem 1.6
      (l.152-163): for t >= 3, a cover of size at most (3/2) |G|^(2 - 1/(2t)) once |G| is large (s = t); for
      t = 2, size O(|G|^(3/2)); and t = 1 is the edgeless case (K_{1,1}-free graphs have no edge).  The pinned
      status open is for a separate literature item.  Related, from the same record:
      studies:std_javadi_hajebi_question_linear_clique_covers_for (graph-theory-misc, answered negatively there by
      Theorem 1.3, l.131-135), another package, not in this wave.  The exponent 2 * q - 1 is an exact natural
      subtraction, guarded by 0 < q. *)
Definition hajebi_ktt_free_subquadratic_clique_cover_statement : Prop :=
  forall t : nat, 1 <= t -> exists q C : nat, 0 < q /\
    forall G : sgraph, induced_free G ('K_t,t) ->
      exists cover : {set {set G}},
        [/\ forall A, A \in cover -> cliqueb A,
            forall x y : G, x -- y -> exists2 A, A \in cover & (x \in A) && (y \in A) &
            #|cover| ^ q <= C * #|G| ^ (2 * q - 1)].

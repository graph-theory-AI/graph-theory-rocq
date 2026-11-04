(** * GTMisc.conjectures.X285 -- v2 rows: weak Meyniel, hat guessing bounded by the Hadwiger number, hat guessing
    after adding a universal vertex, Locke's conjecture, and the studies synonym of Meyniel's conjecture *)

From GTBase Require Import base.
From GraphTheory Require Import coloring.
From GTMisc.foundations Require Import cops.
From GTMisc.conjectures Require Import X99 X227 X217.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X285 statements *****************************************************)

(** Corpus row: studies:std_weak_meyniel_s_conjecture
    Site: none
    Review: none
    English statement: (Weak Meyniel's Conjecture; studies slice of the corpus, record arXiv:1912.06957)
      There is an eps > 0 such that every graph G of order n has c(G) = O(n^(1-eps)).
    Definitions: [cop_number_le G k] - some j <= k such that j cops win on G, i.e. c(G) <= k (GTMisc
      foundations/cops.v); [cops_win G j] - the j cops capture after finitely many rounds (same file): the cops
      are placed first (several may share a vertex), then the robber; the cops move first; in each move every
      piece stays or slides along an edge; a cop landing on the robber captures him; [connected [set: G]] - G is
      connected (coq-graph-theory).
    Notes: encoded for CONNECTED graphs, with eps = 1/q: c(G)^q <= C n^(q-1) is c(G) <= C^(1/q) n^(1-1/q), a
      smaller eps only weakens the bound, and the bound for all n >= 1 is the same as for large n (c(G) <= n).
      Source: Hosseini, Mohar and Gonzalez Hermosillo de la Maza, "Meyniel's conjecture on graphs of bounded
      degree", arXiv:1912.06957v2 (21 November 2020, the last version before the pin), Revision.tex l.54-56
      (printed Conjecture 2: "every graph G of order n") and l.41-43 (the game as above).  Conjecture 2 itself
      prints no connectivity guard, while ordinary Meyniel (l.48-50, Conjecture 1) says connected, and the paper
      states no blanket convention.  The printed text read literally is FALSE: the edgeless graph on n vertices
      needs n cops (grounding_X285: g285_wm_not_trivially_true refutes the reading without the guard).  So the
      guard is not a quotation; it is the reading of the weak conjecture as a weakening of Meyniel's (l.52),
      as X217 encodes Meyniel's conjecture.  The guard 0 < #|G| excludes the empty graph, and 1 <= q keeps the
      truncating subtraction q - 1 exact.  OPEN at the pin: the paper proves only that Meyniel's conjecture for
      subcubic graphs implies the weak form with exponent 3/4 (l.229-231, printed Lemma 7) and a corollary of
      the same kind (l.249-251, printed Corollary 8), each with an o(1) slack in the exponent (l.227). *)
Definition weak_meyniel_cop_number_statement : Prop :=
  exists q C : nat, 1 <= q /\
    forall G : sgraph, 0 < #|G| -> connected [set: G] ->
      exists k : nat, k ^ q <= C * #|G| ^ (q - 1) /\ cop_number_le G k.

(** Corpus row: studies:std_hat_guessing_number_bounded_by_hadwiger_number_a
    Site: none
    Review: none
    English statement: (Open Problem: hat guessing number bounded by Hadwiger number; studies slice of the
      corpus, record arXiv:2112.09619)
      Whether the hat guessing number of graphs can be bounded in terms of their Hadwiger number h(G).
    Definitions: [x99_hadwiger_number G h] - the complete graph on h vertices is a minor of G and no larger
      complete graph is (GTMisc conjectures/X99.v); [x99_hat_guessing_number_at_most G k] - for no q > k do the
      players have a winning strategy, i.e. HG(G) <= k (same file); [x99_winning_hat_strategy G q] - a guess per
      vertex that depends only on the neighbours' hats and is right for at least one vertex on every assignment of
      q colours (same file).
    Notes: encoded as the affirmative answer, a FUNCTION of h(G): one f with HG(G) <= f(h(G)) for every graph.
      Source: Knierim, Martinsson and Steiner, "Hat guessing numbers of strongly degenerate graphs",
      arXiv:2112.09619v1 (17 December 2021, its only version before the pin), main.tex l.173 (the question,
      raised by Alon and Chizewer; h(G) is the largest t >= 1 with a K_t-minor) and l.102-104 (the game, HG(G) the
      largest q with a winning strategy).  Alon and Chizewer (arXiv:2107.05995v2, main.tex l.492-502) ask it as a
      consequence of a degeneracy bound, and distinguish it (l.117-130) from Bosek et al.'s HG(G) <= h(G), which
      is false (X99's hat_guessing_number_hadwiger_bound_statement, the case f = id).  On the empty graph
      X99's Hadwiger number is 0 and every bound holds.  OPEN at the pin: the paper answers yes only for graphs
      without a K_(2,s) subgraph (l.175-177, printed Corollary 1.5). *)
Definition hat_guessing_hadwiger_function_bound_statement : Prop :=
  exists f : nat -> nat,
    forall (G : sgraph) (h : nat), x99_hadwiger_number G h -> x99_hat_guessing_number_at_most G (f h).

(** Corpus row: arxiv:2107.05995#02
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2107.05995__02/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2107.05995__02.json
    English statement: (Alon and Chizewer, arXiv:2107.05995, Open Problems: hat guessing number after adding a
      universal vertex)
      Establish an upper bound for HG(G') as a function of HG(G), where G' is obtained from G by adding a single
      vertex connected to all vertices of G, or show that no such function exists.
    Definitions: [x227_hat_guessing_le G m] - every q for which the players win the q-colour hat game on G
      satisfies q <= m, i.e. HG(G) <= m (GTMisc conjectures/X227.v); [x227_hat_guessing_win],
      [x227_sees_only_neighbours] (same file); [add_node G [set: G]] - G plus one new vertex adjacent to every
      vertex of G (coq-graph-theory).
    Notes: encoded as the AFFIRMATIVE reading of a two-sided question: one f with HG(G') <= f(m) whenever
      HG(G) <= m; the other side ("no such function exists") is its negation.  Bounding by HG(G) itself or by
      any m >= HG(G) is the same up to replacing f by its running maximum.  Source: Alon and Chizewer, "On the hat
      guessing number of graphs", arXiv:2107.05995v2 (21 July 2021, the last version before the pin), main.tex
      l.508-526 (the question; G may be disconnected, l.515-519, so no connectivity guard) and l.82-93 (the game,
      neighbours' hats only, at least one correct guess).  The G_d(N) example (l.512-522) shows HG(G') = q^2 + q
      for arbitrarily large q; that is a lower bound on f, not a refutation.  OPEN at the pin. *)
Definition hat_guessing_add_universal_vertex_statement : Prop :=
  exists f : nat -> nat,
    forall (G : sgraph) (m : nat),
      x227_hat_guessing_le G m -> x227_hat_guessing_le (add_node G [set: G]) (f m).

(** Corpus row: studies:std_locke_s_conjecture
    Site: none
    Review: none
    English statement: (Locke's conjecture; studies slice of the corpus, record arXiv:1911.12471)
      There are only finitely many 3-connected triangle-free cubic n-vertex graphs G with alpha(G) < 3/8 n.
    Definitions: [k_connected G 3] - G has more than 3 vertices and stays connected after deleting any 2
      vertices (GTBase base.v); [triangle_free G] - no three pairwise adjacent vertices (GTBase base.v);
      [regular G 3] - every vertex has exactly 3 neighbours (GTBase base.v); [α([set: G])] - the independence
      number alpha(G), the largest size of a stable set of G (coq-graph-theory coloring, alpha_mem).
    Notes: encoded as stated, "finitely many graphs" as a bound N on the order: there are finitely many graphs of
      each order, so the two agree up to isomorphism.  alpha(G) < 3n/8 is 8 alpha(G) < 3n.  Source: Cames van
      Batenburg, Goedgebeur and Joret, "Large independent sets in triangle-free cubic graphs: beyond planarity",
      arXiv:1911.12471v2 (8 July 2020, the last version before the pin), Revision_IndependenceRatio8over3.tex
      l.196 (Locke's 1986 conjecture as quoted) and l.161 (cubic = 3-regular).  TRUE at the pin: their
      Corollary 8 (l.249-253) gives alpha(G) >= 3n/8 for every 2-connected triangle-free subcubic G except six
      named graphs F_11, F_14^(1), F_14^(2), F_19^(1), F_19^(2), F_22 of orders at most 22, so N = 22 suffices.
      It is NOT a no-exception statement: F_14^(1) is 3-connected, triangle-free and cubic with alpha = 5 < 42/8
      (grounding_X285: g285_locke_hyp_inhabited, on the source's figure file F_14_1-new.graphml). *)
Definition locke_finitely_many_statement : Prop :=
  exists N : nat, forall G : sgraph,
    k_connected G 3 -> triangle_free G -> regular G 3 -> 8 * α([set: G]) < 3 * #|G| -> #|G| <= N.

(** Corpus row: studies:std_meyniel_s_conjecture
    Site: none
    Review: none
    English statement: (Meyniel's conjecture; studies slice of the corpus, records arXiv:1912.06957 and five
      others)
      cop(G) = O(sqrt n) for every n-vertex connected graph G.
    Definitions: [meyniel_cop_number_sqrt_statement] - Meyniel's conjecture as encoded for the corpus row
      others:meyniels-conjecture (GTMisc conjectures/X217.v: some C with c(G) <= C * ceil(sqrt n) for every
      nonempty connected G).
    Notes: this studies row is the same conjecture as others:meyniels-conjecture, so it is a synonym of X217's
      statement (as X254 encodes the Tomescu duplicates), not a second encoding; CORPUS_FEEDBACK item 69 proposes
      the upstream alias.  OPEN at the pin. *)
Definition meyniel_cop_number_sqrt_duplicate_statement : Prop :=
  meyniel_cop_number_sqrt_statement.

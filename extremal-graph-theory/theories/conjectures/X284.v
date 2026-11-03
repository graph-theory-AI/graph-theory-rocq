(** * Extremal.conjectures.X284 -- v2 rows: rainbow cycles at logarithmic average degree, Erdos #584 (dense
      subgraphs whose edges lie on short cycles) *)

From GTBase Require Import base edge_colourings.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X284 statements ******************************************************* *)

(** Corpus row: arxiv:2309.04460#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2309.04460__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2309.04460__00.json
    English statement: (Alon, Bucic, Sauermann, Zakharov and Zamir, "Essentially tight bounds for rainbow cycles in
      proper edge-colourings", arXiv:2309.04460v2, Question 10.1)
      The log log n factor of Theorem 1.1 is necessary: for every constant C there are properly edge-coloured graphs
      on arbitrarily many vertices n with average degree at least C log n and no rainbow cycle.
    Definitions: [proper_edge_colouring col] - edges sharing a vertex get distinct colours (GTBase
      edge_colourings.v); [seq_cycle (--) c] - c lists the vertices of a cycle of G: distinct, more than two,
      consecutive ones adjacent, the last adjacent to the first (GTBase walks_paths.v); [seq_cycle_edge_list c] -
      the edges {c_i, c_(i+1)} of that cycle, the closing edge included (GTBase walks_paths.v); [E(G)] - the edge set
      of G (GTBase common.v).  As the source defines them (source.tex l.105, l.188-192): a colouring is proper
      when adjacent edges get distinct colours, a graph is rainbow when no colour appears on two of its edges,
      d(G) is the average degree and logarithms are natural.
    Notes: encoded as the affirmative answer (the corpus precedent for question rows), in the reading the source
      sets against it: Section 10 (l.783-803) asks whether the factor is necessary and names the alternative "an
      average degree on the order of log n suffices to guarantee a rainbow cycle" (l.795); the statement is exactly
      the negation of that alternative (for every C, average degree C log n does not force a rainbow cycle).  It is
      NOT the stronger matching lower bound Omega(log n log log n), which it does not claim: a threshold of order
      log n (log log n)^(1/2), say, would answer this reading yes and the stronger one no.  Theorem
      1.1 (l.113-115) is the bound C log n log log n for n >= 3; KMSV's lower bound Omega(log n) is l.106.  The
      average degree is 2|E(G)| / n, so "at least C log n" is C n floor(log2 n) <= 2 |E(G)|, written for every L with
      2^L <= n (X229's rendering of the sibling row #01).  For n >= 2, floor(log2 n) and ln n are within constant
      factors of each other, so the universal C absorbs the base and the rounding.  N makes the orders unbounded:
      K_1 meets every degree bound vacuously, and a witness for a large C has many vertices anyway (d(G) <= n - 1).
      Colours are natural numbers: a finite graph uses finitely many colours, so any palette injects into nat.
      Literature status: OPEN at the pin (pinned review 2026-05-14; the Mac's bounded pre-pin search found no
      answer).  The sibling row arxiv:2309.04460#01 is Question 10.2 (Extremal X229). *)
Definition rainbow_cycle_log_degree_insufficient_statement : Prop :=
  forall C N : nat, exists (G : sgraph) (col : {set G} -> nat),
    [/\ N <= #|G|, proper_edge_colouring col,
        forall L : nat, 2 ^ L <= #|G| -> C * (#|G| * L) <= 2 * #|E(G)| &
        forall c : seq G, seq_cycle (--) c -> ~~ uniq (map col (seq_cycle_edge_list c))].

(** Corpus row: erdos:584
    Site: none
    Review: none
    English statement: (Erdos Problems #584; Duke, Erdos and Rodl)
      There is an absolute constant c > 0 such that every graph G with n vertices and delta n^2 edges has subgraphs
      H_1 and H_2 such that H_1 has at least c delta^3 n^2 edges, every two edges of H_1 lie on a cycle of length at
      most 6 in H_1, and every two edges of H_1 sharing a vertex lie on a cycle of length 4 in H_1; and H_2 has at
      least c delta^2 n^2 edges, every two edges of H_2 lying on a cycle of length at most 8 in H_2.
    Definitions: [E(G)] - the edge set of G, as two-element vertex sets (GTBase common.v); [seq_cycle r c] - c lists
      the vertices of a cycle of the relation r: distinct, more than two, consecutive ones related, the last related
      to the first (GTBase walks_paths.v); [seq_cycle_edge_list c] - the edges {c_i, c_(i+1)} of that cycle, the
      closing edge included (GTBase walks_paths.v).  A subgraph H_i is a set of edges of G; its cycles are the cycles
      of the relation "{x, y} is an edge of H_i".
    Notes: the pinned statement is the erdosproblems.com text ("Let G be a graph with n vertices and delta n^2
      edges. Are there subgraphs H_1, H_2 of G such that ..."); encoded as the affirmative answer.  Reading of
      delta (the literal reading of the pinned text): delta = |E(G)| / n^2 ranges over every density and one
      absolute constant d = 1 / c serves every graph; then ">> delta^3 n^2" is |E(G)|^3 <= d |H_1| n^4 and
      ">> delta^2 n^2" is |E(G)|^2 <= d |H_2| n^2.  No density guard is added.  The page's remark ("The real
      challenge is to prove this when delta = n^-c for some c > 0") shows that the question is meant beyond a fixed
      delta; it asks for a polynomially small range with an exponent still to be chosen (as Fox and Sudakov's
      Problem 1.1 sets it, arXiv:0706.1920v3 source.tex l.95-102: c, beta_0 > 0 and every beta <= beta_0), so the
      encoded every-density reading is STRONGER than that challenge.  Under the other reading, delta a constant and
      n large depending on delta, the H_1 part is Duke and Erdos's Corollary 1 (DuEr82, Congr. Numer. 35, p.255) and
      the H_2 part Duke, Erdos and Rodl's fixed-density theorem (as Fox and Sudakov report, l.113-119), so that
      reading is solved.
      Every order n is quantified: the finitely many orders below a threshold n0 are covered by a one-edge H_i once
      d >= n0^2, so this equals the "n sufficiently large" form.  The cycles lie inside H_i (DuEr82 p.253 "a cycle
      of H", DER84 Congr. Numer. 43, p.295 "in G_2"); a cycle's length is its number of edges, equal to its number
      of vertices; "two edges" are two distinct edges, and two distinct edges sharing a vertex meet in one vertex.
      An edgeless G is met by the empty H_i.  Known parts, all before the pin: DER84 (p.295-296; Theorems 1-3,
      p.296-299) proves, for n^(2-eps) edges with 0 < eps < 1/2 and n large, the H_1 bound c n^(2-3eps) without the
      C_4 clause (Theorem 1), c n^(2-5eps) with it (Theorem 3), and H_2 with cycles of length at most 12 (Theorem
      2); Fox and Sudakov (0706.1920v3, Theorem 1.2, l.130-135) prove the H_2 bound n^(2-2beta) / 64, in the strong
      form, for 0 < beta < 1/5 and n large.  Under this reading the statement is FALSE before the pin, by its H_2
      clause: in a graph with no cycle of length at most 8, an H_2 has at most one edge (two distinct edges would need
      such a cycle inside H_2), so the body asks |E(G)|^2 <= d n^2 of every such graph, while such graphs with
      |E(G)| / n unbounded exist (Erdos's high-girth graphs; Fox and Sudakov, l.357-359, state the negative answer
      for beta close to 1, "for such beta the answer to this problem is negative", writing "no 8-cycle").  Eric Li
      (arXiv:2606.06522v1, 2 June 2026, main_7.tex l.133-146) adds the H_1 clause: for each fixed beta in [1/3, 1/2),
      bipartite graphs of density Theta(n^-beta) whose internally strongly C_6-connected subgraphs have
      O(delta^3 n^2 / (log n)^2) edges (theorem statements read, proofs not verified).  Historical body kept.
      Literature status: pinned open; the status is Lancelot's literature item after X284 (question 10 of his
      2026-11-03 daily); no kernel disproof is claimed. *)
Definition erdos_584_short_cycle_subgraphs_statement : Prop :=
  exists d : nat, 0 < d /\ forall G : sgraph,
    (exists2 H1 : {set {set G}}, H1 \subset E(G) &
       [/\ #|E(G)| ^ 3 <= d * (#|H1| * #|G| ^ 4),
           forall e f, e \in H1 -> f \in H1 -> e != f ->
             exists2 c : seq G, seq_cycle (fun x y => [set x; y] \in H1) c &
               [/\ size c <= 6, e \in seq_cycle_edge_list c & f \in seq_cycle_edge_list c] &
           forall e f, e \in H1 -> f \in H1 -> e != f -> e :&: f != set0 ->
             exists2 c : seq G, seq_cycle (fun x y => [set x; y] \in H1) c &
               [/\ size c = 4, e \in seq_cycle_edge_list c & f \in seq_cycle_edge_list c]]) /\
    (exists2 H2 : {set {set G}}, H2 \subset E(G) &
       #|E(G)| ^ 2 <= d * (#|H2| * #|G| ^ 2) /\
       forall e f, e \in H2 -> f \in H2 -> e != f ->
         exists2 c : seq G, seq_cycle (fun x y => [set x; y] \in H2) c &
           [/\ size c <= 8, e \in seq_cycle_edge_list c & f \in seq_cycle_edge_list c]).

(** * Extremal.conjectures.X260 -- wave X260: the number of maximal-clique sizes, and graph-codes (2026-10-29)

    A three-row wave under the prospective contract of meta/faithfulness_policy.json.  Rows: erdos:927 (g(n), the
    largest number of distinct sizes of maximal cliques in a graph on n vertices, against n - log_2 n - log_*(n) + O(1),
    as stated), arxiv:2301.13305#00 (Alon's Question 1.1 on graph-codes, in the source's own "Equivalently" form) and
    arxiv:2301.13305#01 (its instance H = K_4).  Cliques are GTBase's inclusion-maximal [maximal_clique]; logarithms
    are MathComp's [trunc_log 2] (floor of log_2) and a local iterated logarithm.  No shared notion of an exact copy
    exists: edge_colourings' [mono_copy] and D7's [is_copy] are injective homomorphisms, which give containment of the
    image edges, while a graph-code forbids a symmetric difference that IS a copy of H.  The wave therefore defines two
    local families: the clique-size count with its extremal number and the iterated logarithm, and the exact copy with
    the code.  Literature lines are dated against the corpus pin (graph-conjectures b72c5857, 2026-09-23).  The
    sources are the Mac's deposit coordination/sources/x260-source-mac-20261029 (text line numbers below).  The
    grounding certificates are in grounding_X260.v. *)

From GTBase Require Import base common maximal_cliques.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x260 vocabulary ************************************************* *)

(** The number of distinct sizes of maximal cliques of G; each size is at most #|G|, so the sizes are counted inside
    'I_(#|G|+1). *)
Definition x260_clique_size_count (G : sgraph) : nat :=
  #|[set k : 'I_#|G|.+1 | [exists S : {set G}, maximal_clique S && (#|S| == k)]]|.

(** a = g(n): some graph on n vertices has a distinct maximal-clique sizes, and no graph on n vertices has more. *)
Definition x260_clique_size_number (n a : nat) : Prop :=
  (exists G : sgraph, #|G| = n /\ x260_clique_size_count G = a) /\
  (forall G : sgraph, #|G| = n -> x260_clique_size_count G <= a).

(** The iterated logarithm: the least k such that k applications of the floor of log_2 bring n to 0, searched among
    0, ..., n (k = n always qualifies, as trunc_log 2 m < m for m >= 1).  For n >= 1 this is the least k with
    log_2 ... log_2 n < 1 (k logarithms), since the floor of log_2 of the floor of x is the floor of log_2 x. *)
Definition x260_log_star (n : nat) : nat :=
  find (fun k => iter k (trunc_log 2) n == 0) (iota 0 n.+1).

(** S, a set of edges of K_n, is a copy of H: the image of E(H) under an injective map of the vertices of H, exactly
    (an edge set equal to the image, not a superset). *)
Definition x260_copy (n : nat) (H : sgraph) (S : {set {set 'K_n}}) : Prop :=
  exists f : H -> ('K_n), injective f /\ S = [set f @: e | e : {set H} in E(H)].

(** F is an H-code: a family of graphs on [n] (each an edge set of K_n) in which no two distinct members have a
    symmetric difference that is a copy of H. *)
Definition x260_code (n : nat) (H : sgraph) (F : {set {set {set 'K_n}}}) : Prop :=
  (forall A, A \in F -> A \subset E('K_n)) /\
  forall A B, A \in F -> B \in F -> A != B -> ~ x260_copy H ((A :\: B) :|: (B :\: A)).

(** ** X260 statements ******************************************************* *)

(** Corpus row: erdos:927
    Site: none
    Review: none
    English statement: (Erdos Problems #927, Moon and Moser; Erdos)
      Let g(n) be the maximum number of different sizes of cliques that can occur in a graph on n vertices.  Estimate
      g(n) - in particular, is it true that g(n) = n - log_2 n - log_*(n) + O(1), where log_*(n) is the number of
      iterated logarithms such that log ... log n < 1.
    Definitions: [x260_clique_size_number n a] - a = g(n), the largest number of distinct sizes of maximal cliques
      over the graphs on n vertices (this file); [x260_clique_size_count G] - the number of distinct sizes of maximal
      cliques of G (this file); [maximal_clique S] - S is an inclusion-maximal clique (GTBase.maximal_cliques);
      [trunc_log 2 n] - the floor of log_2 n (MathComp); [x260_log_star n] - the least k with k-fold floor-log_2 of n
      equal to 0 (this file).
    Notes: the asked formula is encoded as stated, two-sided with a constant C beyond some N; "Estimate g(n)" is not
      formalised.  Cliques are maximal complete subgraphs, as in every source: Erdos, On cliques in graphs, Israel J.
      Math. 4 (1966) 233-234 ("A complete subgraph of G is called a clique if it is maximal", Er66b.txt l.18-20, with
      g(n) at l.21); Moon and Moser's abstract (MoMo65.publisher.txt l.40); Er71 p.101 (Er71.txt l.12).  On the
      all-cliques reading K_n alone would give g(n) = n.  Er66b takes cliques nonempty (l.17), which changes only g(0),
      1 here (the empty graph's one maximal clique is set0, grounding_X260's g260_number_0) and 0 there. The three
      readings of O(1) in the encoding: (i) trunc_log 2 n is the floor of log_2 n, within 1 of it (2^t <= n < 2^(t+1),
      MathComp's trunc_logP); (ii) for n >= 1 the integer x260_log_star n EQUALS the real iterated count with the page's
      "< 1": by induction the k-th integer iterate is the floor of the k-th real one while the previous real iterate is
      at least 1, as floor(log_2 floor(x)) = floor(log_2 x), so the first real iterate below 1 is the first integer
      iterate equal to 0; (iii) the base, unnamed on the page (Er66b and Gao take log_2, Er71 log), and the stopping
      threshold (Er66b stops below 2, Er69b below 1, Er71 at 1 < log_k n <= e) change log_* n by a bounded amount: with
      towers 2^^k and e^^k, e^^k <= 2^^(k+2) (2^^(k+2) >= 2 (e^^k): directly for k <= 1, then by induction as 4^b >= 2
      e^b for b >= 2), so the counts to bases 2 and e differ by at most 2, and moving the threshold from 1 to 2 or e
      shifts the count by at most 2.  The row is FALSE at the pin (pinned prize "DISPROVED"): Spencer proved g(n) > n -
      log_2 n - O(1), which the page reports (erdos-927.txt l.37-39) and Er71 already records ("Note added in proof:
      Spencer proved f(n) > n - log n / log 2 - c", Er71.txt l.191-193, p.101); Gao, arXiv:2510.14804v3, introduction
      (main.tex l.146-153), says Spencer "disproved" Erdos's lower bound g(n) > n - log n - log_* n - O(1) (Er66b's
      theorem, l.32) as the true order.  The Spencer paper itself is not in the deposit.  This refutes the encoded
      clause: for n >= N with g(n) = a, a >= n - log_2 n - c, so a + trunc_log 2 n + x260_log_star n >= n - c - 1 +
      x260_log_star n, which exceeds n + C once log_* n > C + c + 1; log_* is unbounded, and g(n) exists for every n (a
      graph on n vertices has at most n + 1 clique sizes, and the maximum over the finitely many graphs on n vertices up
      to isomorphism is attained).  The upper half is Moon and Moser's g(n) <= n - floor(log_2 n) (erdos-927.txt
      l.32-34; Er66b.txt l.24-25), so g(n) = n - log_2 n + O(1). No (i)-(iii) choice changes this: each changes the left
      side by O(1) while log_* n grows. *)

Definition maximal_clique_sizes_statement : Prop :=
  exists C N : nat, forall n a : nat, N <= n -> x260_clique_size_number n a ->
    n <= a + trunc_log 2 n + x260_log_star n + C /\
    a + trunc_log 2 n + x260_log_star n <= n + C.

(** Corpus row: arxiv:2301.13305#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2301.13305__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2301.13305__00.json
    English statement: (Alon, Graph-codes, Question 1.1)
      Let H be a family of graphs closed under isomorphism.  Is it true that d_H(n) tends to 0 as n tends to infinity
      if and only if H contains a graph with an even number of edges?  Equivalently: is it true that for any fixed graph
      H with an even number of edges, d_H(n) tends to 0 as n tends to infinity?
    Definitions: [x260_code n H F] - F is an H-code: a family of graphs on [n] (edge sets of K_n) in which no two
      distinct members have a symmetric difference that is a copy of H (this file); [x260_copy n H S] - the edge set S
      is exactly the image of E(H) under an injective map of the vertices of H into [n] (this file); [edge_count H] -
      the number of edges (GTBase.common).
    Notes: the source's own "Equivalently" form is encoded: for every fixed H with a positive even number of edges and
      every q >= 1, eventually q |F| <= 2^C(n,2) for every H-code F on [n], i.e. d_H(n) <= 1/q, where d_H(n) is the
      largest |F| / 2^C(n,2) (Alon, Graph-codes, arXiv:2301.13305v2, source.tex l.92-100).  The threshold N may depend
      on H and q, as the source fixes H first ("for any fixed graph H ... d_H(n) tends to 0"), so the existential after
      the graph quantifier is per H, not uniform over graphs.  The guard 0 < edge_count H is the source's: "Let H be a
      fixed graph with an even (positive) number of edges" (abstract, l.59-60), and "for any fixed nonempty graph H with
      an even number of edges" (concluding remarks, l.470-474).  Without it the edgeless H would make every family a
      code (two distinct members never have an empty symmetric difference), so d_H(n) = 1.  A copy of H: Alon's codes
      avoid symmetric differences that are "all copies of a single graph H on [n]" (l.89-91), and Versteegen,
      arXiv:2310.19891v2 (linear_graph_codes.tex l.98), makes it exact: G is a copy of H if some S has G[S] isomorphic
      to H and every vertex outside S is isolated in G.  That is x260_copy: the edge set of the difference is the image
      of E(H), not a superset; isolated vertices of H take part in the embedding, so there is no copy when n < |V(H)|. 
      The family form is equivalent, as the source says: a family containing an even-edge H0 has d at most d_H0 (a code
      for the family is an H0-code), and conversely the parity remark, "if every member of H has an odd number of edges
      then d_H(n) >= 1/2 as the family of all graphs on [n] with an even number of edges forms an H-code" (l.135-137),
      gives the other direction.  Status: open at the pin, encoded as asked ("remains wide open", l.470-474). 
      Versteegen's O(2^C(n,2) / log n) bound (l.90-91) is for linear graph codes only, so it settles neither this row
      nor #01. *)

Definition graph_codes_even_edges_statement : Prop :=
  forall H : sgraph, 0 < edge_count H -> ~~ odd (edge_count H) ->
    forall q : nat, 1 <= q -> exists N : nat, forall n : nat, N <= n ->
      forall F : {set {set {set 'K_n}}}, x260_code H F -> q * #|F| <= 2 ^ 'C(n, 2).

(** Corpus row: arxiv:2301.13305#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2301.13305__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2301.13305__01.json
    English statement: (Alon, Graph-codes, concluding remarks)
      Is it true that d_{K_4}(n) = o(1)?
    Definitions: [x260_code n H F] - F is an H-code on [n] (this file); [x260_copy n H S] - S is exactly a copy of
      H's edge set (this file); ['K_4] - the complete graph on 'I_4 (GraphTheory).
    Notes: #00 at H = K_4 (six edges), with the same encoding: for every q >= 1, eventually q |F| <= 2^C(n,2) for
      every K_4-code F on [n].  "An interesting special case is whether or not d_{K_4}(n) = o(1)" (Alon,
      arXiv:2301.13305v2, source.tex l.476).  Versteegen restates it as Question 1.1 (2310.19891v2,
      linear_graph_codes.tex l.104-106), open; his bound covers linear codes only.  The companion lower bound
      d_{K_4}(n) >= 1/n^{o(1)} is proved in Alon's revised version from an edge colouring that Hunter and Mubayi
      pointed out (l.477-490).  Status: open at the pin, encoded as asked.  That #00 implies #01 (instantiate
      H := K_4) is an implication edge for later, not part of this wave. *)

Definition graph_codes_K4_statement : Prop :=
  forall q : nat, 1 <= q -> exists N : nat, forall n : nat, N <= n ->
    forall F : {set {set {set 'K_n}}}, x260_code 'K_4 F -> q * #|F| <= 2 ^ 'C(n, 2).

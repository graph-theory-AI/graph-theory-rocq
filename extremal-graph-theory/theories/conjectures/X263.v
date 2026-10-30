(** * Extremal.conjectures.X263 -- v2 rows: comparability graphs of set families, regular induced subgraphs *)

From GTBase Require Import base common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X263 vocabulary ***********************************************)

(** The number of edges of G_F, the comparability graph of a family F of subsets of [n]: the ordered pairs (A, B)
    of members with A a proper subset of B, one for each unordered pair of distinct comparable members. *)
Definition x263_comparable_pairs (n : nat) (F : {set {set 'I_n}}) : nat :=
  #|[set p : {set 'I_n} * {set 'I_n} | [&& p.1 \in F, p.2 \in F & p.1 \proper p.2]]|.

(** ** X263 statements *****************************************************)

(** Corpus row: erdos:777
    Site: none
    Review: none
    English statement: (Erdos Problems #777, a problem of Daykin and Erdos [Gu83])
      If F is a family of subsets of {1, ..., n} then we write G_F for the graph on F where A ~ B if A and B are
      comparable - that is, A is a subset of B or vice versa.  Is it true that, if eps > 0 and n is sufficiently
      large, whenever m <= (2 - eps) 2^(n/2) the graph G_F has < 2^n many edges?  Is it true that if G_F has
      >= c m^2 edges then m <<_c 2^(n/2)?  Is it true that, for any eps > 0, there exists some delta > 0 such that if
      there are > m^(2 - delta) edges then m < (2 + eps)^(n/2)?
    Definitions: [x263_comparable_pairs n F] - the number of edges of G_F (this file); m = #|F|.
    Notes: the three asked clauses are encoded as stated, as a conjunction (the erdos:720 / 1015 precedent, X255),
      with eps = 1/p, c = 1/p and delta = 1/q, squared and cross-multiplied (no reals; a smaller eps, c or delta gives
      a stronger clause, so p, q >= 1 cover every real value): (1) for n >= N, p^2 m^2 <= (2p - 1)^2 2^n forces
      fewer than 2^n edges; (2) m^2 <= p edges forces m^2 <= K 2^n; (3) m^(2q - 1) < edges^q forces
      p^n m^2 < (2p + 1)^n, for every n as asked: since edges < m^2 / 2, the hypothesis gives 2^q < m <= 2^n, so a
      larger q absorbs any threshold in n.  The nat subtractions 2p - 1 and 2q - 1 are guarded by 1 <= p and
      1 <= q (no truncation).  The row is FALSE at the pin: the second clause is refuted.  Alon and Frankl, The
      maximum number of disjoint pairs in a family of subsets, Graphs Combin. 1 (1985), Example 6.1 (printed p.21):
      with X = X1 + X2 split in halves, the sets F with |F meet X2| <= d or |X1 - F| <= d number
      Omega(2^(n/2) n^d) and have c >= 2^(-2d-1) C(m, 2) comparable pairs; with d = 1 the clause fails at c = 1/32.
      The first clause holds for sufficiently large n (the page: Alon, Das, Glebov and Sudakov, arXiv:1411.4196v1,
      Theorem 1.4 and Corollary 1.5) and the third is answered in the affirmative by Alon and Frankl (Section 2:
      m = 2^((1/2 + delta) n) gives c < 4 m^(2 - delta^2 / 2)).  The quantifiers follow the pinned page; Guy's
      original (Gu83) was not read.  The pinned status SOLVED ("resolved in some other way than a proof or
      disproof") matches the mixed answers. *)
Definition set_family_comparability_statement : Prop :=
  [/\ (forall p : nat, 1 <= p -> exists N : nat, forall (n : nat) (F : {set {set 'I_n}}), N <= n ->
         p ^ 2 * #|F| ^ 2 <= (2 * p - 1) ^ 2 * 2 ^ n -> x263_comparable_pairs F < 2 ^ n),
      (forall p : nat, 1 <= p -> exists K : nat, forall (n : nat) (F : {set {set 'I_n}}),
         #|F| ^ 2 <= p * x263_comparable_pairs F -> #|F| ^ 2 <= K * 2 ^ n) &
      (forall p : nat, 1 <= p -> exists q : nat, 1 <= q /\ forall (n : nat) (F : {set {set 'I_n}}),
         #|F| ^ (2 * q - 1) < x263_comparable_pairs F ^ q -> p ^ n * #|F| ^ 2 < (2 * p + 1) ^ n)].

(** Corpus row: erdos:1031
    Site: none
    Review: none
    English statement: (Erdos Problems #1031, a question of Erdos, Fajtlowicz and Staton [Er93, p.340])
      If G is a graph on n vertices which contains no trivial (empty or complete) subgraph on >= 10 log n many
      vertices, then must G contain an induced non-trivial regular subgraph on >> log n many vertices?
    Definitions: [cliqueb S], [stable S] - S is a clique, a stable set (upstream coq-graph-theory); [induced S] -
      G[S] (upstream); [regular G d] - every vertex has exactly d neighbours (GTBase.base).
    Notes: affirmative, as the row is PROVED at the pin.  Trivial subgraphs are induced (a non-induced empty
      subgraph exists on every vertex set): cliques and stable sets.  Base 2, exactly: a set of k vertices has at
      least 10 log_2 n vertices iff n^10 <= 2^k, and log_2 n <= q k iff n <= 2^(q k); no rounding enters the
      hypothesis.  Er93's own log convention is unverified (p.340 was not obtainable).  Base 2 gives the larger
      threshold, so the weaker hypothesis and the stronger statement: it implies the natural-log reading.
      Non-trivial: G[S] is d-regular with 0 < d (not empty) and d + 1 < #|S| (not complete, which is
      (#|S| - 1)-regular).  ">> log n": some constant q and every n >= N.  N is load-bearing: the least n >= 2
      with n^10 <= 2^n is 59, so for 2 <= n <= 58 no set meets the threshold, the hypothesis holds vacuously, and
      K_n (whose regular induced subgraphs are all complete) refutes the clause there.  Promel and Rodl,
      Non-Ramsey graphs are c log n-universal, J. Combin. Theory Ser. A 88 (1999) 379-384, read only in its
      publisher abstract (the full text was not obtainable): for every c1 > 0 there is c2 > 0 such that a graph on
      n vertices with neither a clique nor a stable set of size c1 log n contains every graph on c2 log n vertices
      as an induced subgraph; the page states the same for any c > 0.  With c1 log n = 10 log_2 n in their base,
      the hypothesis here gives theirs, so G contains an induced cycle on k = floor(c2 log n) vertices, 2-regular
      and non-trivial once k >= 4, with log_2 n <= q k for a constant q: the clause for large n.  No small-n
      instance is claimed. *)
Definition regular_induced_subgraph_statement : Prop :=
  exists q N : nat, forall G : sgraph, N <= #|G| ->
    (forall S : {set G}, #|G| ^ 10 <= 2 ^ #|S| -> ~~ cliqueb S && ~~ stable S) ->
    exists (S : {set G}) (d : nat),
      [/\ regular (induced S) d, 0 < d, d.+1 < #|S| & #|G| <= 2 ^ (q * #|S|)].

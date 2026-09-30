(** * Extremal.conjectures.X215 -- Bondy-Murty Appendix A extremal/Ramsey rows (wave X215, 2026-09-23) *)

From GTBase Require Export base.
From Extremal.foundations Require Import edge_colourings.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x215 vocabulary ***********************************************

    Only the diagonal-Ramsey arrow relation is new here; trees, cycles, edge
    sets, subgraph containment and monochromatic copies all come from
    coq-graph-theory / GTBase / [Extremal.foundations.edge_colourings]. *)

(** [x215_arrows N k]: K_N -> (K_k, K_k), i.e. every 2-colouring of the edges of
    the complete graph on [N] vertices has a monochromatic copy of [K_k].  The
    diagonal Ramsey number r(k,k) is the least such [N] ([x215_ramsey_number]). *)
Definition x215_arrows (N k : nat) : Prop :=
  forall col : {set 'K_N} -> bool, exists c : bool, mono_copy 'K_k col c.

(** [x215_ramsey_number k N]: [N] IS the diagonal Ramsey number r(k,k). *)
Definition x215_ramsey_number (k N : nat) : Prop :=
  x215_arrows N k /\ forall M : nat, M < N -> ~ x215_arrows M k.

(** ** X215 statements *****************************************************)

(** Corpus row: bm:bm-033
    Site: https://graph-theory-ai.github.io/graph-conjectures/bm/bm-033/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/bondy_murty_reviews/bm-033.json
    English statement: (Erdos and Sos 1963, Bondy-Murty Appendix A #33)
      Let T be a tree with k edges, hence with k+1 vertices, and let G be a finite simple
      graph whose number of edges m and number of vertices n satisfy n * k < 2 * m + n,
      that is m > n * (k - 1) / 2.  Then G contains T as a (not necessarily induced)
      subgraph.
    Definitions: [is_tree [set: T]] - T is a connected forest (coq-graph-theory);
      [E(G)] = [sg_edge_set G] - the undirected edge set, so #|E(G)| is the number of
      edges (coq-graph-theory); [has_subgraph G T] - T embeds into G by an injective
      adjacency-preserving map (GTBase.common).
    Notes: the source guard "m > n(k-1)/2" is cleared of the division and of natural
      subtraction as [#|G| * k < 2 * #|E(G)| + #|G|], which is equivalent to
      2m > n(k-1) over the rationals for every k >= 1 and, for k = 0, to the (true)
      requirement that G be non-empty.  "Tree with k edges" is rendered by the PAIR of
      hypotheses [#|E(T)| = k] and [#|T| = k.+1]: for a tree the two are equivalent
      (a tree on k+1 vertices has k edges), so the pair selects exactly the trees with
      k edges and neither strengthens nor weakens the hypothesis class; the vertex-count
      half is stated explicitly because coq-graph-theory does not carry the
      |E(T)| = |V(T)| - 1 lemma, and the X215 implication edge (e239) needs it. *)
Definition erdos_sos_tree_embedding_statement : Prop :=
  forall (G T : sgraph) (k : nat),
    is_tree [set: T] ->
    #|E(T)| = k ->
    #|T| = k.+1 ->
    #|G| * k < 2 * #|E(G)| + #|G| ->
    has_subgraph G T.

(** Corpus row: bm:bm-034
    Site: https://graph-theory-ai.github.io/graph-conjectures/bm/bm-034/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/bondy_murty_reviews/bm-034.json
    English statement: (Erdos, Bondy-Murty Appendix A #34)
      For every k >= 2 there are positive integers p, q and a threshold n0 such that for
      every n >= n0 some finite simple graph G on n vertices contains no cycle of length
      2k as a subgraph and has p^k * n^(k+1) <= q^k * |E(G)|^k, i.e. it has at least
      (p/q) * n^(1 + 1/k) edges.  Equivalently: the Turan number ex(n, C_2k) is at least
      c * n^(1+1/k) for a positive constant c and all large n.
    Definitions: [cycle_graph m] - the cycle C_m on 'I_m (GTBase.base);
      [has_subgraph G C] - C embeds into G by an injective adjacency-preserving map, so
      [~ has_subgraph G (cycle_graph (2*k))] is "G has no C_2k" (GTBase.common);
      [E(G)] - the undirected edge set (coq-graph-theory).
    Notes: ex(n, C_2k) is NOT defined as a maximum (graphs on a fixed vertex set do not
      form a finite type here); a LOWER bound on it is stated in the equivalent
      existential form "some C_2k-free graph on n vertices has at least that many edges".
      The real constant c > 0 is taken rational, c = p/q with p, q positive integers, and
      the exponent 1 + 1/k is cleared by raising the inequality |E(G)| >= c * n^(1+1/k)
      to the k-th power: q^k * |E(G)|^k >= p^k * n^(k+1).  The threshold n0 is explicit
      because the bound cannot hold at n = 1 for any positive c. *)
Definition even_cycle_turan_lower_bound_statement : Prop :=
  forall k : nat, 2 <= k ->
    exists p q n0 : nat,
      [/\ 0 < p, 0 < q &
          forall n : nat, n0 <= n ->
            exists G : sgraph,
              [/\ #|G| = n,
                  ~ has_subgraph G (cycle_graph (2 * k)) &
                  p ^ k * n ^ k.+1 <= q ^ k * #|E(G)| ^ k]].

(** Corpus row: bm:bm-037
    Site: https://graph-theory-ai.github.io/graph-conjectures/bm/bm-037/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/bondy_murty_reviews/bm-037.json
    English statement: (Erdos, Bondy-Murty Appendix A #37)
      There are positive integers p > q such that, writing c = p/q > 1, for every k >= 1
      and every N with N * q^k < p^k there is a 2-colouring of the edges of the complete
      graph on N vertices with no monochromatic copy of K_k; that is, r(k,k) >= c^k.
    Definitions: [x215_arrows N k] - every 2-colouring of E(K_N) has a monochromatic K_k
      (this file); [mono_copy F col c] - an injective adjacency-preserving copy of F all
      of whose edges have colour c (Extremal.foundations.edge_colourings).
    Notes: BLOCKED. The row asks for a CONSTRUCTIVE proof that r(k,k) >= c^k. Constructivity
      (an explicit family, or an algorithm producing the colouring) is a property of a PROOF,
      not of a proposition, and expressing it needs the computation model these waves keep out
      of scope. The body above is therefore a PLACEHOLDER: it states only the underlying
      inequality, which is not the open problem at all but Erdos' 1947 probabilistic theorem
      (c = sqrt 2). No source-verification tuple is claimed for this row.
      SECOND-READER READBACK (2026-09-23): the placeholder is WORSE than "a known theorem
      instead of the open problem" -- it is axiom-free REFUTABLE, and so states a FALSE
      proposition.  Its guard [0 < k] admits k = 1, where r(1,1) = 1 while c^1 = c > 1;
      concretely, instantiating the body at k = 1, N = 1 turns its own hypothesis
      [N * q ^ k < p ^ k] into [q < p], which the statement itself asserts, and therefore
      demands [~ x215_arrows 1 1] -- contradicting the Qed lemma [x215_arrows_1_1] that this
      wave's own grounding_X215.v proves.  The refutation is recorded in
      meta/probe_hints/constructive_diagonal_ramsey_lower_bound_statement.v and is
      "Closed under the global context".  The row stays BLOCKED (its real content, the
      constructivity of the proof, is out of scope either way); a body that at least stated
      a true proposition would need the guard [1 < k], since the Erdos bound only holds
      from k = 2 on (r(2,2) = 2 forces c <= sqrt 2). GUARD REPAIR (2026-09-23, main session): the placeholder now
      requires [1 < k]; with [0 < k] it was refutable at k = 1 (r(1,1) = 1, see
      meta/probe_hints/constructive_diagonal_ramsey_lower_bound_statement.v, kept
      as a regression check). It remains a BLOCKED placeholder: Erdos' bound
      r(k,k) >= c^k for k >= 2 is a theorem, and the constructivity the row asks
      for is not a proposition of this development. *)
Definition constructive_diagonal_ramsey_lower_bound_statement : Prop :=
  exists p q : nat,
    [/\ 0 < q, q < p &
        forall k N : nat, 1 < k -> N * q ^ k < p ^ k -> ~ x215_arrows N k].

(** Corpus row: bm:bm-038
    Site: https://graph-theory-ai.github.io/graph-conjectures/bm/bm-038/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/bondy_murty_reviews/bm-038.json
    English statement: (Erdos, Bondy-Murty Appendix A #38)
      There is a rational number L = p/q such that for every rational tolerance a/b > 0
      there is k0 with, for every k >= k0 and the diagonal Ramsey number N = r(k,k),
      (p*b - q*a)^k <= N * (q*b)^k <= (p*b + q*a)^k; that is, r(k,k)^(1/k) converges to L.
    Definitions: [x215_arrows N k] and [x215_ramsey_number k N] - the Ramsey arrow relation
      and "N is r(k,k)" (this file); [mono_copy] (Extremal.foundations.edge_colourings).
    Notes: BLOCKED. The row asks whether lim_k r(k,k)^(1/k) EXISTS and, if so, what its value
      is. The existence of a limit of a real sequence needs a reals layer that GTBase does not
      have, and the "determine its value" half records no conjectured value at all. The body
      above is a PLACEHOLDER that forces the limit to be RATIONAL, which is a strictly
      different (and possibly false) proposition - a wrong-object encoding, kept only so the
      row compiles and carries its vocabulary. No source-verification tuple is claimed. *)
Definition diagonal_ramsey_root_limit_statement : Prop :=
  exists p q : nat,
    0 < q /\
    forall a b : nat, 0 < a -> 0 < b ->
      exists k0 : nat,
        forall k N : nat, k0 <= k -> x215_ramsey_number k N ->
          (p * b - q * a) ^ k <= N * (q * b) ^ k /\
          N * (q * b) ^ k <= (p * b + q * a) ^ k.

(** Corpus row: bm:bm-039
    Site: https://graph-theory-ai.github.io/graph-conjectures/bm/bm-039/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/bondy_murty_reviews/bm-039.json
    English statement: (Burr and Erdos, Bondy-Murty Appendix A #39)
      Let T be a tree with k >= 1 edges, hence with n = k+1 >= 2 vertices.  Then every
      2-colouring of the edges of the complete graph on N = 2k = 2n-2 vertices contains a
      monochromatic copy of T; that is, r(T,T) <= 2n-2.
    Definitions: [is_tree [set: T]] (coq-graph-theory); [mono_copy T col c] - an injective
      adjacency-preserving copy of T inside the host all of whose edges get colour c
      (Extremal.foundations.edge_colourings); [E(T)] (coq-graph-theory).
    Notes: "tree on n vertices" is rendered, as in [erdos_sos_tree_embedding_statement], by
      the equivalent pair [#|E(T)| = k] and [#|T| = k.+1], and the bound 2n-2 is then 2k, so
      no natural subtraction occurs. The degenerate case n = 1 (k = 0) is EXCLUDED by
      [0 < k]: r(K_1,K_1) = 1 > 0 = 2n-2, so the source bound is false there and the
      conjecture is universally read over trees with at least one edge. *)
Definition burr_erdos_tree_ramsey_statement : Prop :=
  forall (T : sgraph) (k N : nat),
    is_tree [set: T] ->
    #|E(T)| = k ->
    #|T| = k.+1 ->
    0 < k ->
    N = 2 * k ->
    forall col : {set 'K_N} -> bool, exists c : bool, mono_copy T col c.

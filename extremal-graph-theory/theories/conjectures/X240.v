(** * Extremal.conjectures.X240 -- wave X240: degenerate Turan exponents and graph Ramsey numbers (2026-10-27)

    A six-row wave under the prospective contract of meta/faithfulness_policy.json.  Rows: erdos:146
    (Turan exponents of r-degenerate bipartite graphs), erdos:159 (R(C_4, K_n)), erdos:986 (the
    off-diagonal R(k, n) for fixed k), erdos:1030 (R(k+1, k) / R(k, k)), erdos:544 (R(3, k+1) - R(3, k))
    and Wigderson's edge-deletion conjecture (studies).  No local helper and no copied vocabulary:
    two-colour graph Ramsey numbers are Extremal.conjectures.XE1's [xe1_graph_ramsey_number H K R] (the
    least R such that every graph on R vertices contains H or its complement contains K) and
    [xe1_diagonal_ramsey_number G R] (= [xe1_graph_ramsey_number G G R]); Turan numbers are
    Extremal.conjectures.D2tur's [is_turan_number n Fam m] (m = ex(n; Fam), an attained maximum over
    n-vertex graphs with no member of Fam as a subgraph); GTBase supplies [bipartite], [k_degenerate],
    [cycle_graph], 'K_n and [del_edge_set]; [trunc_log] is MathComp's.  Literature dates are against
    the corpus pin (graph-conjectures b72c5857, 2026-09-23); these rows carry no review date, so their
    pinned status is the pin's.  The grounding certificates are in grounding_X240.v. *)

From Extremal.conjectures Require Import XE1 D2tur.
(* GTBase last: its canonical [edge_count] must shadow D2tur's eta-alias of the same name. *)
From GTBase Require Import base common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X240 statements ******************************************************* *)

(** Corpus row: erdos:146
    Site: none
    Review: none
    English statement: (Erdos Problems #146)
      If H is bipartite and r-degenerate (every induced subgraph of H has minimum degree at most r),
      then ex(n; H) << n^{2 - 1/r}: for every r >= 1 and every such H there is C with
      ex(n; H) <= C n^{2 - 1/r} for all n.
    Definitions: [bipartite H] - H has a proper 2-colouring (GTBase.base); [k_degenerate H r] - every
      nonempty vertex set S has a vertex with at most r neighbours in S (GTBase.base);
      [is_turan_number n Fam m] - m = ex(n; Fam), the maximum edge count of an n-vertex graph with
      no member of Fam as a subgraph (Extremal.conjectures.D2tur; here Fam is the single graph H).
    Notes: the pinned statement is the erdosproblems.com text ("If H is bipartite and is
      r-degenerate ... then ex(n; H) << n^{2-1/r}").  r >= 1 is required for n^{2-1/r} to make
      sense.  m <= C n^{2-1/r} is raised to the r-th power and multiplied by n: m^r n <= C^r n^{2r}
      (equivalent for n >= 1; n = 0 gives 0 <= 0); a real constant is replaced by its ceiling.  An
      edgeless H has no extremal number once n >= |H| (every n-vertex graph contains it), which only
      empties its own instance.  Literature status: DISPROVED BEFORE the corpus pin, not in the
      pinned status: the 2026 OpenAI report, Chapter 10, Section 1.2 ("Erdos [Erd67, Erd97, Blo146]
      conjectured that every fixed bipartite r-degenerate graph H satisfies ex(n, H) = O(n^{2-1/r})")
      and Theorem 1.2 ("There exist a fixed connected bipartite 2-degenerate graph H and constants c,
      eps > 0 such that ex(n, H) >= c n^{3/2+eps} for all sufficiently large n"; unrefereed, with a
      Lean formalization); the teorth/erdosproblems mirror (10fb9c15) lists "disproved (Lean)"
      (2026-08-02).  The row is encoded as stated. *)
Definition degenerate_bipartite_turan_exponent_statement : Prop :=
  forall r : nat, 1 <= r -> forall H : sgraph, bipartite H -> k_degenerate H r ->
    exists C : nat, forall n m : nat,
      is_turan_number n (fun _ : 'I_1 => H) m -> m ^ r * n <= C ^ r * n ^ (2 * r).

(** Corpus row: erdos:159
    Site: none
    Review: none
    English statement: (Erdos Problems #159)
      There is a constant c > 0 with R(C_4, K_n) << n^{2-c}, where R(C_4, K_n) is the least N such
      that every graph on N vertices contains a C_4 or an independent set of n vertices.
    Definitions: [xe1_graph_ramsey_number (cycle_graph 4) 'K_n R] - R = R(C_4, K_n): every graph on R
      vertices contains C_4 as a subgraph or its complement contains K_n, and R is least
      (Extremal.conjectures.XE1); [cycle_graph 4] - C_4 (GTBase).
    Notes: the pinned statement is the erdosproblems.com text ("There exists some constant c > 0 such
      that R(C_4, K_n) << n^{2-c}").  c is taken rational, c = a/b (any c > 0 can be lowered to one),
      and R <= C n^{2 - a/b} is raised to the b-th power and multiplied by n^a: R^b n^a <=
      C^b n^{2b}.  Literature status: open at the teorth/erdosproblems mirror (10fb9c15). *)
Definition c4_clique_ramsey_power_saving_statement : Prop :=
  exists a b C : nat, [/\ 0 < a, 0 < b &
    forall n R : nat, xe1_graph_ramsey_number (cycle_graph 4) 'K_n R ->
      R ^ b * n ^ a <= C ^ b * n ^ (2 * b)].

(** Corpus row: erdos:986
    Site: none
    Review: none
    English statement: (Erdos Problems #986)
      For every fixed k >= 3 there is c = c(k) > 0 with R(k, n) >> n^{k-1} / (log n)^c, where R(k, n)
      is the least N such that every graph on N vertices contains K_k or an independent set of n
      vertices.
    Definitions: [xe1_graph_ramsey_number 'K_k 'K_n R] - R = R(k, n): every graph on R vertices
      contains K_k or its complement contains K_n, and R is least (Extremal.conjectures.XE1);
      [trunc_log 2 n] - the floor of log2 n (MathComp).
    Notes: the pinned statement is the erdosproblems.com text ("For any fixed k >= 3, R(k,n) >>
      n^{k-1}/(log n)^c for some constant c = c(k) > 0").  R >> n^{k-1} / (log n)^c is n^{k-1} <=
      p R (log n)^c for large n, multiplied by n so that k - 1 is not written: n^k <= p R n
      (trunc_log 2 n)^c.  The base of the logarithm and its floor are absorbed by p (log2 n / 2 <=
      trunc_log 2 n <= log2 n for n >= 2), and a real c by its ceiling ((log n)^c grows with c once
      log n >= 1).  Literature status: PROVED BEFORE the corpus pin, not in the pinned status:
      Bradac, "Off-diagonal Ramsey numbers", arXiv:2605.28793v3 (v1 2026-05-27, v3 2026-06-16),
      Theorem thm:main (main.tex l.288-291): "For any s >= 3, there is a positive constant c_s such
      that for any k >= 2, r(s, k) >= c_s k^{s-1} / (log k)^{2s-4}" (the row with c = 2k - 4); v1
      proved only Omega(k^{s-2} / (log k)^{2s-6}) (l.292); unrefereed.  The teorth/erdosproblems
      mirror (10fb9c15) lists "proved" (2026-06-21).  The row is encoded as stated. *)
Definition clique_ramsey_polylog_lower_statement : Prop :=
  forall k : nat, 3 <= k -> exists c p n0 : nat, 0 < p /\
    forall n R : nat, n0 <= n -> xe1_graph_ramsey_number 'K_k 'K_n R ->
      n ^ k <= p * R * n * trunc_log 2 n ^ c.

(** Corpus row: erdos:1030
    Site: none
    Review: none
    English statement: (Erdos Problems #1030)
      There is c > 0 such that R(k+1, k) / R(k, k) exceeds 1 + c in the limit k -> oo, where R(k, l)
      is the least n such that every red / blue colouring of the edges of K_n has a red K_k or a blue
      K_l.
    Definitions: [xe1_graph_ramsey_number 'K_k.+1 'K_k R1] - R1 = R(k+1, k) (the red graph and its
      complement, the blue graph; Extremal.conjectures.XE1); [xe1_graph_ramsey_number 'K_k 'K_k R0]
      - R0 = R(k, k).
    Notes: the pinned statement is the erdosproblems.com text ("Prove the existence of some c > 0
      such that lim_{k -> oo} R(k+1,k)/R(k,k) > 1 + c").  It is stated in the liminf reading:
      eventually R(k+1, k) / R(k, k) > 1 + 1/q for some q >= 1, written (q + 1) R0 < q R1.  This is
      equivalent to "liminf > 1 + c for some c > 0", and to the pinned text whenever the limit
      exists.  Literature status: open at the teorth/erdosproblems mirror (10fb9c15). *)
Definition consecutive_diagonal_ramsey_ratio_statement : Prop :=
  exists q : nat, 1 <= q /\ exists k0 : nat, forall k R0 R1 : nat, k0 <= k ->
    xe1_graph_ramsey_number 'K_k 'K_k R0 -> xe1_graph_ramsey_number 'K_k.+1 'K_k R1 ->
    (q + 1) * R0 < q * R1.

(** Corpus row: erdos:544
    Site: none
    Review: none
    English statement: (Erdos Problems #544)
      R(3, k+1) - R(3, k) tends to infinity as k tends to infinity, where R(3, k) is the least N such
      that every graph on N vertices contains a triangle or an independent set of k vertices.
    Definitions: [xe1_graph_ramsey_number 'K_3 'K_k R0] - R0 = R(3, k) (Extremal.conjectures.XE1).
    Notes: the pinned statement is the erdosproblems.com text ("Show that R(3,k+1) - R(3,k) -> oo as
      k -> oo.  Similarly, prove or disprove that R(3,k+1) - R(3,k) = o(k)").  The first sentence is
      stated, without subtraction: for every M, eventually R(3, k) + M <= R(3, k+1).  The second
      sentence asks a question in both directions and is not formalized here (as erdos:715, X183).
      Literature status: open at the teorth/erdosproblems mirror (10fb9c15). *)
Definition triangle_ramsey_increment_unbounded_statement : Prop :=
  forall M : nat, exists k0 : nat, forall k R0 R1 : nat, k0 <= k ->
    xe1_graph_ramsey_number 'K_3 'K_k R0 -> xe1_graph_ramsey_number 'K_3 'K_k.+1 R1 ->
    R0 + M <= R1.

(** Corpus row: studies:std_wigderson_s_edge_deletion_ramsey_conjecture
    Site: none
    Review: none
    English statement: (Wigderson, "Wigderson's edge-deletion Ramsey conjecture")
      Deleting an edge from a graph can change the Ramsey number by at most a constant factor: there
      is C such that r(G) <= C r(G - e) for every graph G and every edge e of G, where r(G) is the
      least N such that every two-colouring of the edges of K_N has a monochromatic copy of G.
    Definitions: [xe1_diagonal_ramsey_number G R] - R = r(G): every graph on R vertices or its
      complement contains G (Extremal.conjectures.XE1); [del_edge_set G [set [set x; y]]] - G with
      the edge xy deleted (GTBase.common).
    Notes: the pinned statement is the studies record (source arXiv:2311.01887v1, Ahme et al.,
      main.tex l.198: "Wigderson has conjectured that deleting an edge can change the Ramsey number
      by at most a constant factor").  Wigderson's own statement (arXiv:2208.11181v3,
      Revised_2024-01-16.tex l.379-385): "Let G be a graph, and let H be obtained from G by deleting
      a single edge.  Then r(H) >= c r(G) for some absolute constant c > 0"; C = ceil(1/c).  The
      other direction, r(G - e) <= r(G), is monotonicity.  Every graph is allowed, isolated vertices
      included, as in Wigderson's vertex-deletion counterexamples (l.365).  Literature status: open
      as far as the sources show (2311.01887v1, 2023-11-03, lists it as open); the vertex-deletion
      version of Conlon, Fox and Sudakov is false (Wigderson, 2208.11181). *)
Definition edge_deletion_ramsey_constant_factor_statement : Prop :=
  exists C : nat, forall (G : sgraph) (x y : G) (R1 R0 : nat), x -- y ->
    xe1_diagonal_ramsey_number G R1 ->
    xe1_diagonal_ramsey_number (del_edge_set G [set [set x; y]]) R0 ->
    R1 <= C * R0.

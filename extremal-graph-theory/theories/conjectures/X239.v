(** * Extremal.conjectures.X239 -- wave X239: hypercube, Ramsey, Turan and induced-regular rows (2026-10-27)

    A six-row wave under the prospective contract of meta/faithfulness_policy.json.  Rows: erdos:86
    (C_4 in dense subgraphs of the hypercube), erdos:554 (odd cycles against triangles in many
    colours), erdos:573 (ex(n; {C_3, C_4})), erdos:571 (rational Turan exponents), erdos:82 (regular
    induced subgraphs) and erdos:575 (bipartite compactness).  No local helper and no copied
    vocabulary: Ramsey numbers are Extremal.conjectures.X195's [x195_ramsey_number k Fam R] (k
    COLOURS), Turan numbers are Extremal.conjectures.D2tur's [is_turan_number n Fam m] (m = ex(n; Fam),
    an attained maximum over n-vertex graphs with no member of Fam as a subgraph), and GTBase supplies
    [product_hypercube], [cycle_graph], [del_edge_set], [has_subgraph], [bipartite], [regular] and
    [induced]; [trunc_log] is MathComp's.  Literature dates are against the corpus pin
    (graph-conjectures b72c5857, 2026-09-23); these rows carry no review date, so their pinned status
    is the pin's.  The grounding certificates are in grounding_X239.v. *)

From Extremal.foundations Require Import edge_colourings.
From Extremal.conjectures Require Import X195 D2tur.
(* GTBase last: its canonical [edge_count] must shadow D2tur's eta-alias of the same name. *)
From GTBase Require Import base common hypercubes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X239 statements ******************************************************* *)

(** Corpus row: erdos:86
    Site: none
    Review: none
    English statement: (Erdos Problems #86)
      Every subgraph of the n-dimensional hypercube Q_n (2^n vertices, n 2^{n-1} edges) with at least
      (1/2 + o(1)) n 2^{n-1} edges contains a C_4: for every q >= 1 there is n0 such that, for
      n >= n0, every subgraph of Q_n with at least (1/2 + 1/q) n 2^{n-1} edges contains a C_4.
    Definitions: [product_hypercube n] - Q_n (GTBase.hypercubes); [del_edge_set G (E(G) :\: F)] -
      the spanning subgraph of G with edge set F (GTBase); [has_subgraph H C] - C is a (not
      necessarily induced) subgraph of H (GTBase.common); [cycle_graph 4] - C_4 (GTBase).
    Notes: the pinned statement is the erdosproblems.com question ("Is it true that every subgraph
      of Q_n with >= (1/2 + o(1)) n 2^{n-1} many edges contains a C_4?"); the affirmative form is
      stated.  (1/2 + o(1)) is "for every epsilon = 1/q, eventually", and |F| >= (1/2 + 1/q) n
      2^{n-1} is written (q + 2) n 2^n <= 4 q |F|.  A subgraph is taken spanning, given by its edge
      set F, which is enough since containing a C_4 is monotone.  Literature status: open at the
      teorth/erdosproblems mirror (10fb9c15). *)
Definition hypercube_dense_subgraph_C4_statement : Prop :=
  forall q : nat, 1 <= q -> exists n0 : nat,
    forall (n : nat) (F : {set {set product_hypercube n}}), n0 <= n -> F \subset E(product_hypercube n) ->
      (q + 2) * (n * 2 ^ n) <= 4 * q * #|F| ->
      has_subgraph (del_edge_set (product_hypercube n) (E(product_hypercube n) :\: F)) (cycle_graph 4).

(** Corpus row: erdos:554
    Site: none
    Review: none
    English statement: (Erdos Problems #554)
      For every n >= 2, R_k(C_{2n+1}) / R_k(K_3) tends to 0 as k tends to infinity, where R_k(G) is
      the least m such that every k-colouring of the edges of K_m has a monochromatic copy of G.
    Definitions: [x195_ramsey_number k Fam R] - R = R_k(G) for Fam the single graph G
      (Extremal.conjectures.X195; k counts colours); [cycle_graph (2 * n + 1)] - C_{2n+1} (GTBase).
    Notes: the pinned statement is the erdosproblems.com text ("Show that lim_{k -> oo} R_k(C_{2n+1})
      / R_k(K_3) = 0 for any n >= 2").  The limit 0 is "for every q, eventually R_k(C_{2n+1}) <=
      R_k(K_3) / q", written q R1 <= R3.  Literature status: open at the teorth/erdosproblems mirror
      (10fb9c15).  Partial progress BEFORE the corpus pin, not in the pinned status: arXiv:2510.17981v1
      (submitted 2025-10-20), Theorem 1.1, gives R_k(C_{2l+1}) <= (4l - 2)^k k^{k/l} + 1, and
      arXiv:2608.02522v2 (v1 2026-08-03, v2 2026-09-07) l.236-240, citing the 2026 OpenAI report
      (Chapter 9), gives R_k(C_3) >= (c k^{1/3} / log k)^k; for n >= 4 the ratio is then at most
      (C log k)^k k^{k(1/n - 1/3)}, which tends to 0, so the row holds for n >= 4 (the lower bound is
      unrefereed); n = 2 and n = 3 stay open.  The row is encoded as stated. *)
Definition odd_cycle_triangle_ramsey_ratio_statement : Prop :=
  forall n : nat, 2 <= n -> forall q : nat, 1 <= q ->
    exists k0 : nat, forall k R1 R3 : nat, k0 <= k ->
      x195_ramsey_number k (fun _ : 'I_1 => cycle_graph (2 * n + 1)) R1 ->
      x195_ramsey_number k (fun _ : 'I_1 => 'K_3) R3 -> q * R1 <= R3.

(** Corpus row: erdos:573
    Site: none
    Review: none
    English statement: (Erdos Problems #573)
      ex(n; {C_3, C_4}) ~ (n/2)^{3/2}: the maximum number of edges of an n-vertex graph with no
      triangle and no 4-cycle is (1 + o(1)) (n/2)^{3/2}.
    Definitions: [is_turan_number n Fam m] - m = ex(n; Fam), the maximum edge count of an n-vertex
      graph with no member of Fam as a subgraph (Extremal.conjectures.D2tur); the family
      [fun i : 'I_2 => cycle_graph (i + 3)] is {C_3, C_4} (GTBase).
    Notes: the pinned statement is the erdosproblems.com question ("Is it true that ex(n; {C_3,
      C_4}) ~ (n/2)^{3/2}?"); the affirmative form is stated.  m ~ (n/2)^{3/2} iff m^2 ~ n^3 / 8; for
      epsilon = 1/q the ratio m / (n/2)^{3/2} lies in [q/(q+1), (q+1)/q] for large n, squared and
      multiplied out (no roots, no subtraction).  Literature status: open at the teorth/erdosproblems
      mirror (10fb9c15). *)
Definition triangle_square_free_turan_asymptotic_statement : Prop :=
  forall q : nat, 1 <= q -> exists n0 : nat,
    forall n m : nat, n0 <= n ->
      is_turan_number n (fun i : 'I_2 => cycle_graph (i + 3)) m ->
      q ^ 2 * n ^ 3 <= 8 * (q + 1) ^ 2 * m ^ 2 /\ 8 * q ^ 2 * m ^ 2 <= (q + 1) ^ 2 * n ^ 3.

(** Corpus row: erdos:571
    Site: none
    Review: none
    English statement: (Erdos Problems #571)
      For every rational alpha in [1, 2) there is a bipartite graph G with ex(n; G) asymp n^alpha,
      i.e. n^alpha / c <= ex(n; G) <= c n^alpha for some c and all large n.
    Definitions: [bipartite G] - G has a proper 2-colouring (GTBase.base); [is_turan_number n Fam m]
      - m = ex(n; Fam) (Extremal.conjectures.D2tur).
    Notes: the pinned statement is the erdosproblems.com text ("Show that for any rational alpha in
      [1, 2) there exists a bipartite graph G such that ex(n; G) asymp n^alpha").  alpha = p/q with
      q <= p < 2q; both bounds are raised to the q-th power.  ex(n; G) is required to EXIST (exists
      m): with "forall m, is_turan_number ... ->" an edgeless G (no G-free graph on n >= |G| vertices,
      so no extremal number) would make the row trivially true.  Literature status: SOLVED BEFORE the
      corpus pin, not in the pinned status: the mirror (10fb9c15) lists "proved (Lean)" (Lean status
      2026-09-03), and the proof is in the FrontierMath Erdos benchmark, arXiv:2609.25050v1 (submitted
      2026-09-06; l.225, l.306, the proof l.382 ff.), an unrefereed preprint.  The row is encoded as
      stated. *)
Definition rational_turan_exponent_statement : Prop :=
  forall p q : nat, 1 <= q -> q <= p -> p < 2 * q ->
    exists G : sgraph, bipartite G /\ exists c n0 : nat, 1 <= c /\
      forall n : nat, n0 <= n -> exists m : nat,
        [/\ is_turan_number n (fun _ : 'I_1 => G) m, n ^ p <= (c * m) ^ q & m ^ q <= c ^ q * n ^ p].

(** Corpus row: erdos:82
    Site: none
    Review: none
    English statement: (Erdos Problems #82)
      Let F(n) be maximal such that every graph on n vertices contains a regular induced subgraph on
      at least F(n) vertices.  Then F(n) / log n tends to infinity.
    Definitions: [regular H d] - every vertex of H has degree d (GTBase.base); [induced S] - the
      subgraph induced by S (upstream); [trunc_log 2 n] - the floor of log2 n (MathComp).
    Notes: the pinned statement is the erdosproblems.com text ("Prove that F(n)/log n -> oo").  It is
      "for every M, eventually every n-vertex graph has a regular induced subgraph on at least
      M log n vertices"; the base of the logarithm and its floor are absorbed by M (log2 n / 2 <=
      trunc_log 2 n <= log2 n for n >= 2).  Literature status: open at the teorth/erdosproblems
      mirror (10fb9c15) and in arXiv:2604.08215v3 (Dyson and McKay, "Ramsey numbers for regular
      induced subgraphs") l.125-135: "Q1. Does f(n)/log n -> oo? ... both these questions remain
      open". *)
Definition regular_induced_subgraph_superlogarithmic_statement : Prop :=
  forall M : nat, exists n0 : nat,
    forall G : sgraph, n0 <= #|G| ->
      exists S : {set G}, (exists d : nat, regular (induced S) d) /\ M * trunc_log 2 #|G| <= #|S|.

(** Corpus row: erdos:575
    Site: none
    Review: none
    English statement: (Erdos Problems #575, Erdos and Simonovits)
      For every finite family F of finite graphs containing a bipartite graph, some bipartite
      G in F has ex(n; G) <<_F ex(n; F), where ex(n; F) is the maximum number of edges of an n-vertex
      graph containing no member of F as a subgraph.
    Definitions: [bipartite G] - G has a proper 2-colouring (GTBase.base); [is_turan_number n Fam m]
      - m = ex(n; Fam) (Extremal.conjectures.D2tur; the family indexed by 'I_k).
    Notes: the pinned statement is the erdosproblems.com question ("Is it true that, for every F, if
      there is a bipartite graph in F then there exists some bipartite G in F such that ex(n; G)
      <<_F ex(n; F)?"); the affirmative form is stated, << as an eventual bound with constants C and
      N, as D2tur's opg:turan_number_of_a_finite_family.  Literature status: FALSE AS STATED, BEFORE
      the corpus pin, not in the pinned status: the folklore family {K_{1,2}, 2K_2} has, for n >= 4,
      ex(n; {K_{1,2}, 2K_2}) = 1 while ex(n; K_{1,2}) = floor(n/2) and ex(n; 2K_2) = n - 1 (both
      members bipartite), as the 2026 OpenAI report, Chapter 10, Section 1.1 recalls; the mirror
      (10fb9c15) lists "disproved".  The corrected form, every member containing a cycle, is refuted
      by the same chapter's Theorem 1.1 (a finite family of connected bipartite graphs with ex(n; F)
      = O(n^{4/3 - 1/48}) and ex(n; F) = Omega(n^{4/3}) for each member; unrefereed).  The row is
      encoded as stated. *)
Definition bipartite_turan_compactness_statement : Prop :=
  forall (k : nat) (Fam : 'I_k -> sgraph), (exists i : 'I_k, bipartite (Fam i)) ->
    exists (i : 'I_k) (C N : nat), bipartite (Fam i) /\
      forall n m1 m : nat, N <= n ->
        is_turan_number n (fun _ : 'I_1 => Fam i) m1 -> is_turan_number n Fam m -> m1 <= C * m.

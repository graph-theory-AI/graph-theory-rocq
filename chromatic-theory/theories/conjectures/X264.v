(** * Chromatic.conjectures.X264 -- wave X264: defective, single-conflict and rainbow colourings (2026-10-30)

    A three-row wave under the prospective contract of meta/faithfulness_policy.json.  Rows:
    studies:std_guo_kang_zwaneveld_conjecture (chi(G) = chi^d(G boxtimes K_(d+1)), the d-defective chromatic number
    of the strong product with K_(d+1)), arxiv:1803.10962#01 (the single-conflict chromatic number of a d-degenerate
    graph on n vertices is at most C' sqrt(d) log n) and arxiv:2405.14795#01 (for odd n, every pair of proper
    edge-colourings of K_n admits a rainbow stacking).  Shared vocabulary: the chromatic number chi([set: G]) of
    coq-graph-theory, GTBase's [k_degenerate], [box_rel], [tensor_rel] and [proper_edge_colouring], X210's
    single-conflict colourings [x210_conflict_k_colourable_under_rat_bound] and MathComp's [trunc_log] and
    permutations.  Local helpers: the strong product ([x264_strong_rel], [x264_strong_product]), defective
    colourability ([x264_defective_colourable]) and rainbow stackings of two colourings ([x264_rainbow_stacking]).
    Pinned statuses: GKZ open (false at the pin), 1803.10962#01 solved, 2405.14795#01 open; literature lines are
    dated against the corpus pin (graph-conjectures b72c5857, 2026-09-23).  The sources are the Mac's deposit
    coordination/sources/x264-source-mac-20261030 (TeX line numbers below).  The grounding certificates are in
    grounding_X264.v. *)

From GTBase Require Import base common edge_colourings.
From mathcomp Require Import fingroup perm.
From Chromatic.conjectures Require Import X210.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X264 vocabulary ********************************************************* *)

(** The adjacency of the strong product G boxtimes H on G * H (Guo, Kang and Zwaneveld, arXiv:2411.06941v1,
    improper-arXiv.tex l.125: equal in one coordinate and adjacent in the other, or adjacent in both): the union of
    GTBase's cartesian [box_rel] and tensor [tensor_rel] relations. *)
Definition x264_strong_rel (G H : sgraph) : rel (G * H) :=
  fun p q => box_rel p q || tensor_rel p q.

Lemma x264_strong_sym (G H : sgraph) : symmetric (@x264_strong_rel G H).
Proof. by move=> p q; rewrite /x264_strong_rel box_sym tensor_sym. Qed.

Lemma x264_strong_irrefl (G H : sgraph) : irreflexive (@x264_strong_rel G H).
Proof. by move=> p; rewrite /x264_strong_rel box_irrefl tensor_irrefl. Qed.

(** The strong product G boxtimes H.  Neither coq-graph-theory nor GTBase has one (base.v has the cartesian and
    tensor products; extremal X191's [x191_clique_blowup] is a blow-up of K_m only). *)
Definition x264_strong_product (G H : sgraph) : sgraph :=
  SGraph (@x264_strong_sym G H) (@x264_strong_irrefl G H).

(** G has a d-defective colouring by 'I_k: every vertex has at most d neighbours of its own colour
    (2411.06941v1 l.178; Norin and Steiner, arXiv:2504.01548v1, main.tex l.110).  chi^d(G) is the least such k. *)
Definition x264_defective_colourable (G : sgraph) (d k : nat) : Prop :=
  exists col : G -> 'I_k,
    forall v : G, #|N(v) :&: [set u : G | col u == col v]| <= d.

(** A rainbow stacking (s1, s2) of two edge-colourings of K_n (Alon, Defant and Kravitz, arXiv:2405.14795v1,
    main.tex l.106, with m = 2): at every edge {i, j} the colours chi1 {s1^-1 i, s1^-1 j} and
    chi2 {s2^-1 i, s2^-1 j} differ. *)
Definition x264_rainbow_stacking (n r : nat) (chi1 chi2 : {set 'K_n} -> 'I_r)
    (s1 s2 : {perm 'I_n}) : Prop :=
  forall i j : ('K_n), i -- j ->
    chi1 [set (s1^-1)%g i; (s1^-1)%g j] != chi2 [set (s2^-1)%g i; (s2^-1)%g j].

(** ** X264 statements ********************************************************* *)

(** Corpus row: studies:std_guo_kang_zwaneveld_conjecture
    Site: none
    Review: none
    English statement: (Guo, Kang and Zwaneveld, Conjecture 2 of arXiv:2411.06941v1)
      For every graph G and every integer d >= 0, we have chi(G) = chi^d(G boxtimes K_(d+1)).
    Definitions: chi([set: G]) - the chromatic number (coq-graph-theory); [x264_defective_colourable H d k] - some
      colouring of H by 'I_k gives every vertex at most d neighbours of its own colour, so chi^d(H) is the least such
      k (this file); [x264_strong_product G H] - the strong product G boxtimes H (this file); 'K_(d+1) - the
      complete graph on d + 1 vertices.
    Notes: chi^d(H), the d-defective (d-improper) chromatic number, is the least number of colours of a colouring in
      which every vertex has at most d neighbours of its own colour (2411.06941v1 l.112 and l.178; 2504.01548v1
      l.110).  The equality of two least numbers is their agreement on every bound k: both properties are upward
      closed in k (g264_defective_mono in grounding_X264.v), so the conjecture is: chi(G) <= k iff
      x264_defective_colourable (G boxtimes K_(d+1)) d k, for every G, d and k.  Direction -> holds for all G and d
      by lifting a proper colouring of G to every copy (2411.06941v1 l.132; 2504.01548v1 l.120; g264_lift), so the
      content is direction <-.  The strong product follows the GKZ footnote (l.125): (u,u') ~ (v,v') iff they are
      distinct and in each coordinate equal or adjacent; with H = K_t this is Norin and Steiner's form, (u,i) ~
      (v,j) iff u = v and i <> j, or uv is an edge (2504.01548v1 l.114; g264_strong_KE).  Literature status: FALSE
      at the pin (pinned status open).  Norin and Steiner, Defective coloring of blowups (arXiv:2504.01548v1,
      2 April 2025), Theorem 1.2 (main.tex l.124-126): for every d >= 2 there is a graph G with
      chi^d(G boxtimes K_(d+1)) <= k = 2d^3 + 2d^2 + d + 3 but chi(G) > k (k = 29 at d = 2), an instance of
      direction <- that fails.  They note the conjecture holds for d < 2 (l.127, from GKZ's Corollary 20) and prove
      chi(G) <= 2 chi^d(G boxtimes K_d) (Theorem 1.3, l.134-136).  Encoded as stated; the row is false at the pin. *)
Definition guo_kang_zwaneveld_defective_strong_product_statement : Prop :=
  forall (G : sgraph) (d k : nat),
    χ([set: G]) <= k <-> x264_defective_colourable (x264_strong_product G ('K_d.+1)) d k.

(** Corpus row: arxiv:1803.10962#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1803.10962__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1803.10962__01.json
    English statement: (Dvorak, Esperet, Kang and Ozeki, arXiv:1803.10962)
      There might yet be some constant C' > 0 such that the single-conflict chromatic number of any d-degenerate
      graph on n vertices is at most C' sqrt(d) log n.
    Definitions: [x210_conflict_k_colourable_under_rat_bound G k 1 k] - every assignment of at most one forbidden
      ordered pair of colours of 'I_k to each edge (k * #pairs <= 1 * k), transposed on the reverse orientation, is
      avoided by some colouring by 'I_k (Chromatic.conjectures.X210); [k_degenerate G d] - every nonempty vertex set
      has a vertex with at most d neighbours inside it (GTBase base.v); [trunc_log 2 n] - the floor of log2 n
      (MathComp).
    Notes: The source (arXiv:1803.10962v2, dp1.tex l.86-90) defines the single-conflict chromatic number as the
      least positive k such that G is conflict-colourable for every local k-partition: on a simple graph, one
      forbidden pair (kappa_u(e), kappa_v(e)) on each edge e = uv.  For positive k, at most one pair per edge is the
      same requirement as exactly one (g264_single_conflictE in grounding_X264.v), and the property is upward
      closed in k (g264_single_conflict_mono), so "at most C' sqrt(d) log n" is "every positive k with
      k >= C' sqrt(d) log n works"; both sides are squared.  A real C' > 0 may be replaced by a natural C, since a
      larger C admits fewer k; the base and floor of the logarithm are absorbed by C for n >= 2
      (log2 n / 2 <= trunc_log 2 n <= log2 n).  "Graph" is simple: the paper says multigraph when it means one, and
      the question would give the mu = 1 case of its Theorem 1 (l.168); for edge multiplicity omega(log^2 n) the
      bound fails (arXiv:2112.06333v2, SCCmain.tex l.264-266).  Guard: 0 < k is the source's positivity of k
      (l.86, "For any positive integer k"), and it is load-bearing: an edgeless graph with a vertex is 0-degenerate,
      and K_1 has trunc_log 2 1 = 0, so without the guard the clause asks for a colouring by no colour
      (g264_sc_guard_teeth).  With it these instances hold (one colour suffices without edges), and every other
      instance (d >= 1 and n >= 2) is the source's.  Literature status: true at the pin (pinned status solved).
      Bradshaw and Masarik, Single-conflict colorings of degenerate graphs (arXiv:2112.06333v2, 29 January 2025),
      Theorem 1.7 (SCCmain.tex l.241-246): a d-degenerate simple graph of maximum degree Delta has single-conflict
      chromatic number at most the ceiling of 2 sqrt(d [1 + log((d + 1) Delta)]), which "immediately answers
      Question 1.5 for simple graphs" (l.246; also l.373-375).  The clause follows since G is also
      min(d, n - 1)-degenerate and Delta < n, so (min(d, n - 1) + 1) Delta <= n^2. *)
Definition degenerate_single_conflict_sqrt_log_statement : Prop :=
  exists C : nat,
    forall (G : sgraph) (d k : nat), 0 < k -> k_degenerate G d ->
      C ^ 2 * d * trunc_log 2 #|G| ^ 2 <= k ^ 2 ->
      x210_conflict_k_colourable_under_rat_bound G k 1 k.

(** Corpus row: arxiv:2405.14795#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2405.14795__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2405.14795__01.json
    English statement: (Alon, Defant and Kravitz, Question 3.3, arXiv:2405.14795)
      Is it true that when n is odd, every pair of proper edge-colorings of K_n admits a rainbow stacking?
    Definitions: [proper_edge_colouring chi] - two distinct edges at a common vertex get different colours, for a
      map chi on vertex sets of which only the edges are read (GTBase edge_colourings); [x264_rainbow_stacking chi1
      chi2 s1 s2] - for every edge {i, j} of K_n, chi1 {s1^-1 i, s1^-1 j} <> chi2 {s2^-1 i, s2^-1 j} (this file);
      'K_n - the complete graph on 'I_n.
    Notes: The question is encoded as its affirmative answer.  The definitions follow the paper (arXiv:2405.14795v1,
      main.tex l.106): K_n has vertex set [n], the edge-colourings map the edges into one common set C_r of r
      colours, and a rainbow stacking of chi_1, ..., chi_m is a tuple of vertex permutations (sigma_1, ...,
      sigma_m) such that at each edge e the colours chi_k(sigma_k^-1(e)) are all distinct; here m = 2.  The palette
      'I_r has arbitrary size r and is the same for both colourings, whose colour labels are compared, never
      renamed independently.  Every common palette reduces to some 'I_r: the edges of K_n use finitely many colours,
      and an injective relabelling preserves properness (GTBase's proper_edge_colouring_relabel) and the
      distinctness of two colours.  For r = 0 there is no map into the palette.  A common relabelling of the
      vertices fixes s1 = 1 (g264_rainbow_stacking_id in grounding_X264.v), an equivalent form not used here.
      Context: Proposition 3.2 (l.388-391) gives, for n = 2^k - 2 with k >= 2, a pair of proper edge-colourings of
      K_n with no rainbow stacking (the pinned context says "for each even n >= 4"); the answer is yes for n = 3 by
      inspection and n = 5 by computer search (l.414).  Literature status: open at the pin. *)
Definition odd_complete_proper_edge_colourings_rainbow_stacking_statement : Prop :=
  forall (n r : nat) (chi1 chi2 : {set 'K_n} -> 'I_r),
    odd n -> proper_edge_colouring chi1 -> proper_edge_colouring chi2 ->
    exists s1 s2 : {perm 'I_n}, x264_rainbow_stacking chi1 chi2 s1 s2.

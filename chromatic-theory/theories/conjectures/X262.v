(** * Chromatic.conjectures.X262 -- wave X262: chromatic numbers of K_r-free and degenerate graphs (2026-10-29)

    A four-row wave under the prospective contract of meta/faithfulness_policy.json.  Rows: erdos:920 (the largest
    chromatic number of a K_k-free graph on n vertices is >> n^(1-1/(k-1)) / (log n)^(c_k), k >= 4),
    studies:std_harris_conjecture (Harris: chi_f(G) <= K d / log d for triangle-free d-degenerate G),
    arxiv:2601.15245#02 (Problem 6.2: chi(G) = O(d / log d) for triangle-free d-degenerate G of maximum degree at most
    e^(d^(1-eps))) and arxiv:2601.15245#03 (Problem 6.3: a K_r-free d-degenerate graph with chromatic number d + 1 has
    e^(Omega_r(d)) vertices).  Shared vocabulary only, no local helper: the chromatic and clique numbers chi([set: G])
    and omega([set: G]) of coq-graph-theory, GTBase's [k_degenerate] and [Delta], Chromatic.conjectures.X130's
    [x130_frac_chi_le] (as X218 states #04 of the same paper) and MathComp's [trunc_log].  Pinned statuses: all four
    open; literature lines are dated against the corpus pin (graph-conjectures b72c5857, 2026-09-23).  The sources are
    the Mac's deposit coordination/sources/x262-source-mac-20261029 (TeX line numbers below).  The grounding
    certificates are in grounding_X262.v. *)

From GTBase Require Import base common.
From Chromatic.conjectures Require Import X130.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X262 statements ****************************************************** *)

(** Corpus row: erdos:920
    Site: none
    Review: none
    English statement: (Erdos Problems #920, Erdos)
      Let f_k(n) be the maximum possible chromatic number of a graph with n vertices which contains no K_k.  Is it
      true that, for k >= 4, f_k(n) >> n^(1-1/(k-1)) / (log n)^(c_k) for some constant c_k > 0?
    Definitions: chi([set: G]) and omega([set: G]) - the chromatic and clique numbers (coq-graph-theory; "contains no
      K_k" is omega([set: G]) < k); [trunc_log 2 n] - the floor of log2 n (MathComp).
    Notes: f_k(n) is a maximum over the finitely many graphs on n vertices and the bound is increasing in the
      chromatic number, so "f_k(n) is at least the bound" says that some K_k-free graph G on n vertices reaches it;
      the statement quantifies over that witness and needs no helper for f_k.  ">>" is a constant C and a threshold N
      on n.  Both sides are raised to the power k - 1: n^(k-2) <= C chi(G)^(k-1) (log n)^(c_k (k-1)).  A real c_k > 0
      may be rounded up to a natural c, since a larger power of the logarithm only weakens the bound once log n >= 1,
      and c = 0 only strengthens it; the base of the logarithm and its floor change the logarithmic factor by a
      constant for each k (log2 n / 2 <= trunc_log 2 n <= log2 n for n >= 2), absorbed by C.  Erdos (Er69b, p.29,
      Eq.(7), "for l > 3") writes the same function as g_l(n), not the f_k of his p.28, after the Graver-Yackel upper
      bound (4) and the case l = 3 (6).  Literature status: true at the pin (pinned status open, a stale record).
      Bradac, Off-diagonal Ramsey numbers (arXiv:2605.28793v3, 16 June 2026), Theorem 1.1 (main.tex l.288-291): for
      every s >= 3 there is c_s > 0 with r(s,t) >= c_s t^(s-1) / (log t)^(2s-4) for every t >= 2 (v3: l.292 says the
      first version proved only the exponent s - 2); for k = 4 also Mattheus and Verstraete (arXiv:2306.04007v5,
      Theorem 1, l.148-151), r(4,t) = Omega(t^3 / log^4 t).  The encoded clause follows with s = k: r(k,t) > n gives
      a K_k-free graph on n vertices with no stable set of size t, hence chromatic number at least n / (t - 1), and t
      of order n^(1/(k-1)) (log n)^((2k-4)/(k-1)) gives the bound with c_k = (2k-4)/(k-1) < 2, so c = 2.  The page
      (erdos-920.txt, edited 25 July 2026) records this positive answer.  Guard: k >= 4 is the pinned range, and it
      makes k - 1 and k - 2 true subtractions. *)
Definition kk_free_chromatic_lower_bound_statement : Prop :=
  forall k : nat, 4 <= k ->
    exists c C N : nat,
      forall n : nat, N <= n ->
        exists G : sgraph,
          [/\ #|G| = n, ω([set: G]) < k &
              n ^ (k - 2) <= C * χ([set: G]) ^ (k - 1) * trunc_log 2 n ^ (c * (k - 1))].

(** Corpus row: studies:std_harris_conjecture
    Site: none
    Review: none
    English statement: (Harris' Conjecture, as Janzer, Steiner and Sudakov state it, arXiv:2410.02437v1, Conjecture
      3.1)
      There exists an absolute constant K > 0 such that for every sufficiently large d in N, every triangle-free
      d-degenerate graph G satisfies chi_f(G) <= K d / log d.
    Definitions: [x130_frac_chi_le G p q] - some (a:b)-fold colouring of G has a q <= p b, i.e. chi_f(G) <= p / q
      (Chromatic.conjectures.X130); [k_degenerate G d] - every nonempty vertex set has a vertex with at most d
      neighbours inside it (GTBase base.v); omega([set: G]) < 3 - triangle-free (coq-graph-theory); [trunc_log 2 d] -
      the floor of log2 d (MathComp).
    Notes: The fractional chromatic number of a finite graph is attained by an (a:b)-fold colouring, so "chi_f(G) <= K
      d / log d" is x130_frac_chi_le G (K d) (trunc_log 2 d) (X130.v; X218 states #04 of arXiv:2601.15245 the same
      way).  A real K may be rounded up, and the base and floor of the logarithm are absorbed by K both ways: for d >=
      2, trunc_log 2 d <= log2 d = ln d / ln 2 < trunc_log 2 d + 1 <= 2 trunc_log 2 d.  "Sufficiently large d" is the
      threshold d0, and d0 >= 2 may be assumed.  The row's two records name different conjectures "Harris'
      Conjecture": the encoded text is 2410.02437v1 Conjecture 3.1 (main.tex l.242-244), which cites Harris
      (arXiv:1604.00438v8, Conjecture 6.2, source.tex l.654-657: chi_f(G) <~ d / log d for d-degenerate triangle-free
      G); Harris's l.659 separates it from his draft's broader Hall-ratio conjecture, refuted since (l.776-783 cite
      Blumenthal et al. and Dvorak, Ossona de Mendez and Wu, arXiv:1812.07327, whose no1sub.tex l.98-100 and
      Corollary 3, l.139-141, concern that conjecture).  Literature status: true at the pin (pinned status open, a
      stale record).  Martinsson (arXiv:2501.18238v1, 30 January 2025), Theorem 1.2 (source.tex l.118-119): every
      triangle-free d-degenerate graph has chi_f(G) <= (4 + o(1)) d / ln d, the o(1) tending to 0 as d grows; his
      Conjecture 1.1 (l.112) is Harris's 6.2.  The encoded clause follows with K = 8: for d large, (4 + o(1)) <= 5,
      and 5 d / ln d <= 8 d / trunc_log 2 d.  arXiv:2601.15245v1 (main.tex l.187) cites this resolution. *)
Definition harris_triangle_free_degenerate_fractional_statement : Prop :=
  exists K d0 : nat,
    forall (d : nat) (G : sgraph),
      d0 <= d -> ω([set: G]) < 3 -> k_degenerate G d ->
      x130_frac_chi_le G (K * d) (trunc_log 2 d).

(** Corpus row: arxiv:2601.15245#02
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2601.15245__02/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2601.15245__02.json
    English statement: (Bradac, Fox, Steiner, Sudakov and Zhang, Problem 6.2, arXiv:2601.15245)
      Is the following statement true for all eps > 0?  If G is a d-degenerate triangle-free graph with maximum degree
      Delta(G) <= e^(d^(1-eps)), then we have chi(G) = O(d / log d).
    Definitions: [k_degenerate G d] (GTBase base.v); [Delta G] - the maximum degree (GTBase base.v); omega([set: G])
      < 3 - triangle-free and chi([set: G]) - the chromatic number (coq-graph-theory); [trunc_log 2 n] - the floor of
      log2 n (MathComp).
    Notes: The conclusion is complete in the TeX (main.tex l.777-780; the row's class_notes calling it truncated are
      wrong).  eps is 1/q for a positive integer q: the hypothesis weakens as eps decreases, so the statement for
      every eps > 0 is the statement for every eps = 1/q.  The constant of O(d / log d) may depend on eps (C after
      q), and the bound is cross-multiplied: chi(G) trunc_log 2 d <= C d; small d are absorbed by C, since chi(G) <=
      d + 1 for a d-degenerate G and trunc_log 2 d = 0 for d <= 1.  The hypothesis is raised to the power q, in base
      2: (trunc_log 2 Delta(G))^q <= d^(q-1).  The base and the floor are absorbed by the "for every eps", both
      ways, for large d: (i) the encoded hypothesis at q gives ln Delta < ln 2 (d^(1-1/q) + 1) <= d^(1-1/q) once
      d^(1-1/q) >= 3, the source's at eps = 1/q (at q = 1 it bounds Delta by 3, so chi <= 4); (ii) the source's at
      eps gives trunc_log 2 Delta <= d^(1-eps) / ln 2 <= d^(1-1/q) once d^(eps-1/q) >= 1 / ln 2, the encoded one at
      any q > 1 / eps.  The source's O(d / log d) and the encoded C d / trunc_log 2 d are the same up to the
      constant (d >= 2).
      Literature status: open at the pin.  The paper's Theorem 1.1 (main.tex l.145-147) bounds the chromatic number
      under n <= 2^(cd) vertices instead of a degree bound.  Guard: q >= 1 (0 < q) makes q - 1 a true subtraction. *)
Definition triangle_free_degenerate_small_degree_chi_statement : Prop :=
  forall q : nat, 0 < q ->
    exists C : nat,
      forall (d : nat) (G : sgraph),
        ω([set: G]) < 3 -> k_degenerate G d ->
        trunc_log 2 (Delta G) ^ q <= d ^ (q - 1) ->
        χ([set: G]) * trunc_log 2 d <= C * d.

(** Corpus row: arxiv:2601.15245#03
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2601.15245__03/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2601.15245__03.json
    English statement: (Bradac, Fox, Steiner, Sudakov and Zhang, Problem 6.3, arXiv:2601.15245)
      Is it true that if the chromatic number of a K_r-free d-degenerate graph is d+1, then the graph has
      e^(Omega_r(d)) vertices?
    Definitions: omega([set: G]) < r - K_r-free and chi([set: G]) - the chromatic number (coq-graph-theory);
      [k_degenerate G d] (GTBase base.v); [trunc_log 2 n] - the floor of log2 n (MathComp).
    Notes: "e^(Omega_r(d)) vertices" is #|G| >= e^(c_r d) for some c_r > 0 and every large d, i.e. d <= ln #|G| / c_r;
      the base 2 and the floor are absorbed by m (ln n <= log2 n < 2 trunc_log 2 n for n >= 2).  The asymptotic is in
      d for a fixed r, so m and the threshold d0 depend on r: K_(d+1) is d-degenerate with chromatic number d + 1 and
      is K_r-free when d + 1 < r, on only d + 1 vertices (grounding_X262).  Range: r >= 3, as the paper writes no
      range and for r <= 2 a K_r-free graph is edgeless (chromatic number at most 1), so chi = d + 1 forces d = 0
      and these r are vacuous.  Literature status: open at the pin.  The case r = 3 is the paper's Theorem 1.5
      (main.tex l.181-183: e^(Omega(d)) <= f(d), f(d) the smallest order of a triangle-free d-degenerate (d+1)-
      chromatic graph, from Theorem 1.1, l.145-147), and l.187 says that whether f_r(d) is exponential in d for r >= 4
      "remains open"; Problem 6.3 is main.tex l.784-787.  The row stays one statement over every r >= 3. *)
Definition kr_free_degenerate_critical_order_exponential_statement : Prop :=
  forall r : nat, 3 <= r ->
    exists m d0 : nat,
      forall (d : nat) (G : sgraph),
        d0 <= d -> ω([set: G]) < r -> k_degenerate G d -> χ([set: G]) = d.+1 ->
        d <= m * trunc_log 2 #|G|.

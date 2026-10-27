(** * Extremal.conjectures.X237 -- wave X237: Ramsey, Turan and density rows (2026-10-27)

    A six-row wave under the prospective contract of meta/faithfulness_policy.json.  Rows: erdos:181
    and erdos:1029 (diagonal Ramsey numbers), studies:std_schur_erd_s_problem (multicolour Ramsey
    numbers of cliques), erdos:572 and erdos:714 (Turan numbers of even cycles and of K_{r,r}) and
    studies:std_kuperwasser_samotij_wigderson_conjecture (forest removal and 2-density).  No
    vocabulary is copied: Ramsey numbers are Extremal.conjectures.X195's [x195_ramsey_number k Fam R]
    (k COLOURS; R is the least n such that K_n arrows Fam), Turan numbers are
    Extremal.conjectures.D2tur's [is_turan_number n Fam m] (m = ex(n; Fam), an attained maximum), and
    the maximum density m(G) <= a/b is Extremal.conjectures.X233's [x233_max_density_at_most G a b].
    GTBase supplies [product_hypercube], [cycle_graph], [complete_multipartite_graph], [del_edge_set],
    [edge_count] and [induced]; [is_forest] is upstream.  The grounding certificates are in
    grounding_X237.v. *)

From Extremal.foundations Require Import edge_colourings.
From Extremal.conjectures Require Import X195 D2tur X233.
(* GTBase last: its canonical [edge_count] must shadow D2tur's eta-alias of the same name. *)
From GTBase Require Import base common hypercubes complete_multipartite_graphs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x237 vocabulary ************************************************* *)

(** The 2-density m_2(H) is at most a/b: for every vertex set S with at least 3 vertices,
    (e(H[S]) - 1) / (|S| - 2) <= a/b, written b e + 2a <= a |S| + b without subtraction
    (arXiv:2402.03045 l.109; maxima over subgraphs are attained on vertex sets). *)
Definition x237_two_density_at_most (H : sgraph) (a b : nat) : Prop :=
  forall S : {set H}, 3 <= #|S| -> b * edge_count (induced S) + 2 * a <= a * #|S| + b.

(** F is the edge set of a forest of G: F consists of edges of G, and the spanning subgraph with
    exactly the edges of F is a forest (arXiv:2402.03045 l.169, l.930-932). *)
Definition x237_forest_edges (G : sgraph) (F : {set {set G}}) : Prop :=
  F \subset E(G) /\ is_forest [set: del_edge_set G (E(G) :\: F)].

(** ** X237 statements ******************************************************* *)

(** Corpus row: erdos:181
    Site: none
    Review: none
    English statement: (Erdos Problems #181)
      The Ramsey number of the n-dimensional hypercube Q_n (2^n vertices) satisfies R(Q_n) << 2^n:
      R(Q_n) <= C 2^n for some constant C and every n.
    Definitions: [x195_ramsey_number 2 Fam R] - R is the least n such that every 2-colouring of the
      edges of K_n has a monochromatic copy of the member of Fam, here Q_n
      (Extremal.conjectures.X195); [product_hypercube n] - Q_n as the iterated product K_2 x ... x
      K_2 (GTBase.hypercubes).
    Notes: the pinned statement is the erdosproblems.com text ("Prove that R(Q_n) << 2^n"); its
      status at the teorth/erdosproblems mirror (commit 10fb9c15) is open.  << is "at most a constant
      times" for every n; R is quantified as in X195 / X234 (the Ramsey number is unique).
      Literature status: open; the best known bound is R(Q_n) << 2^{(2-c)n} (Tikhomirov,
      arXiv:2208.14568). *)
Definition hypercube_ramsey_linear_statement : Prop :=
  exists C : nat, forall n R : nat,
    x195_ramsey_number 2 (fun _ : 'I_1 => product_hypercube n) R -> R <= C * 2 ^ n.

(** Corpus row: erdos:1029
    Site: none
    Review: none
    English statement: (Erdos Problems #1029)
      If R(k) is the diagonal Ramsey number of K_k, then R(k) / (k 2^{k/2}) tends to infinity.
    Definitions: [x195_ramsey_number 2 Fam R] - R = R(k) for Fam the single graph K_k
      (Extremal.conjectures.X195).
    Notes: the pinned statement is the erdosproblems.com text; status open at the teorth/erdosproblems
      mirror (10fb9c15).  "Tends to infinity" is: for every M, eventually R(k) >= M k 2^{k/2}; both
      sides are squared, R(k)^2 >= M^2 k^2 2^k, so that 2^{k/2} needs no root; a natural M suffices.
      Literature status: open; the best lower bound is (1 + o(1)) sqrt(2)/e k 2^{k/2} (Spencer). *)
Definition diagonal_ramsey_ratio_unbounded_statement : Prop :=
  forall M : nat, exists k0 : nat, forall k R : nat, k0 <= k ->
    x195_ramsey_number 2 (fun _ : 'I_1 => 'K_k) R -> M ^ 2 * k ^ 2 * 2 ^ k <= R ^ 2.

(** Corpus row: studies:std_schur_erd_s_problem
    Site: none
    Review: none
    English statement: (arXiv:1505.07429, Fox, Pach and Suk, "Semi-algebraic colorings of complete
      graphs", the problem of Schur and Erdos)
      For every fixed p >= 3, the m-colour Ramsey number R(p; m) of K_p is 2^{O(m)}.
    Definitions: [x195_ramsey_number m Fam R] - R is the least n such that every m-colouring of the
      edges of K_n has a monochromatic K_p (Extremal.conjectures.X195; its k counts colours).
    Notes: the source is 1505.07429v2 main.tex: R(p; m) for p >= 3 and m >= 2, and the open problem
      "to decide whether R(p;m) = 2^{O(m)}, for a fixed p" l.56, the definition l.71, Schur's bounds
      l.72-73.  The affirmative form is stated.  2^{O(m)} is "at most C^m for some C".  The guard
      m >= 1 instead of the source's m >= 2 is equivalent, since R(p; 1) = p (replace C by max(C, p)).
      Literature status: REFUTED at p = 3 BEFORE the corpus pin (b72c5857, 2026-09-23), not in the
      pinned status, in an unrefereed source: arXiv:2608.02522v2 (v1 2026-08-03, v2 2026-09-07)
      general.tex l.236-240 reports R_k(C_3) >= (c k^{1/3} / log k)^k from a 2026 OpenAI report,
      so R(3; m) = m^{Theta(m)} is superexponential.  The row is encoded as stated; the finding is
      reported for the corpus. *)
Definition multicolour_clique_ramsey_exponential_statement : Prop :=
  forall p : nat, 3 <= p -> exists C : nat,
    forall m R : nat, 1 <= m -> x195_ramsey_number m (fun _ : 'I_1 => 'K_p) R -> R <= C ^ m.

(** Corpus row: erdos:572
    Site: none
    Review: none
    English statement: (Erdos Problems #572)
      For k >= 3, ex(n; C_{2k}) >> n^{1+1/k}: some c > 0 has ex(n; C_{2k}) >= c n^{1+1/k} for all
      large n.
    Definitions: [is_turan_number n Fam m] - m is the maximum number of edges of an n-vertex graph
      with no (not necessarily induced) copy of the member of Fam (Extremal.conjectures.D2tur);
      [cycle_graph (2 * k)] - the cycle C_{2k} on 'I_{2k} (GTBase).
    Notes: the pinned statement is the erdosproblems.com text; status open at the teorth/erdosproblems
      mirror (10fb9c15).  c = a/b is rational (a smaller c is weaker), and the inequality is raised to
      the k-th power, (b ex)^k >= a^k n^{k+1}.  "Large n" (n0) is needed: ex(1; C_{2k}) = 0.
      Literature status: open for general k; known for k = 2, 3, 5 (Benson), with the general lower
      bound n^{1+2/(3k-3+nu)} (Lazebnik, Ustimenko and Woldar). *)
Definition even_cycle_turan_lower_statement : Prop :=
  forall k : nat, 3 <= k -> exists a b n0 : nat, [/\ 0 < a, 0 < b &
    forall n m : nat, n0 <= n -> is_turan_number n (fun _ : 'I_1 => cycle_graph (2 * k)) m ->
      a ^ k * n ^ k.+1 <= (b * m) ^ k].

(** Corpus row: erdos:714
    Site: none
    Review: none
    English statement: (Erdos Problems #714)
      For every r >= 2, ex(n; K_{r,r}) >> n^{2-1/r}.
    Definitions: [is_turan_number n Fam m] - m = ex(n; Fam) (Extremal.conjectures.D2tur);
      [complete_multipartite_graph 2 r] - K_{r,r}, two parts of r vertices (GTBase).
    Notes: the pinned statement is the erdosproblems.com question ("Is it true that ex(n; K_{r,r}) >>
      n^{2-1/r}?"); status open at the teorth/erdosproblems mirror (10fb9c15).  The affirmative form
      is stated.  The pinned text gives no range for r; r >= 2 is the guard, since at r = 1 the row
      is false (K_{1,1} = K_2 and ex(n; K_2) = 0, not >> n); r >= 2 is the setting of the
      Kovari-Sos-Turan upper bound.  ex^r >= c^r n^{2r-1} is written a^r n^{2r} <= (b ex)^r n, with
      no subtraction (equivalent for n >= 1).  Literature status: open for r >= 4; known for r = 2
      and r = 3 (Brown; Erdos, Renyi and Sos). *)
Definition complete_bipartite_turan_lower_statement : Prop :=
  forall r : nat, 2 <= r -> exists a b n0 : nat, [/\ 0 < a, 0 < b &
    forall n m : nat, n0 <= n -> is_turan_number n (fun _ : 'I_1 => complete_multipartite_graph 2 r) m ->
      a ^ r * n ^ (2 * r) <= (b * m) ^ r * n].

(** Corpus row: studies:std_kuperwasser_samotij_wigderson_conjecture
    Site: none
    Review: none
    English statement: (arXiv:2402.03045, Christoph, Martinsson, Steiner and Wigderson, "Resolution of
      the Kohayakawa-Kreuter conjecture", Conjecture 7.1 of Kuperwasser, Samotij and Wigderson)
      For every real m > 0, every graph G with m(G) <= m contains a forest F such that
      m_2(G - F) <= m, where m(G) = max e(J)/v(J) and m_2(H) = max (e(J) - 1)/(v(J) - 2) over
      subgraphs J with v(J) >= 1, resp. v(J) >= 3.
    Definitions: [x233_max_density_at_most G a b] - every vertex set S has b e(G[S]) <= a |S|, i.e.
      m(G) <= a/b (Extremal.conjectures.X233); [x237_two_density_at_most H a b] - m_2(H) <= a/b;
      [x237_forest_edges F] - F is the edge set of a forest of G (this file); [del_edge_set G F] -
      G - F, the edges of F removed (GTBase).
    Notes: the source is 2402.03045v2 main.tex: m_2 l.109, m l.128, G - F l.169, the conjecture
      l.930-932.  The maxima over subgraphs J are attained on vertex sets (more edges on the same
      vertex set only raise both ratios); an empty maximum (no 3-set) is vacuous.  m = a/b is
      rational: the real statement is equivalent to "every G has a forest F with m_2(G - F) <=
      m(G)", m(G) being rational (F empty for edgeless G), so nothing is lost.  Literature status:
      RESOLVED BEFORE the corpus pin (b72c5857, 2026-09-23), not in the pinned status, in an
      unrefereed preprint: Yancey, arXiv:2603.03086v2 (v1 2026-03-03, v2 2026-04-29; l.44-48: "We
      prove the conjecture in full"); his (a, b)-sparseness counts nonempty subgraphs, i.e. those
      with an edge (l.64, l.280), so (1, -1)-sparse is a forest, (m, 0)-sparse is m(G) <= m and
      (m, 1 - 2m)-sparse is m_2 <= m, exactly this row.  The row is encoded as stated; the finding is
      reported for the corpus. *)
Definition forest_removal_two_density_statement : Prop :=
  forall (a b : nat) (G : sgraph), 0 < a -> 0 < b -> x233_max_density_at_most G a b ->
    exists F : {set {set G}}, x237_forest_edges F /\ x237_two_density_at_most (del_edge_set G F) a b.

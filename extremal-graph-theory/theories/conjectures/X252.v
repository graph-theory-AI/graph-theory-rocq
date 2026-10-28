(** * Extremal.conjectures.X252 -- wave X252: ex(n;G) << n^{3/2} and 2-degeneracy, the extremal number of the 1-subdivision of K_k, dense neighbourhoods above the Turan number (2026-10-28)

    A three-row wave under the prospective contract of meta/faithfulness_policy.json.  Rows: erdos:113 (a bipartite G has
    ex(n;G) << n^{3/2} iff G is 2-degenerate), erdos:1021 (ex(n, G_k) << n^{3/2 - c_k} for the 1-subdivision G_k of K_k)
    and erdos:1079 (at least ex(n;K_r) edges give a vertex of degree >> n whose neighbourhood spans ex(d;K_{r-1}) edges).
    No local helper and no copied vocabulary: Turan numbers are Extremal.conjectures.D2tur's [is_turan_number n Fam m];
    GTBase supplies [bipartite], [subdivision], [min_degree_at_least], [edge_count] and 'K_n; [induced] and N(v) are
    upstream.  All three rows have pinned status "solved"; their literature lines are dated against the corpus pin
    (graph-conjectures b72c5857, 2026-09-23).  The sources are the Mac's deposit
    coordination/sources/x252-source-mac-20261028.  The grounding certificates are in grounding_X252.v. *)

From Extremal.conjectures Require Import D2tur.
(* GTBase last: its canonical [edge_count] must shadow D2tur's eta-alias of the same name. *)
From GTBase Require Import base common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X252 statements ******************************************************* *)

(** Corpus row: erdos:113
    Site: none
    Review: none
    English statement: (Erdos Problems #113, Erdos and Simonovits)
      A bipartite graph G has ex(n;G) << n^{3/2} if and only if G is 2-degenerate, that is, G contains no induced
      subgraph with minimum degree at least 3.
    Definitions: [is_turan_number n Fam m] - m = ex(n; Fam), an attained maximum over n-vertex graphs with no member of
      Fam as a subgraph (Extremal.conjectures.D2tur; here Fam is the single graph G); [bipartite G] - G has a proper
      2-colouring (GTBase.base); [min_degree_at_least H d] - every vertex of H has degree at least d (GTBase.base);
      [induced S] - the subgraph induced by S (upstream).
    Notes: the pinned statement is the erdosproblems.com text, encoded as stated: ex(n;G) << n^{3/2} is m^2 <= c n^3 for
      every n, c depending on G (when no G-free graph on n vertices exists, nothing is asserted at n); "contains no
      induced subgraph with minimal degree at least 3" ranges over the nonempty vertex sets S (the empty induced
      subgraph has a vacuous minimum degree).
      Literature status: FALSE at the pin (pinned status solved, class_notes "Solved (disproved)"; erdos rows read only
      open / solved).  The "only if" direction is refuted by Janzer, arXiv:2109.06110v2 (2021-11-08): Conjecture 1.3 is
      the row, and Theorem 1.4 gives, for every eps > 0, a 3-regular bipartite H with ex(n;H) = O(n^{4/3+eps}), which
      is not 2-degenerate; the live page: "Disproved by Janzer [Ja23b]".  The "if" direction is erdos:146 at r = 2,
      refuted as X240's Notes record (the OpenAI report "Ten Advances in Mathematics and Theoretical Computer
      Science", 2026-08-01, Chapter 10, Theorem 1.2, unrefereed, before the pin; CORPUS_FEEDBACK item 23). *)
Definition bipartite_three_halves_iff_two_degenerate_statement : Prop :=
  forall G : sgraph, bipartite G ->
    ((exists c : nat, forall n m : nat, is_turan_number n (fun _ : 'I_1 => G) m -> m ^ 2 <= c * n ^ 3) <->
     (forall S : {set G}, S != set0 -> ~ min_degree_at_least (induced S) 3)).

(** Corpus row: erdos:1021
    Site: none
    Review: none
    English statement: (Erdos Problems #1021, Erdos and Simonovits)
      For every k >= 3 there is a constant c_k > 0 such that ex(n, G_k) << n^{3/2 - c_k}, where G_k is the bipartite
      graph between y_1, ..., y_k and z_1, ..., z_(k choose 2) with each z_j joined to a unique pair of the y_i.
    Definitions: [is_turan_number n Fam m] (as at erdos:113); [subdivision G 2] - G with every edge replaced by a path
      through one new vertex (GTBase.base), so subdivision 'K_k 2 is G_k, the 1-subdivision of K_k.
    Notes: the pinned statement is the erdosproblems.com question ("Is it true that ..."), encoded in its affirmative
      form, which the literature proves before the pin (pinned status solved): Conlon and Lee, arXiv:1807.05008v2,
      Theorem 1.3 (any bipartite graph with maximum degree two on one side and no C_4 has ex(n, H) <= C n^{3/2 - delta};
      equivalently the subdivision of any graph, and it suffices for cliques); Janzer, arXiv:1809.00468v1, Theorem 3:
      c_k = 1/(4k - 6).  The live page calls G_k "the 1-subdivision of K_k".  Its aside "ex(n, C_6) << n^{7/6}"
      (k = 3) is a source discrepancy, not used: Janzer states ex(n, C_6) = Theta(n^{4/3}).
      c_k = 1/q for some q >= 1 (every c_k > 0 has some 1/q below it), and m <= C n^{3/2 - 1/q} is raised to the power
      2q: m^{2q} <= c n^{3q - 2} for every n, c depending on k; the subtraction 3q - 2 never truncates for q >= 1. *)
Definition one_subdivision_clique_turan_power_saving_statement : Prop :=
  forall k : nat, 3 <= k -> exists q c : nat, 1 <= q /\
    forall n m : nat, is_turan_number n (fun _ : 'I_1 => subdivision 'K_k 2) m -> m ^ (2 * q) <= c * n ^ (3 * q - 2).

(** Corpus row: erdos:1079
    Site: none
    Review: none
    English statement: (Erdos Problems #1079; Erdos 1975)
      Let r >= 4.  Every graph G on n vertices with at least ex(n;K_r) edges contains a vertex of degree d >>_r n whose
      neighbourhood contains at least ex(d;K_{r-1}) edges.
    Definitions: [is_turan_number n Fam m] (as at erdos:113); N(v) - the neighbourhood of v (upstream), #|N(v)| its
      degree; [edge_count (induced N(v))] - the number of edges inside N(v) (GTBase.common, upstream induced).
    Notes: the pinned statement is the erdosproblems.com question, encoded in its affirmative form, which the literature
      proves before the pin (pinned status solved).  Erdos [Er75, p.14] asks it with f_r(n) = ex(n;K_r) + 1 in both
      places; the encoded row, as the page states it, has ex in both places.  Bollobas and Thomason, JCTB 31 (1981)
      111-114 (the abstract; the full text was not obtained): if e(G) >= t_s(n) then G = T_s(n) or some vertex of
      degree d > c_s n has at least t_{s-1}(d) + 1 edges in its neighbourhood (s = r - 1); Bondy, JCTB 34 (1983): a
      vertex of maximum degree, in the strict form.  The Turan graph T_{r-1}(n) satisfies the non-strict row: each
      vertex has degree d >= n - ceil(n/3) >= n/2 and its neighbourhood is T_{r-2}(d), with exactly ex(d;K_{r-1})
      edges.  So the row holds for every n >= 2 and fails only for n <= 1, where no vertex has positive degree: hence
      the guard 2 <= #|G|.  d >>_r n is #|G| <= c #|N(v)|, c depending on r only; the subtraction r - 1 never truncates
      for r >= 4. *)
Definition turan_density_neighbourhood_turan_statement : Prop :=
  forall r : nat, 4 <= r -> exists c : nat, 1 <= c /\
    forall (G : sgraph) (m : nat), 2 <= #|G| -> is_turan_number #|G| (fun _ : 'I_1 => 'K_r) m -> m <= edge_count G ->
      exists v : G, #|G| <= c * #|N(v)| /\
        forall t : nat, is_turan_number #|N(v)| (fun _ : 'I_1 => 'K_(r - 1)) t -> t <= edge_count (induced N(v)).

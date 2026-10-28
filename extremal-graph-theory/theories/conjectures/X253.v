(** * Extremal.conjectures.X253 -- wave X253: the Turan number of the 1-subdivision of K_k with an apex, minimum degree forcing K_r in balanced r-partite graphs (2026-10-28)

    A two-row wave under the prospective contract of meta/faithfulness_policy.json.  Rows: erdos:926 (ex(n;H_k) <<_k
    n^{3/2} for the 1-subdivision of K_k with a vertex joined to its branch vertices) and erdos:1078 (minimum degree
    (r - 3/2 - o(1)) n forces K_r in an r-partite graph with n vertices in each part).  No local helper and no copied
    vocabulary: Turan numbers are Extremal.conjectures.D2tur's [is_turan_number n Fam m]; GTBase supplies [subdivision],
    [has_subgraph] and 'K_n; [add_node] and N(v) are upstream.  Both rows have pinned status "solved"; their literature
    lines are dated against the corpus pin (graph-conjectures b72c5857, 2026-09-23).  The sources are the Mac's deposit
    coordination/sources/x253-source-mac-20261028.  The grounding certificates are in grounding_X253.v. *)

From Extremal.conjectures Require Import D2tur.
(* GTBase last: its canonical [edge_count] must shadow D2tur's eta-alias of the same name. *)
From GTBase Require Import base common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X253 statements ******************************************************* *)

(** Corpus row: erdos:926
    Site: none
    Review: none
    English statement: (Erdos Problems #926, Erdos)
      Let k >= 4.  Then ex(n;H_k) <<_k n^{3/2}, where H_k is the graph on the vertices x, y_1, ..., y_k,
      z_1, ..., z_(k choose 2) in which x is adjacent to all y_i and each pair y_i, y_j is adjacent to a unique z.
    Definitions: [is_turan_number n Fam m] - m = ex(n; Fam), an attained maximum over n-vertex graphs with no member of
      Fam as a subgraph (Extremal.conjectures.D2tur; here Fam is the single graph H_k); [subdivision G 2] - G with every
      edge replaced by a path through one new vertex (GTBase.base): subdivision 'K_k 2 has the branch vertices y_i (inl)
      and one vertex z for each pair; [add_node G N] - G with one new vertex adjacent exactly to the vertices of N
      (upstream), here x joined to the branch vertices [set v | is_inl v].
    Notes: the pinned statement is the erdosproblems.com question ("Is it true that ..."), encoded in its affirmative
      form, which the literature proves before the pin (pinned status solved): Furedi, On a Turan type problem of Erdos,
      Combinatorica 11 (1991) 75-79 (DOI 10.1007/BF01375476): an n-vertex graph with at least k^{3/2} n^{3/2} edges
      contains L^k (p.75), and L^k (p.76: x_0 joined to each of y_1, ..., y_k and x_ij joined to y_i and y_j, a bipartite
      graph) is H_k; the live page: "The answer is yes, proved by Furedi [Fu91]".  The improvement ex(n;H_k) << k n^{3/2}
      of Alon, Krivelevich and Sudakov, which the page cites, is not used.  ex(n;H_k) <<_k n^{3/2} is m^2 <= c n^3 for
      every n, c depending on k (Furedi's bound gives c = k^3). *)
Definition clique_subdivision_apex_turan_three_halves_statement : Prop :=
  forall k : nat, 4 <= k -> exists c : nat,
    forall n m : nat,
      is_turan_number n (fun _ : 'I_1 => add_node (subdivision 'K_k 2) [set v | is_inl v]) m -> m ^ 2 <= c * n ^ 3.

(** Corpus row: erdos:1078
    Site: none
    Review: none
    English statement: (Erdos Problems #1078, Bollobas, Erdos and Szemeredi)
      Let G be an r-partite graph with n vertices in each part.  If G has minimum degree >= (r - 3/2 - o(1)) n then G
      contains a K_r.
    Definitions: an r-partite graph with n vertices in each part - a map p : G -> 'I_r with fibres of size n and no edge
      inside a fibre; N(v) - the neighbourhood of v (upstream), #|N(v)| its degree; [has_subgraph G 'K_r] - K_r is a
      subgraph of G (GTBase.common).
    Notes: the o(1) is read as in the original source, Bollobas, Erdos and Szemeredi, On complete subgraphs of
      r-chromatic graphs, Discrete Math. 13 (1975) 97-107, p.98: f_r(n) is the least integer such that every such graph
      with minimum degree > f_r(n) contains K_r, c_r = lim_n f_r(n)/n, and they conjecture lim_r (c_r - r + 2) = 1/2,
      having proved c_r >= r - 2 + 1/2 - 1/(2(r - 2)) for r > 4 (the page: r - 3/2 "would be the best possible").  The
      row is the forcing half, limsup_r (c_r - r + 2) <= 1/2, encoded with eps = 1/q: for every q >= 1, for all large r
      and then all large n, minimum degree >= (r - 3/2 + 1/q) n forces K_r (2q deg >= (2qr - 3q + 2) n, written without
      a subtraction).  This is the row with its o(1) a function of r tending to 0, of either sign; no range of r is
      stated or needed.  The reading "for every eps > 0, minimum degree >= (r - 3/2 - eps) n eventually forces K_r" is
      refuted by the lower bound above and is not the row.  Erdos, Some recent progress on extremal problems in graph
      theory (1975), p.12 (read from the page scan of the Renyi PDF; its OCR text corrupts the formulas), prints the
      stronger fixed-r form "if each vertex has valency >= (r - 3/2) n then our graph contains a K(r)"; it is not the
      encoded row.
      Literature status: proved before the pin (pinned status solved).  Haxell, A note on vertex list colouring, CPC 10
      (2001): a graph of maximum degree d whose vertex classes have size >= 2d has an independent transversal (as
      Szabo and Tardos, Combinatorica 26 (2006), Theorem 1.1, state it); applied to the non-adjacent pairs between the
      parts, minimum degree >= (r - 3/2) n gives K_r for every r and n >= 1, and Haxell and Szabo, CPC 15 (2006), p.2,
      say this settled the conjecture.  The exact threshold (r - 1) n - ceil(s n / (2s - 1)), s = floor(r/2), follows
      from Haxell and Szabo's Theorem 1.1.  The pinned citation key BES75 names a different paper (Burr, Erdos and
      Spencer); the source is BES75b (CORPUS_FEEDBACK). *)
Definition balanced_multipartite_min_degree_clique_statement : Prop :=
  forall q : nat, 1 <= q -> exists r0 : nat, forall r : nat, r0 <= r -> exists n0 : nat,
    forall (n : nat) (G : sgraph) (p : G -> 'I_r), n0 <= n ->
      (forall i : 'I_r, #|[set v | p v == i]| = n) ->
      (forall x y : G, x -- y -> p x != p y) ->
      (forall v : G, (2 * q * r + 2) * n <= 2 * q * #|N(v)| + 3 * q * n) ->
      has_subgraph G 'K_r.

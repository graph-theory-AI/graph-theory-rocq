(** * Hypergraph.conjectures.X225 -- hypergraph Turan exponents and hypergraph minors rows (wave X225, 2026-09-23) *)

From GTBase Require Export base.
From Hypergraph.foundations Require Export hypergraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The hypergraph vocabulary of this wave -- [hg_uniform], [hg_loopless],
    [hg_partite_uniform], [hg_colourable], [hg_has_clique_minor],
    [hg_degeneracy], [hg_skel_degeneracy], [hg_dmax], [hg_containsb],
    [hg_turan] -- lives in [Hypergraph.foundations.hypergraph], shared with the
    X217 wave.  Only the Latin-square pattern of row arxiv:2401.00359#02 is
    local. *)

(** ** Local x225 vocabulary *********************************************** *)

Notation x225_I3 i := (@Ordinal 3 i isT).

(** A [d x d] Latin square: every row and every column is injective. *)
Definition x225_latin_square (d : nat) (L : 'I_d -> 'I_d -> 'I_d) : Prop :=
  (forall i : 'I_d, injective (L i)) /\ (forall j : 'I_d, injective (fun i => L i j)).

(** [H_L]: the 3-uniform 3-partite hypergraph on three disjoint copies of
    [{1,...,d}] whose hyperedges are the triples [(i, j, L i j)]. *)
Definition x225_latin_hypergraph (d : nat) (L : 'I_d -> 'I_d -> 'I_d)
  : {set {set 'I_3 * 'I_d}} :=
  [set [set (x225_I3 0, i); (x225_I3 1, j); (x225_I3 2, L i j)]
     | i in [set: 'I_d], j in [set: 'I_d]].

(** ** X225 statements ***************************************************** *)

(** Corpus row: arxiv:2206.13635#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2206.13635__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2206.13635__00.json
    English statement: (Steiner 2022, "Coloring hypergraphs with excluded minors", Conjecture 2)
      For every integer t at least 2 both of the following hold.  First, every loopless
      hypergraph -- one in which every hyperedge has at least two vertices -- that has no
      K_t minor can be properly coloured with the ceiling of 3(t-1)/2 colours, where a
      colouring is proper when no hyperedge is monochromatic.  Second, that number of colours
      cannot be lowered: some loopless K_t-minor-free hypergraph admits no proper colouring
      with one colour fewer.  A K_t minor is a family of t non-empty pairwise disjoint sets
      of vertices, each of them connected in the subhypergraph spanned by it, such that any
      two of them are joined by a hyperedge that lies inside their union and meets both.
    Definitions: [hg_loopless E] - every hyperedge has at least two vertices
      (hypergraph-theory/theories/foundations/hypergraph.v); [hg_has_clique_minor E t] - the
      K_t-minor model described above, with branch sets connected via [hg_connected_on], i.e.
      in the subhypergraph consisting of the hyperedges lying entirely inside the branch set
      (same file); [hg_colourable E m] - some colouring of the vertices by m colours leaves no
      hyperedge monochromatic (same file); [ceil_div a b] - the ceiling of a/b (GTBase.base).
    Notes: MODELLING CHOICES.  (1) The corpus text is the EQUALITY h(t) = ceil(3(t-1)/2) for
      the least integer h(t) bounding the chromatic number on K_t-minor-free hypergraphs; it
      is rendered as the conjunction of the upper half ("every K_t-minor-free hypergraph is
      ceil(3(t-1)/2)-colourable", the open content, which is also the source's "in other
      words" reading) and the tightness half ("some K_t-minor-free hypergraph is not
      colourable with one colour fewer", proved in the source by an explicit construction).
      Together the two halves say exactly h(t) = ceil(3(t-1)/2).  (2) BRANCH-SET CONNECTIVITY
      is the STRICT reading: a branch set must be connected using only hyperedges that lie
      entirely inside it (the contraction reading of "subhypergraphs and contracted
      hyperedges").  Sanity check of that choice: it gives h(2) = 2 = ceil(3/2), because the
      3-uniform hypergraph with a single hyperedge is then K_2-minor-free and not
      1-colourable (grounding_X225.v, [x225_conj2_tight_at_two]); under the weaker reading
      (hyperedges allowed to stick out of the branch set) that example has a K_2 minor and
      the source's own lower bound would fail at t = 2.  (3) The LOOPLESS guard is
      load-bearing: a hyperedge with at most one vertex is monochromatic under every
      colouring, so it would make the conclusion false while adding no minor
      (grounding_X225.v, [x225_loopless_guard_has_teeth]).  (4) Hypergraphs are finite: the
      vertices form a [finType] and the hyperedges a finite family of vertex sets. *)
Definition kt_minor_free_hypergraph_chromatic_three_halves_statement : Prop :=
  forall t : nat,
    2 <= t ->
    (forall (T : finType) (E : {set {set T}}),
       hg_loopless E ->
       ~ hg_has_clique_minor E t ->
       hg_colourable E (ceil_div (3 * t.-1) 2)) /\
    (exists (T : finType) (E : {set {set T}}),
       [/\ hg_loopless E,
           ~ hg_has_clique_minor E t &
           ~ hg_colourable E (ceil_div (3 * t.-1) 2).-1]).

(** Corpus row: arxiv:2206.13635#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2206.13635__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2206.13635__01.json
    English statement: (Steiner 2022, "Coloring hypergraphs with excluded minors", Problem 1)
      Is every loopless hypergraph without a K_3 minor 3-colourable?  That is: whenever every
      hyperedge of a finite hypergraph has at least two vertices and there are no three
      non-empty pairwise disjoint vertex sets, each connected in the subhypergraph spanned by
      it and any two of them joined by a hyperedge inside their union meeting both, the
      vertices can be coloured with three colours so that no hyperedge is monochromatic.
    Definitions: [hg_loopless E] - every hyperedge has at least two vertices
      (hypergraph-theory/theories/foundations/hypergraph.v); [hg_has_clique_minor E 3] - a
      K_3-minor model: three non-empty pairwise disjoint branch sets, each connected in the
      subhypergraph spanned by it, pairwise joined by a hyperedge inside their union (same
      file); [hg_colourable E 3] - three colours suffice to leave no hyperedge monochromatic
      (same file).
    Notes: the source poses this as a question; it is recorded as the smallest open case
      (t = 3) of Conjecture 2, where [ceil_div (3 * 2) 2] is exactly 3, and the best known
      upper bound is 4.  It is stated here in the affirmative, the repository convention for
      "is every ... ?" rows.  The minor notion, the looplessness guard and the finiteness
      convention are the ones documented on
      [kt_minor_free_hypergraph_chromatic_three_halves_statement] above. *)
Definition k3_minor_free_hypergraph_three_colourable_statement : Prop :=
  forall (T : finType) (E : {set {set T}}),
    hg_loopless E ->
    ~ hg_has_clique_minor E 3 ->
    hg_colourable E 3.

(** Corpus row: arxiv:2401.00359#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2401.00359__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2401.00359__01.json
    English statement: (Fox, Sankar, Simkin, Tidor and Zhou 2024, Conjecture 6.2)
      For every k at least 2 there is a positive constant c_k, depending only on k, such that
      for every k-uniform k-partite hypergraph H with at least one hyperedge there is a
      positive constant K, allowed to depend on H, with ex(n,H) raised to the power d_max(H),
      times n^{c_k}, at most K times n raised to the power k times d_max(H), for all
      sufficiently large n.  Equivalently, ex(n,H) is at most O_H(n^{k - c_k/d_max(H)}).
      Here ex(n,H) is the largest number of hyperedges of a k-uniform hypergraph on n
      vertices that contains no copy of H, and d_max(H) is the largest of the skeletal
      degeneracies d_i(H) for i between 1 and k-1, where d_i(H) is the degeneracy of the
      (i+1)-uniform hypergraph made of all (i+1)-element sets contained in a hyperedge of H.
    Definitions: [hg_uniform F k] - every hyperedge has exactly k vertices
      (hypergraph-theory/theories/foundations/hypergraph.v); [hg_partite_uniform part F] -
      [part] splits the vertices into k classes and every hyperedge meets each class exactly
      once (same file); [hg_containsb F E] - E contains a copy of the pattern F, i.e. an
      injective vertex map sending every hyperedge of F to a hyperedge of E (same file);
      [hg_turan F k n] - the Turan number ex(n,F): the largest number of hyperedges of a
      k-uniform hypergraph on the n vertices ['I_n] containing no copy of F (same file);
      [hg_degeneracy E] - the least d such that every non-empty vertex set spans a vertex of
      degree at most d in the subhypergraph it spans (same file); [hg_skeleton E i] - the
      (i+1)-element sets contained in a hyperedge (same file); [hg_skel_degeneracy E i] -
      d_i(E), the degeneracy of that i-skeleton (same file); [hg_dmax E k] - the maximum of
      d_i(E) over 1 <= i < k (same file); [eventually P] - P holds for all sufficiently large
      n (GTBase.asymptotics).
    Notes: MODELLING CHOICES.  (1) EXPONENT CLEARED TO NAT FORM: the real exponent
      k - c_k/d_max(H) is removed by raising the bound to the power d_max(H) and multiplying
      through by n^{c_k}, which is an equivalence for positive d_max: ex <= K' n^{k-c/dmax}
      iff ex^dmax * n^c <= K n^{k*dmax} with K = K'^dmax.  So c_k stays an existential
      depending only on k, while the O_H implied constant K is chosen after H, exactly as in
      the source.  (2) GUARD [F != set0]: the empty pattern has d_max 0 and Turan number 0,
      and the cleared inequality would degenerate to n^{c_k} <= K, which is refutable
      (grounding_X225.v, [x225_empty_pattern_guard_has_teeth]); every genuine k-partite
      pattern has a hyperedge.  (3) GUARD [2 <= k]: the source states the conjecture for
      k >= 3; the k = 2 instance is the Furedi / Alon-Krivelevich-Sudakov theorem on
      degenerate bipartite graphs, so admitting it adds a settled case and no open content.
      (4) Copies are NOT induced (the pattern's hyperedges must be hyperedges of the host;
      extra hyperedges are allowed) and the vertex map is injective, the standard reading of
      the Turan number.  (5) The host vertex set is ['I_n], i.e. n labelled vertices. *)
Definition kpartite_hypergraph_turan_exponent_dmax_statement : Prop :=
  forall k : nat,
    2 <= k ->
    exists ck : nat,
      0 < ck /\
      forall (S : finType) (F : {set {set S}}) (part : S -> 'I_k),
        F != set0 ->
        hg_uniform F k ->
        hg_partite_uniform part F ->
        exists K : nat,
          0 < K /\
          eventually (fun n =>
            (hg_turan F k n) ^ (hg_dmax F k) * n ^ ck <= K * n ^ (k * hg_dmax F k)).

(** Corpus row: arxiv:2401.00359#02
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2401.00359__02/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2401.00359__02.json
    English statement: (Fox, Sankar, Simkin, Tidor and Zhou 2024, Conjecture 6.4)
      There are absolute positive constants a and b such that the following holds for every d
      at least 2 and every d by d Latin square L.  Let H_L be the 3-uniform 3-partite
      hypergraph on three disjoint copies of {1,...,d} whose hyperedges are the triples
      consisting of i in the first copy, j in the second and L(i,j) in the third.  Then for
      all sufficiently large n, n^{3d} is at most ex(n,H_L)^d times n^a, and ex(n,H_L)^d
      times n^b is at most n^{3d}.  Equivalently ex(n,H_L) = n^{3 - Theta(1/d)}.
    Definitions: [x225_latin_square L] - every row and every column of L is injective
      (hypergraph-theory/theories/conjectures/X225.v); [x225_latin_hypergraph L] - the
      hypergraph H_L above, on the vertex set ['I_3 * 'I_d] (same file); [hg_turan F 3 n] -
      the Turan number ex(n,F) over 3-uniform hypergraphs on n vertices
      (hypergraph-theory/theories/foundations/hypergraph.v); [hg_containsb F E] - E contains
      an injective copy of F (same file); [eventually P] - P holds for all sufficiently large
      n (GTBase.asymptotics).
    Notes: MODELLING CHOICES.  (1) EXPONENT CLEARED TO NAT FORM: ex(n,H_L) = n^{3-Theta(1/d)}
      is rendered as the pair of inequalities n^{3d} <= ex^d * n^a (the lower bound
      ex >= n^{3-a/d}) and ex^d * n^b <= n^{3d} (the upper bound ex <= n^{3-b/d}), both
      obtained by raising to the power d; no truncated subtraction is used.  (2) The
      constants a and b are quantified OUTERMOST, hence independent of d and of the Latin
      square: that is what the Theta(1/d) in the exponent asserts.  (3) GUARD [2 <= d]: for
      d = 1 the pattern H_L is a single hyperedge, so ex(n,H_L) = 0 as soon as n >= 3 and the
      lower bound cannot hold; the conjecture is about d by d Latin squares as d grows.
      (4) The guard [x225_latin_square L] is load-bearing: a constant L gives a pattern with
      d hyperedges only, not the intended H_L (grounding_X225.v,
      [x225_latin_guard_has_teeth]).  (5) H_L is 3-uniform and 3-partite by construction: its
      hyperedges carry one vertex in each of the three copies of {1,...,d}. *)
Definition latin_square_hypergraph_turan_exponent_statement : Prop :=
  exists a b : nat,
    [/\ 0 < a,
        0 < b &
        forall (d : nat) (L : 'I_d -> 'I_d -> 'I_d),
          2 <= d ->
          x225_latin_square L ->
          eventually (fun n =>
            n ^ (3 * d) <= (hg_turan (x225_latin_hypergraph L) 3 n) ^ d * n ^ a /\
            (hg_turan (x225_latin_hypergraph L) 3 n) ^ d * n ^ b <= n ^ (3 * d))].

(** * GTMisc.conjectures.X288 -- v2 rows: pure pairs for forests (Liebenau-Pilipczuk), Le's induced paths and cycles
      in 2O-free graphs, and the coarse Menger conjectures (strong form as X116's statement, weak form) *)

From GTBase Require Import base set_pairs induced_paths induced_cycles walks_paths balls distant_paths.
From GTMisc.conjectures Require Import X116.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X288 statements ******************************************************** *)

(** Corpus row: studies:std_liebenau_pilipczuk_conjecture
    Site: none
    Review: none
    English statement: (Liebenau and Pilipczuk; studies slice of the corpus, record arXiv:1809.00919)
      For every forest H, there exists eps > 0 such that for every graph G with |G| > 1 that is both H-free and
      H-bar-free, there is a pure pair (A, B) with |A|, |B| >= eps |G|.
    Definitions: [is_forest [set: H]] - H has no cycle (coq-graph-theory); [induced_free G H] - no induced
      subgraph of G is isomorphic to H (GTBase common.v); [compl H] - the complement of H (coq-graph-theory);
      [anticomplete A B] - A and B are disjoint with no edge between them, [complete_between A B] - every vertex
      of A is adjacent to every vertex of B (GTBase set_pairs.v).
    Notes: encoded as stated (1809.00919v3 source.tex l.146-147, Theorem 1.2): eps is written 1 / m for a natural
      m > 0, so |A|, |B| >= eps |G| reads |G| <= m * |A| and |G| <= m * |B| (a real eps > 0 gives m = ceil(1 / eps),
      and conversely eps = 1 / m).  A pure pair is disjoint and complete or anticomplete (l.106-109); the order
      condition |G| > 1 is kept: without it the row fails at the one-vertex graph (grounding_X288).  Graphs are
      finite and simple, H-free means no induced copy of H (l.102-105).  Literature status: TRUE at the pin, by
      the paper itself (l.149: "This is true, and a consequence of our main result"); recorded open at the pin, for
      lit24.  Theorem statements read, proofs not verified. *)
Definition liebenau_pilipczuk_forest_pure_pair_statement : Prop :=
  forall H : sgraph, is_forest [set: H] ->
    exists m : nat, 0 < m /\
      forall G : sgraph, 1 < #|G| -> induced_free G H -> induced_free G (compl H) ->
        exists A B : {set G},
          (anticomplete A B || [disjoint A & B] && complete_between A B) /\
          #|G| <= m * #|A| /\ #|G| <= m * #|B|.

(** Corpus row: studies:std_le_s_induced_paths_conjecture
    Site: none
    Review: none
    English statement: (Le's induced-paths conjecture; studies slice of the corpus, record arXiv:2212.01089)
      There exists c > 0 such that every 2O-free graph G has at most |G|^c induced paths.
    Definitions: [seq_cycle (--) c] - c is a cycle of G with at least three vertices (GTBase walks_paths.v);
      [anticomplete A B] - disjoint with no edge between them (GTBase set_pairs.v); [seq_vertices p] - the vertex
      set of a sequence (GTBase walks_paths.v); [nonempty_induced_path p] - p is a nonempty path of G without a
      chord (GTBase induced_paths.v).
    Notes: encoded as stated (2212.01089v2 source.tex l.111-113, Conjecture 1.1).  2O-free: no two cycles of G are
      vertex-disjoint and anticomplete (l.103-106), written as the negation of two seq_cycle's with anticomplete
      vertex sets.  An induced path is an induced subgraph, so it is determined by its vertex set: the number of
      induced paths is the number of vertex sets of nonempty chordless paths, and the row bounds every family P of
      such vertex sets by |G|^c.  Every path has at least one vertex, so the one-vertex graph has exactly one
      induced path (l.131).  Literature status: TRUE at the pin, by the paper itself (Theorem 1.2, l.127-130, for
      every s; l.124-125); recorded open at the pin, for lit24.  Theorem statements read, proofs not verified. *)
Definition le_induced_paths_polynomial_statement : Prop :=
  exists c : nat, 0 < c /\
    forall G : sgraph,
      ~ (exists c1 c2 : seq G,
           [/\ seq_cycle (--) c1, seq_cycle (--) c2 & anticomplete (seq_vertices c1) (seq_vertices c2)]) ->
      forall P : {set {set G}},
        (forall S, S \in P -> exists p : seq G, nonempty_induced_path p /\ seq_vertices p = S) ->
        #|P| <= #|G| ^ c.

(** Corpus row: studies:std_le_s_conjecture_on_induced_cycles_in_2o_free_gra
    Site: none
    Review: none
    English statement: (Le's induced-cycles conjecture; studies slice of the corpus, record arXiv:2212.01089)
      There exists c > 0 such that every 2O-free graph G has at most |G|^c induced cycles.
    Definitions: [seq_cycle (--) c] - c is a cycle of G with at least three vertices (GTBase walks_paths.v);
      [anticomplete A B] - disjoint with no edge between them (GTBase set_pairs.v); [seq_vertices p] - the vertex
      set of a sequence (GTBase walks_paths.v); [chordless_cycle c] - c is a cycle of G with at least three
      vertices and no chord (GTBase induced_cycles.v).
    Notes: encoded as stated (2212.01089v2 source.tex l.108-109, the prose before Conjecture 1.1).  2O-free as in
      the induced-paths row (l.103-106).  An induced cycle is determined by its vertex set, so the row bounds every
      family P of vertex sets of chordless cycles by |G|^c.  Literature status: TRUE at the pin, by the paper itself
      (Theorem 1.2, l.127-130, proves the induced-paths form, "and hence both conjectures", l.124); recorded open at
      the pin, for lit24.  Theorem statements read, proofs not verified. *)
Definition le_induced_cycles_polynomial_statement : Prop :=
  exists c : nat, 0 < c /\
    forall G : sgraph,
      ~ (exists c1 c2 : seq G,
           [/\ seq_cycle (--) c1, seq_cycle (--) c2 & anticomplete (seq_vertices c1) (seq_vertices c2)]) ->
      forall P : {set {set G}},
        (forall S, S \in P -> exists p : seq G, chordless_cycle p /\ seq_vertices p = S) ->
        #|P| <= #|G| ^ c.

(** Corpus row: studies:std_le_s_conjecture_on_induced_paths_in_o_free_graph
    Site: none
    Review: none
    English statement: (Le's conjecture as quoted by Bonnet et al.; studies slice of the corpus, record
      arXiv:2206.00594)
      There is a constant c such that every O_2-free n-vertex graph has at most n^c distinct induced paths.
    Definitions: [le_induced_paths_polynomial_statement] - Le's induced-paths conjecture as encoded for the corpus
      row studies:std_le_s_induced_paths_conjecture (this file: some c > 0 with at most |G|^c induced paths in every
      2O-free graph).
    Notes: this studies row is the same conjecture as studies:std_le_s_induced_paths_conjecture, so it is a synonym
      of that statement (as X254 encodes the Tomescu duplicates), not a second encoding.  O_2-free means no two
      independent cycles, that is vertex-disjoint cycles with no edge between them (2206.00594v5 revision.tex
      l.193-199), which is 2O-free; "a constant c" and "c > 0" agree, since a bound with c = 0 also holds with c = 1
      and the empty graph has no path.  The source quotes it as Conjecture 1.5 (l.335-337).  CORPUS_FEEDBACK item 72
      proposes the upstream alias.  Literature status: TRUE at the pin (l.339: solved by Nguyen, Scott and Seymour);
      recorded open at the pin, for lit24. *)
Definition le_induced_paths_o2_free_duplicate_statement : Prop :=
  le_induced_paths_polynomial_statement.

(** Corpus row: studies:std_coarse_menger_conjecture_159
    Site: none
    Review: none
    English statement: (the coarse Menger conjecture as stated by Nguyen, Scott and Seymour; studies slice of the
      corpus, record arXiv:2508.14332)
      For all integers k, c >= 1 there exists l > 0 such that for every graph G and S, T subsets of V(G), either
      there are k paths between S and T pairwise at distance at least c, or there is a set X with |X| <= k - 1
      such that every path between S and T contains a vertex at distance at most l from some member of X.
    Definitions: [coarse_menger_paths_bounded_separator_statement] - the coarse Menger conjecture as encoded for
      the corpus row studies:std_coarse_menger_conjecture (GTMisc conjectures/X116.v: for all k, d >= 1 some l > 0
      such that every G, S, T has k distinct S-T paths pairwise at distance at least d, or a set X with |X| <= k - 1
      whose closed l-ball meets every S-T path).
    Notes: this studies row is the same conjecture as studies:std_coarse_menger_conjecture, so it is a synonym of
      X116's statement, not a second encoding: 2508.14332v1 paper.tex l.112-118 and 2401.06685v2 source.tex
      l.108-115 state the same proposition, with c for d; distance is the number of edges of a shortest joining
      path in both (paper.tex l.104-105).  CORPUS_FEEDBACK item 73 proposes the upstream alias.  Literature status:
      FALSE at the pin, for every k >= 3 even when c = 3 and G has maximum degree three (2401.06685v2 Theorem 1.3,
      l.121-131; 2508.14332v1 l.121-122); recorded open at the pin, for lit24. *)
Definition coarse_menger_paths_bounded_separator_duplicate_statement : Prop :=
  coarse_menger_paths_bounded_separator_statement.

(** Corpus row: studies:std_weak_coarse_menger_conjecture_nguyen_scott_seymo
    Site: none
    Review: none
    English statement: (Nguyen, Scott and Seymour's weak coarse Menger conjecture; studies slice of the corpus,
      record arXiv:2508.14332)
      For all integers k, c >= 1 there exist m, l > 0 such that for every graph G and S, T subsets of V(G), either
      there are k paths between S and T pairwise at distance at least c, or there is a set X with |X| <= m such
      that every path between S and T contains a vertex at distance at most l from some member of X.
    Definitions: [has_k_distant_set_paths c k S T] - k distinct S-T paths whose closed (c-1)-balls avoid one
      another (GTBase distant_paths.v); [seq_set_path S T p] - p is a simple path from S to T (GTBase
      walks_paths.v); [set_ball l X] - the closed l-ball around X, inside the components of X (GTBase balls.v);
      [seq_vertices p] - the vertex set of p (GTBase walks_paths.v).
    Notes: encoded as stated (2508.14332v1 paper.tex l.130-138).  "Pairwise at distance at least c" means no
      vertex of one path lies within distance c - 1 of the other, so for c >= 1 the paths are vertex-disjoint;
      distance is the number of edges of a shortest joining path (l.104-105), and a vertex in another component is
      at no finite distance.  S and T need not be disjoint, and a one-vertex path in S and T is an S-T path.  m and
      l may depend on k and c, as printed.  Literature status: FALSE at the pin, already for k = c = 3 (Theorem 1.3,
      l.140-147); recorded open at the pin, for lit24. *)
Definition weak_coarse_menger_statement : Prop :=
  forall k c : nat, 1 <= k -> 1 <= c ->
    exists m l : nat, [/\ 0 < m, 0 < l &
      forall (G : sgraph) (S T : {set G}),
        has_k_distant_set_paths c k S T \/
        exists X : {set G}, #|X| <= m /\
          forall p : seq G, seq_set_path S T p ->
            exists2 v : G, v \in seq_vertices p & v \in set_ball l X].

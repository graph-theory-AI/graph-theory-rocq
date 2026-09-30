(** * Chromatic.conjectures.X219 -- list colouring, surfaces and planar degeneracy rows (wave X219, 2026-09-23) *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x219 vocabulary ***********************************************

    Reused instead of re-encoded: [choosable] / [list_colourable] / [wagner_planar]
    / [triangle_free] / [k_degenerate] (GTBase base.v), [surface_embeddable]
    (GTBase surface.v), [is_forest] / [induced] / [del_edges] (coq-graph-theory
    sgraph.v), [trunc_log] (MathComp). *)

(** [G] is CRITICAL for the (subgraph-monotone) property [P]: [P] fails on [G]
    but holds on every one-vertex-deleted and every one-edge-deleted subgraph.
    For a property preserved by taking subgraphs -- as both 5-choosability and
    "chromatic number at most 5" are -- this is exactly "P fails on G but holds
    on every proper subgraph of G". *)
Definition x219_subgraph_critical_for (P : sgraph -> Prop) (G : sgraph) : Prop :=
  [/\ ~ P G,
      forall v : G, P (induced ([set: G] :\ v)) &
      forall u v : G, u -- v -> P (del_edges [set u; v])].

(** A 2-colouring of [G] witnessing bipartiteness with [A] as one side. *)
Definition x219_bipartition (G : sgraph) (A : {set G}) : Prop :=
  forall u v : G, u -- v -> (u \in A) != (v \in A).

(** Maximum degree at most [D] on the part [A]. *)
Definition x219_max_degree_on (G : sgraph) (A : {set G}) (D : nat) : Prop :=
  forall v : G, v \in A -> #|N(v)| <= D.

(** [(kA,kB)]-choosability of the bipartite graph [G] with side [A]: every list
    assignment giving at least [kA] colours to each vertex of [A] and at least
    [kB] colours to each vertex outside [A] admits a proper list colouring. *)
Definition x219_kAkB_choosable (G : sgraph) (A : {set G}) (kA kB : nat) : Prop :=
  forall (C : finType) (L : G -> {set C}),
    (forall v : G, v \in A -> kA <= #|L v|) ->
    (forall v : G, v \notin A -> kB <= #|L v|) ->
    list_colourable L.

(** [k]-EDGE-choosability: every symmetric assignment of lists of at least [k]
    colours to the edges admits a proper edge colouring from the lists. *)
Definition x219_edge_choosable (G : sgraph) (k : nat) : Prop :=
  forall (C : finType) (L : G -> G -> {set C}),
    (forall u v : G, L u v = L v u) ->
    (forall u v : G, u -- v -> k <= #|L u v|) ->
    exists col : G -> G -> C,
      [/\ forall u v : G, col u v = col v u,
          forall u v : G, u -- v -> col u v \in L u v &
          forall u v w : G, u -- v -> u -- w -> v != w -> col u v != col u w].

(** Fractional vertex-arboricity at most two, in [b]-fold form: there EXISTS a
    fold parameter [b >= 1] and [2*b] induced forests covering every vertex at
    least [b] times.  The parameter must be EXISTENTIAL, exactly as in X130's
    [x130_frac_chi_le]: the covering LP has rational data, so its optimum is
    attained and one good [b] is all that "va_f(G) <= 2" asks for.  A universal
    [b] would instead collapse to its [b = 1] instance -- the admissible [b] are
    closed under addition (take the disjoint union of two families) -- i.e. to
    the INTEGRAL vertex-arboricity being at most two, which is false for planar
    graphs. *)
Definition x219_frac_vertex_arboricity_le_two (G : sgraph) : Prop :=
  exists b : nat,
    0 < b /\
    exists F : 'I_(2 * b) -> {set G},
      (forall i : 'I_(2 * b), is_forest (F i)) /\
      (forall v : G, b <= #|[set i : 'I_(2 * b) | v \in F i]|).

(** ** X219 statements *****************************************************)

(** Corpus row: arxiv:2407.18800#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2407.18800__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2407.18800__00.json
    English statement: (Dvorak and Moreno Penarrubia 2024, Conjecture 2, arXiv:2407.18800)
      A finite simple graph that embeds in the torus -- that is, a connected graph of orientable
      genus at most one -- is critical for 5-choosability if and only if it is 6-critical, where
      critical for a property means that the property fails on the graph but holds on every graph
      obtained by deleting one vertex or one edge.
    Definitions: [x219_subgraph_critical_for P G] - P fails on G but holds on every one-vertex-
      deleted and every one-edge-deleted subgraph (this file); [choosable G 5] - every assignment
      of lists of at least five colours admits a proper list colouring (GTBase base.v);
      [surface_embeddable 1 G] - G has a rotation system of ORIENTABLE genus at most one, i.e. it
      embeds in the torus (GTBase surface.v: [surface_euler_genus] halves 2 + E - V - F, so its
      value is the orientable genus and the torus is the index one); [connected [set: G]] - G is
      connected (coq-graph-theory sgraph.v), the guard base/theories/surface.v asks the consumers
      of its Euler count to keep; [chi(A)] (coq-graph-theory coloring.v via GTBase);
      [induced] / [del_edges] (coq-graph-theory sgraph.v).
    Notes: FIX 2026-09-23 of the defect the second-reader readback blocked the row on: "drawn on
      the torus" was encoded as [surface_embeddable 2], but [surface_euler_genus] divides
      (2 + E - V - F) by two and so returns the ORIENTABLE GENUS -- the torus is
      [surface_embeddable 1]. The body used to assert the equivalence for every graph of
      orientable genus at most two, the double torus included, which is strictly stronger than
      Conjecture 2 and is not claimed by the source. The hypothesis is now
      [surface_embeddable 1 G] together with [connected [set: G]], the connectivity guard
      base/theories/surface.v asks consumers of its Euler count to keep; on this row the guard is
      harmless anyway (criticality forces connectivity), but it is kept so that every embedding
      row of the wave reads the same way, and grounding_X219.v machine-checks that it is
      satisfiable and that it has teeth. The criticality machinery itself was checked against the
      paper and is faithful. 6-criticality is spelled out as criticality for the property
      "chromatic number at most five": the graph is not 5-colourable while every proper subgraph
      is, which forces the chromatic number to be exactly six. Criticality is stated through the
      two elementary deletions rather than over all proper subgraphs; this is equivalent because
      both properties are preserved when passing to a subgraph, so a counterexample among proper
      subgraphs yields one after a single deletion. Corpus status: open; the source proves the equivalence under an extra cyclic-system-of-triangles hypothesis
      and reports K7 as the only graph critical for 5-list-colouring but not for 5-choosability
      under it.
      V counts every vertex including isolated ones (base fix 2026-09-23): the old count saw
      only the vertices carrying a dart, so the Euler count overstated the genus of every
      graph with an isolated vertex and this hypothesis admitted fewer graphs than intended. *)
Definition toroidal_five_choosability_critical_iff_six_critical_statement : Prop :=
  forall G : sgraph,
    surface_embeddable 1 G ->
    connected [set: G] ->
    (x219_subgraph_critical_for (fun H : sgraph => choosable H 5) G
       <-> x219_subgraph_critical_for (fun H : sgraph => χ([set: H]) <= 5) G).

(** Corpus row: arxiv:2407.18800#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2407.18800__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2407.18800__01.json
    English statement: (Dvorak and Moreno Penarrubia 2024, Conjecture 3, arXiv:2407.18800)
      A finite simple graph that embeds in the torus -- that is, a connected graph of orientable
      genus at most one -- is 5-choosable if and only if its chromatic number is at most five.
    Definitions: [choosable G 5] (GTBase base.v); [surface_embeddable 1 G] - a rotation system of
      ORIENTABLE genus at most one, i.e. an embedding in the torus (GTBase surface.v:
      [surface_euler_genus] halves 2 + E - V - F, so its value is the orientable genus and the
      torus is the index one); [connected [set: G]] - G is connected (coq-graph-theory sgraph.v),
      the guard base/theories/surface.v asks the consumers of its Euler count to keep;
      [chi(A)] (coq-graph-theory coloring.v via GTBase).
    Notes: FIX 2026-09-23 of the two defects the second-reader readback blocked the row on, both
      in the toroidal hypothesis. (1) [surface_euler_genus] divides (2 + E - V - F) by two, so it
      is the ORIENTABLE GENUS and the torus is [surface_embeddable 1]; [surface_embeddable 2] is
      the genus-two surface. (2) The Euler formula is applied to the whole graph with no
      connectivity guard, so padding an arbitrary graph of genus g with g disjoint copies of K_2
      drove the computed value to zero: taking a complete bipartite graph K_{m,m} whose choice
      number exceeds five and padding it that way gives a graph with chromatic number two that is
      not 5-choosable and satisfied the old [surface_embeddable 2] hypothesis, refuting the
      biconditional. The hypothesis is now [surface_embeddable 1 G] together with
      [connected [set: G]], which is the faithful reading of "embeds in the torus" and kills the
      padding refutation (a padded graph is disconnected); grounding_X219.v machine-checks that
      the guard is satisfiable and that it has teeth. Only the "5-colourable implies
      5-choosable" direction is open; the converse is immediate because a constant list assignment
      of five colours reduces choosability to colourability. The biconditional is kept because it
      is the source's wording and the equivalence with Conjecture 2 (the row above) is stated in
      that form. Corpus status: open.
      V counts every vertex including isolated ones (base fix 2026-09-23): the old count saw
      only the vertices carrying a dart, so the Euler count overstated the genus of every
      graph with an isolated vertex and this hypothesis admitted fewer graphs than intended. *)
Definition toroidal_five_choosable_iff_five_colourable_statement : Prop :=
  forall G : sgraph,
    surface_embeddable 1 G ->
    connected [set: G] ->
    (choosable G 5 <-> χ([set: G]) <= 5).

(** Corpus row: arxiv:2407.18800#02
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2407.18800__02/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2407.18800__02.json
    English statement: (Dvorak and Moreno Penarrubia 2024, Conjecture 4, arXiv:2407.18800)
      Every finite simple graph that embeds in the torus -- that is, every connected graph of
      orientable genus at most one -- and in which every cycle has length at least four is
      5-choosable.
    Definitions: [choosable G 5] (GTBase base.v); [surface_embeddable 1 G] - a rotation system of
      ORIENTABLE genus at most one, i.e. an embedding in the torus (GTBase surface.v);
      [connected [set: G]] - G is connected (coq-graph-theory sgraph.v), the guard
      base/theories/surface.v asks the consumers of its Euler count to keep;
      [girth_geq G 4] - every genuine cycle has at least four vertices (GTBase base.v).
    Notes: BLOCKED. The source's hypothesis is EDGE-WIDTH at least four, the length of a shortest
      NON-CONTRACTIBLE cycle of the drawing. GTBase's surface layer (base/theories/surface.v) gives
      rotation systems, faces and Euler genus, but no contractibility or homotopy predicate for
      cycles, so edge-width cannot be defined here. The placeholder above replaces edge-width by
      GIRTH at least four, which is a STRICTLY STRONGER hypothesis (a non-contractible cycle is a
      cycle, so girth at least four implies edge-width at least four, but not conversely: a
      toroidal triangulation can have triangles that are all contractible). The placeholder is
      therefore a WEAKENING of the conjecture and must not be read as the conjecture itself; the
      row's statement leg stays blocked until a contractibility predicate lands in
      base/theories/surface.v. The second-reader readback of 2026-09-23 confirmed this against the
      paper (edge-width is defined there as the length of the shortest non-contractible cycle of
      the drawing) and found a SECOND defect: the toroidal hypothesis [surface_embeddable 2] is
      orientable genus at most two, whereas the torus is [surface_embeddable 1]
      ([surface_euler_genus] halves 2 + E - V - F), and the connectivity guard asked for by
      base/theories/surface.v was missing. That second defect is FIXED (2026-09-23) in the
      placeholder below, which now reads [surface_embeddable 1 G] together with
      [connected [set: G]] exactly as the two repaired rows above; the row nevertheless STAYS
      BLOCKED on the first defect, because girth is not edge-width and no contractibility
      predicate exists in base/theories/surface.v. Corpus status: open; Postle's bound gives the
      statement with four replaced by a sufficiently large constant.
      V counts every vertex including isolated ones (base fix 2026-09-23): the old count saw
      only the vertices carrying a dart, so the Euler count overstated the genus of every
      graph with an isolated vertex and this hypothesis admitted fewer graphs than intended. *)
Definition toroidal_edge_width_four_five_choosable_statement : Prop :=
  forall G : sgraph,
    surface_embeddable 1 G ->
    connected [set: G] ->
    girth_geq G 4 ->
    choosable G 5.

(** Corpus row: arxiv:2004.07457#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2004.07457__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2004.07457__01.json
    English statement: (Alon, Cambie and Kang 2021, Conjecture 7, arXiv:2004.07457)
      Three sufficient conditions each force every bipartite finite simple graph with sides A and B
      of maximum degrees at most DA and DB to be (kA,kB)-choosable, with kA, kB, DA, DB positive.
      (i) For every positive q there is a threshold D0 such that the conclusion holds whenever
      DA and DB are at least D0, the q-th power of kA is at least DA and the q-th power of kB is at
      least DB. (ii) There are a constant C greater than one and a threshold D0 greater than one
      such that the conclusion holds whenever DA and DB are at least D0, kA is at least C times
      the base-two logarithm of DB and kB is at least C times the base-two logarithm of DA. (iii) There are a
      positive constant C and a threshold D0 greater than one such that, when both sides have
      maximum degree at most a common D that is at least D0, the conclusion holds whenever the
      kA-th power of kB is at least C to the power kA times D times the (kA - 1)-st power of the
      base-two logarithm of D, or the symmetric inequality with kA and kB exchanged holds.
    Definitions: [x219_kAkB_choosable G A kA kB] - every list assignment with at least kA colours
      on A and at least kB colours off A admits a proper list colouring (this file);
      [x219_bipartition G A] - every edge has exactly one end in A (this file);
      [x219_max_degree_on G A D] - every vertex of A has at most D neighbours (this file);
      [list_colourable] (GTBase base.v); [trunc_log 2 n] - floor of the base-two logarithm
      (MathComp).
    Notes: The source's real parameters are cleared by rearrangement over the naturals. The real
      epsilon of (i) is the rational 1/q, and "kA >= DA^(1/q)" becomes "DA <= kA^q"; the threshold
      D0 depends on q only, as in the source. In (ii) and (iii) the real constant C becomes a
      natural constant, which is no loss for a lower bound of this shape. In (iii) the source's
      "kB >= C * (D / log D)^(1/kA) * log D" is raised to the power kA and multiplied by log D,
      giving "kB^kA >= C^kA * D * (log D)^(kA - 1)" with no division and no root; the two are
      equivalent for positive kA and positive log D. The base-two logarithm is floored
      ([trunc_log]), which only weakens the hypotheses slightly and never changes their asymptotic
      content. The three conditions are stated as one conjunction, since the source states them as
      three separate sufficient conditions for the same conclusion. FIX 2026-09-23 of the defect
      the second-reader readback blocked the row on: as transcribed, conditions (ii) and (iii)
      carried no lower guard on the maximum degrees, so at DA = DB = 1 both hypotheses
      [C * trunc_log 2 DB <= kA] and [C * trunc_log 2 DA <= kB] read [0 <= kA] and [0 <= kB] for
      every C, and the body then claimed that every bipartite graph of maximum degree one is
      (1,1)-choosable -- REFUTED by a single edge whose two vertices carry the same one-element
      list (the refutation is recorded as grounding_X219.[x219_asym_needs_degree_guard], and the
      curated witness meta/probe_hints/asymmetric_bipartite_list_colouring_statement.v, which
      refuted the old body, must now FAIL to compile). The paper's Conjecture 7 inherits the same
      degenerate corner because its conditions are meant asymptotically: its abstract says the
      conclusion holds "provided Delta_A and Delta_B are large enough", and its own condition (i)
      carries exactly such a threshold. MODELLING CHOICE: conditions (ii) and (iii) now carry the
      same kind of threshold, an EXISTENTIAL D0 with the guards [D0 <= DA], [D0 <= DB] (resp.
      [D0 <= D]), quantified together with the constant C. Requiring [1 < D0] is logically free --
      the conditions are antitone in D0, so any admissible threshold can be raised to two -- and
      it records the corner that must be excluded: [trunc_log 2 1 = 0] kills the lower bound on
      the list sizes, whereas from D >= 2 on [trunc_log 2 D >= 1] and the conditions have teeth.
      This is a strictly weaker reading than the paper's literal (ii) and (iii), which state no
      threshold; it is the asymptotic content those conditions are meant to carry, and nothing
      smaller repairs the row. The three rearrangements above were re-derived by the readback and
      are correct. Corpus status: open; the source proves the three cases for complete bipartite
      graphs. *)
Definition asymmetric_bipartite_list_colouring_statement : Prop :=
  (* (i) *)
  (forall q : nat, 0 < q ->
     exists D0 : nat,
       forall (G : sgraph) (A : {set G}) (DA DB kA kB : nat),
         x219_bipartition A ->
         x219_max_degree_on A DA ->
         x219_max_degree_on (~: A) DB ->
         0 < kA -> 0 < kB -> D0 <= DA -> D0 <= DB ->
         DA <= kA ^ q -> DB <= kB ^ q ->
         x219_kAkB_choosable A kA kB)
  /\
  (* (ii) *)
  (exists C D0 : nat, [/\ 1 < C, 1 < D0 &
     forall (G : sgraph) (A : {set G}) (DA DB kA kB : nat),
       x219_bipartition A ->
       x219_max_degree_on A DA ->
       x219_max_degree_on (~: A) DB ->
       0 < kA -> 0 < kB -> D0 <= DA -> D0 <= DB ->
       C * trunc_log 2 DB <= kA -> C * trunc_log 2 DA <= kB ->
       x219_kAkB_choosable A kA kB])
  /\
  (* (iii) *)
  (exists C D0 : nat, [/\ 0 < C, 1 < D0 &
     forall (G : sgraph) (A : {set G}) (D kA kB : nat),
       x219_bipartition A ->
       x219_max_degree_on A D ->
       x219_max_degree_on (~: A) D ->
       0 < kA -> 0 < kB -> D0 <= D ->
       (C ^ kA * D * trunc_log 2 D ^ kA.-1 <= kB ^ kA \/
        C ^ kB * D * trunc_log 2 D ^ kB.-1 <= kA ^ kB) ->
       x219_kAkB_choosable A kA kB]).

(** Corpus row: arxiv:1902.07018#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1902.07018__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1902.07018__00.json
    English statement: (Alon, Bucic, Kalvari, Kuperwasser and Szabo 2019, open question on the list Ramsey number of a path with two edges, arXiv:1902.07018)
      For every positive even number n, the complete graph on n vertices is (n-1)-edge-choosable:
      every symmetric assignment of lists of at least n-1 colours to its edges admits a proper edge
      colouring picking each edge's colour from its own list.
    Definitions: [x219_edge_choosable G k] - every symmetric list assignment with at least k
      colours per edge admits a proper edge colouring from the lists, where proper means two
      distinct edges sharing an endpoint get distinct colours (this file); ['K_n] - the complete
      graph on n vertices (coq-graph-theory sgraph.v via GTBase).
    Notes: The row records that the value of the list Ramsey number R_l(K_{1,2}, k) for ODD k is
      not known to be k+1 or k+2. The record's own context states that this case is EQUIVALENT to
      the List Colouring Conjecture for cliques of EVEN order, that is, to the equality between
      the list chromatic index and the chromatic index of K_n for even n. The Rocq body is that
      determinate form. Only the upper bound is stated: the chromatic index of K_n is n-1 for even
      n and the list chromatic index is always at least the chromatic index, so "(n-1)-edge-
      choosable" is exactly the open half of the equality. Corpus status: open; the even-k case is
      settled by Haggkvist and Janssen's theorem on cliques of odd order. *)
Definition list_chromatic_index_even_clique_statement : Prop :=
  forall n : nat,
    0 < n ->
    ~~ odd n ->
    x219_edge_choosable 'K_n n.-1.

(** Corpus row: arxiv:2009.12189#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2009.12189__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2009.12189__00.json
    English statement: (Bonamy, Kardos, Kelly and Postle 2020, Conjecture 1.1, arXiv:2009.12189)
      Every planar finite simple graph has fractional vertex-arboricity at most two: for some
      positive b there are 2*b vertex sets, each inducing a forest, such that every vertex lies in
      at least b of them.
    Definitions: [x219_frac_vertex_arboricity_le_two G] - the displayed b-fold covering property,
      with the fold parameter b EXISTENTIALLY quantified (this file); [is_forest S] - the subgraph
      induced on S is a forest (coq-graph-theory sgraph.v via GTBase); [wagner_planar G] - G has
      neither K5 nor K3,3 as a minor, which by Wagner's theorem is planarity (GTBase base.v).
    Notes: FIX 2026-09-23 of the defect the second-reader readback blocked the row on: the b-fold
      form used the WRONG QUANTIFIER ("for every b") and the body was false. The set of b
      admitting a 2b-family that covers every vertex b times is closed under addition (take the
      union of two families), so "for every b" is equivalent to its instance b = 1, which says
      that the vertex set splits into TWO induced forests, i.e. that the INTEGRAL
      vertex-arboricity is at most two -- and the source paper itself states that "there exist
      planar graphs with vertex-arboricity three". The fold parameter is now EXISTENTIAL, in the
      shape X130's [x130_frac_chi_le] already uses for the fractional chromatic number: there
      EXISTS b >= 1 and 2*b induced forests covering every vertex at least b times (the covering
      LP has rational data, so its optimum is attained, which is what makes the existential form
      equivalent to the real inequality va_f(G) <= 2). The [0 < b] guard is load bearing and has
      teeth: without it b = 0 satisfies the body for every graph whatsoever
      (grounding_X219.[x219_frac_va_b0_vacuous]). The fractional vertex-arboricity is the least
      ratio a/b for which a induced forests cover every vertex b times. Planarity
      is the minor-theoretic (Wagner) predicate of GTBase, not a fixed embedding. Corpus status:
      open; the statement implies both the Albertson-Berman conjecture on large induced forests and
      a fractional chromatic number of at most four for planar graphs. *)
Definition planar_fractional_vertex_arboricity_two_statement : Prop :=
  forall G : sgraph,
    wagner_planar G ->
    x219_frac_vertex_arboricity_le_two G.

(** Corpus row: arxiv:1709.04036#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1709.04036__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1709.04036__01.json
    English statement: (Dvorak and Kelly 2018, remark after Theorem 1.2, arXiv:1709.04036)
      Every triangle-free planar finite simple graph has a vertex set S with 6*|S| at least
      5*|V(G)|, that is at least five sixths of its vertices, whose induced subgraph is
      2-degenerate.
    Definitions: [k_degenerate H 2] - every nonempty vertex subset of H has a vertex with at most
      two neighbours inside it (GTBase base.v); [triangle_free] and [wagner_planar] (GTBase
      base.v); [induced S] (coq-graph-theory sgraph.v).
    Notes: The row records the authors' belief that their argument can be pushed from the proved
      4/5 bound to 5/6; the self-contained mathematical content is exactly the 5/6 weakening of
      their Conjecture 1.1, which asks for 7/8 and is encoded in X32.v as
      [triangle_free_planar_large_induced_two_degenerate_statement]. The fraction is
      cross-multiplied to avoid natural division. Corpus status: open. *)
Definition triangle_free_planar_five_sixths_two_degenerate_statement : Prop :=
  forall G : sgraph,
    wagner_planar G ->
    triangle_free G ->
    exists S : {set G},
      (6 * #|S| >= 5 * #|G|)%N /\
      k_degenerate (induced S) 2.

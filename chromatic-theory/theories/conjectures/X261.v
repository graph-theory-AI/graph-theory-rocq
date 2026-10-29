(** * Chromatic.conjectures.X261 -- wave X261: cochromatic, choice and acyclic chromatic numbers, and clique
    subdivisions (2026-10-29)

    A five-row wave under the prospective contract of meta/faithfulness_policy.json.  Rows: erdos:625 (chi(G) -
    zeta(G) -> oo almost surely for G(n,1/2)), erdos:717 (chi(G) << n^(1/2) / log n * sigma(G)), erdos:760 (a
    subgraph with cochromatic number >> m / log m), erdos:797 (the acyclic chromatic number of a graph of maximum
    degree d is o(d^2)) and erdos:799 (the choice number of almost all graphs on n vertices is o(n)).  Shared
    vocabulary is reused: the chromatic number chi([set: G]) of coq-graph-theory, upstream [cliqueb] and [stable],
    GTBase's [choosable] (any finite palette), [has_subgraph] (not induced), [Delta], [eventually], the G(n,1/2)
    weights [fg_gnp_weight] with [fg_whp] (GTBase.finite_graph), and MathComp's [trunc_log].  Local notions:
    cochromatic colourings as a Boolean (Chromatic.conjectures.XE2's [xe2_cochromatic_colouring] is the same notion as
    a Prop; grounding_X261 proves the reflection), the cochromatic number, clique subdivisions and their largest
    order, acyclic colourings (Chromatic.conjectures.U4's [acyclic_colouring] with whole-palette lists is the same
    notion, proved in grounding_X261), and choosability with lists drawn from a fixed finite palette (grounding_X261
    proves it equivalent to GTBase's [choosable]).  Pinned statuses: 625 open, 717, 760, 797 and 799 solved;
    literature lines are dated against the corpus pin (graph-conjectures b72c5857, 2026-09-23).  The sources are the
    Mac's deposit coordination/sources/x261-source-mac-20261029 (text line numbers below).  The grounding certificates
    are in grounding_X261.v. *)

From GTBase Require Import base common finite_graph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x261 vocabulary ************************************************* *)

(** G has a cochromatic colouring with k colours: every colour class induces a complete graph (upstream [cliqueb]) or
    an empty graph (upstream [stable]).  Empty classes are allowed, so this is "at most k colours".  It is a Boolean
    (a finite quantifier over [{ffun G -> 'I_k}]), so that it can describe an event of G(n,1/2). *)
Definition x261_cochromatic_at_most (G : sgraph) (k : nat) : bool :=
  [exists col : {ffun G -> 'I_k},
    [forall i : 'I_k, let S := [set v : G | col v == i] in cliqueb S || stable S]].

(** z = zeta(G), the cochromatic number: a cochromatic colouring with z colours exists and none with fewer. *)
Definition x261_cochromatic_exact (G : sgraph) (z : nat) : bool :=
  x261_cochromatic_at_most G z && [forall j : 'I_z, ~~ x261_cochromatic_at_most G j].

(** G contains a subdivision of K_k: k distinct branch vertices [b i] and, for every pair i < j, a path from [b i] to
    [b j] whose sequence [b i :: rcons (p i j) (b j)] follows edges of G and repeats no vertex; every interior
    [p i j] avoids all branch vertices, and two interiors meet only for the same pair (internally vertex-disjoint
    paths replacing the edges of K_k). *)
Definition x261_topological_clique (G : sgraph) (k : nat) : Prop :=
  exists (b : 'I_k -> G) (p : 'I_k -> 'I_k -> seq G),
    [/\ injective b,
        forall i j : 'I_k, i < j ->
          path (--) (b i) (rcons (p i j) (b j)) && uniq (b i :: rcons (p i j) (b j)),
        forall (i j l : 'I_k) (x : G), i < j -> x \in p i j -> x != b l
      & forall (i j i' j' : 'I_k) (x : G), i < j -> i' < j' ->
          x \in p i j -> x \in p i' j' -> i = i' /\ j = j'].

(** s = sigma(G): G contains a subdivision of K_s and of no larger clique. *)
Definition x261_clique_subdivision_order (G : sgraph) (s : nat) : Prop :=
  x261_topological_clique G s /\ forall t : nat, x261_topological_clique G t -> t <= s.

(** G has an acyclic colouring with k colours: a proper colouring into ['I_k] in which every cycle (a [ucycle] of
    length at least 3) uses at least three colours, so that no cycle lies in the subgraph induced by two colour
    classes. *)
Definition x261_acyclic_colourable (G : sgraph) (k : nat) : Prop :=
  exists f : G -> 'I_k,
    (forall x y : G, x -- y -> f x != f y) /\
    forall c : seq G, ucycle (--) c -> 2 < size c -> 2 < size (undup [seq f x | x <- c]).

(** G is k-choosable with every list drawn from the palette ['I_(#|G| * k)]: for every assignment of lists of at least
    k colours of that palette, some proper colouring picks each vertex's colour from its list.  It is a Boolean;
    grounding_X261 proves it equivalent to GTBase's [choosable G k], where the palette is any finite type. *)
Definition x261_choosable_b (G : sgraph) (k : nat) : bool :=
  [forall L : {ffun G -> {set 'I_(#|G| * k)}},
    [forall v, k <= #|L v|] ==>
    [exists f : {ffun G -> 'I_(#|G| * k)},
      [forall v, f v \in L v] && [forall x, [forall y, x -- y ==> (f x != f y)]]]].

(** ** X261 statements ******************************************************* *)

(** Corpus row: erdos:625
    Site: none
    Review: none
    English statement: (Erdos Problems #625, Erdos and Gimbel)
      The cochromatic number zeta(G) is the minimum number of colours needed to colour the vertices of G such that
      each colour class induces either a complete graph or an empty graph.  If G is a random graph with n vertices
      and each edge included independently with probability 1/2, is it true that almost surely chi(G) - zeta(G) ->
      oo as n -> oo?
    Definitions: [x261_cochromatic_exact G z] - z = zeta(G) (this file); [x261_cochromatic_at_most G k] - a
      cochromatic colouring with k colours (this file); [fg_labelled_sgraph E] - the graph on ['I_n] with edge set E,
      [fg_gnp_weight 1 2 n] - the G(n,1/2) weight (every labelled graph on n vertices has weight 1), [fg_whp] -
      the probability tends to 1 (GTBase base/theories/finite_graph.v); chi([set: G]) - the chromatic number
      (coq-graph-theory).
    Notes: "almost surely chi - zeta -> oo" is read as convergence in probability: for every M, with probability
      tending to 1, zeta(G) + M <= chi(G).  This is the sources' reading: Heckel (arXiv:2408.13839v2, source.tex
      l.231; arXiv:2409.17614v2, source.tex l.257) restates the question as "is there a function f(n) -> oo such
      that, with high probability, chi(G) - zeta(G) >= f(n)", whp meaning probability -> 1 (2409.17614v2 l.251), and
      Steiner (arXiv:2408.02400v2, main.tex l.113-115) keeps the page's "almost surely" for G_n ~ G(n,1/2); the
      M-form is equivalent to the f-form (from the M-form, let f grow past M once the probability of zeta + M <= chi
      exceeds 1 - 1/M for every larger n).  The event quantifies z over ['I_n.+1]: zeta(G) <= n always (one colour
      per vertex, grounding_X261's g261_cochromatic_card), so the bound loses nothing.  Each colour class INDUCES a
      complete or an empty graph, as on the page (erdos-625-latex.txt l.25).  Literature status: open at the pin
      (pinned status open, $1000).  Published partial results: Heckel (2408.13839v2) and, independently, Steiner
      (2408.02400v2) show chi - zeta is not whp bounded, and any whp bound f(n) has f(n) >= n^(1/2 - o(1)) along an
      infinite sequence; Heckel (2409.17614v2, Theorem 1) gives chi - zeta >= n^(1 - eps) for roughly 95% of all n,
      not for all n.  The current page links a manuscript of Petkov (the deposit's 625-claim.pdf, commit b3fdc4d3,
      10 September 2026, before the pin) claiming chi - zeta >> n / (log n)^3 almost surely along all n; it is cited
      as a claim, not verified, and changes no status. *)
Definition random_graph_chi_minus_cochromatic_unbounded_statement : Prop :=
  forall M : nat,
    @fg_whp (fun n : nat => {set {set 'I_n}}) (fun n => @fg_gnp_weight 1 2 n)
      (fun n E => let G := fg_labelled_sgraph E in
         [forall z : 'I_n.+1, x261_cochromatic_exact G z ==> (z + M <= χ([set: G]))]).

(** Corpus row: erdos:717
    Site: none
    Review: none
    English statement: (Erdos Problems #717, Erdos and Fajtlowicz)
      Let G be a graph on n vertices with chromatic number chi(G) and let sigma(G) be the maximal k such that G
      contains a subdivision of K_k.  Is it true that chi(G) << n^(1/2) / log n * sigma(G)?
    Definitions: [x261_clique_subdivision_order G s] - s = sigma(G) (this file); [x261_topological_clique G k] - G
      contains a subdivision of K_k (this file); chi([set: G]) - the chromatic number (coq-graph-theory);
      [trunc_log 2 n] - the floor of log2 n (MathComp).
    Notes: "<<" is an absolute constant C, and the root is removed by squaring: (chi(G) * trunc_log 2 n)^2 <= C n
      sigma(G)^2 for every graph G on n vertices.  The base of the logarithm and its floor are absorbed by C (log2 n /
      2 <= trunc_log 2 n <= log2 n for n >= 2), and so is the range: for n <= 1 trunc_log 2 n = 0 and both sides are
      trivial, and for n >= 2 the right side is positive (sigma(G) >= 1), so enlarging C covers any finite set of
      small graphs.  A subdivision of K_k replaces the edges of K_k by internally vertex-disjoint paths (Fox, Lee and
      Sudakov, arXiv:1107.1920v3, source.tex l.92-95, which also defines sigma(G)); the paths may be single edges.
      Literature status: proved before the pin (pinned status solved, "PROVED ... in the affirmative"; the page,
      erdos-717-latex.txt).  Fox, Lee and Sudakov, Chromatic number, clique subdivisions, and the conjectures of Hajos
      and Erdos-Fajtlowicz (arXiv:1107.1920v3, 14 February 2012), Theorem 1.1 (source.tex l.130-132): there is an
      absolute constant C with chi(G) / sigma(G) <= C n^(1/2) / log n for every n-vertex graph G, n >= 2 (H(n), the
      maximum of chi(G) / sigma(G), l.72-78); the encoded clause follows by squaring.  Erdos and Fajtlowicz (ErFa81,
      in the deposit) showed the matching lower bound for almost all graphs. *)
Definition chi_clique_subdivision_root_log_statement : Prop :=
  exists C : nat, forall (G : sgraph) (s : nat), x261_clique_subdivision_order G s ->
    (χ([set: G]) * trunc_log 2 #|G|) ^ 2 <= C * #|G| * s ^ 2.

(** Corpus row: erdos:760
    Site: none
    Review: none
    English statement: (Erdos Problems #760, Erdos and Gimbel)
      The cochromatic number zeta(G) is the minimum number of colours needed to colour the vertices of G such that
      each colour class induces either a complete graph or independent set.  If G is a graph with chromatic number
      chi(G) = m then must G contain a subgraph H with zeta(H) >> m / log m?
    Definitions: [x261_cochromatic_at_most H k] - a cochromatic colouring of H with k colours (this file);
      [has_subgraph G H] - H is a subgraph of G, not necessarily induced (GTBase common.v); chi([set: G]) - the
      chromatic number (coq-graph-theory); [trunc_log 2 m] - the floor of log2 m (MathComp).
    Notes: ">>" is an absolute constant C: every cochromatic colouring of H with k colours has m <= C k trunc_log 2 m,
      that is zeta(H) >= m / (C trunc_log 2 m).  The guard 2 <= m is load-bearing: at m = 1, log 1 = 0 and the
      bound would ask m <= 0 (grounding_X261's not_trivially_true certificate deletes it).  The source proves the
      bound for large m ("Throughout, we assume that n is sufficiently large", AKS97.txt l.56); the small cases are
      absorbed by C, since H = G has zeta(H) >= 1 and trunc_log 2 m >= 1 for m >= 2.  The subgraph is NOT
      necessarily induced, and the induced reading would be false: every induced subgraph of K_m is complete, so its
      cochromatic number is 1 (the page: "best possible, as shown by taking G to be a complete graph",
      erdos-760-latex.txt l.27); AKS97's complete-graph case passes to an m-vertex subgraph with no large clique or
      independent set (AKS97.txt l.58-60).  Literature status: proved before the pin (pinned status solved, "PROVED
      (LEAN)").  Alon, Krivelevich and Sudakov, Subgraphs with a large cochromatic number, J. Graph Theory 25 (1997)
      295-297 (author manuscript AKS97.pdf), Theorem 1.1 (AKS97.txt l.29-30): a graph with chromatic number m
      contains a subgraph with cochromatic number at least (1/4 + o(1)) m / log2 m; the encoded clause follows with
      C absorbing the o(1), the floor and the small m.  The page's Lean link (formal-conjectures 760.lean, commit
      6fbb54f2) states the problem with sorry; the linked proof (plby/lean-proofs Erdos760.lean, commit f2462b28,
      Lean / mathlib 4.29.1) states erdos_760 with C = 32, m >= 2, an edge-preserving subgraph on a vertex subset and
      floor(log2 m), the shape encoded here; it is cited as an external proof, not as kernel evidence (no Lean run
      here). *)
Definition subgraph_large_cochromatic_number_statement : Prop :=
  exists C : nat, forall (G : sgraph) (m : nat), χ([set: G]) = m -> 2 <= m ->
    exists H : sgraph, has_subgraph G H /\
      forall k : nat, x261_cochromatic_at_most H k -> m <= C * k * trunc_log 2 m.

(** Corpus row: erdos:797
    Site: none
    Review: none
    English statement: (Erdos Problems #797, Erdos)
      Let f(d) be the maximal acyclic chromatic number of any graph with maximum degree d - that is, the vertices of
      any graph with maximum degree d can be coloured with f(d) colours such that there is no edge between vertices
      of the same colour and no cycle containing only two colours.  Estimate f(d).  In particular is it true that
      f(d) = o(d^2)?
    Definitions: [x261_acyclic_colourable G k] - an acyclic colouring of G with k colours (this file); [Delta G] -
      the maximum degree (GTBase base.v); [eventually P] - P holds for all sufficiently large d (GTBase
      asymptotics.v).
    Notes: the precise clause f(d) = o(d^2) is encoded: for every q >= 1, eventually in d, every graph with maximum
      degree d has an acyclic colouring with k colours and q k <= d^2.  "Estimate f(d)" is not formalised, as
      erdos:1013's "find an asymptotic" was not.  The maximum degree is exactly d, as in Alon, McDiarmid and Reed's
      A(d) = max{A(G) : Delta(G) = d} (AMR91 p.278, AMR91-page2.png); "at most d" (Erdos's 1980 discussion,
      Er80-acyclic.pdf) is equivalent, since adding a disjoint star K_(1,d) raises the maximum degree to d and an
      acyclic colouring restricts to subgraphs.  "No cycle containing only two colours" is "every cycle uses at least
      three colours"; AMR91 p.277 says the same as "no cycle in the subgraph induced by the vertices of any two of the
      colors" (AMR91.txt l.32-35), and a proper colouring has no one-coloured edge.  Literature status: proved before
      the pin (pinned status solved, "PROVED ... in the affirmative").  Alon, McDiarmid and Reed, Acyclic coloring of
      graphs, Random Structures and Algorithms 2 (1991) 277-288 (author scan AMR91.pdf), Theorem 1.1 (p.278): A(d) =
      O(d^(4/3)); Proposition 2.2 (AMR91.txt l.131-132): A(G) <= ceil(50 d^(4/3)) for every graph of maximum degree d.
      The encoded clause follows: q ceil(50 d^(4/3)) <= d^2 once d is large. *)
Definition acyclic_chromatic_max_degree_subquadratic_statement : Prop :=
  forall q : nat, 0 < q -> eventually (fun d : nat =>
    forall G : sgraph, Delta G = d -> exists k : nat, x261_acyclic_colourable G k /\ q * k <= d ^ 2).

(** Corpus row: erdos:799
    Site: none
    Review: none
    English statement: (Erdos Problems #799, Erdos, Rubin and Taylor)
      The list chromatic number chi_L(G) is the minimal k such that for any assignment of a list of k colours to each
      vertex of G (perhaps different lists for different vertices) a colouring of each vertex by a colour on its list
      can be chosen such that adjacent vertices receive distinct colours.  Is it true that chi_L(G) = o(n) for almost
      all graphs on n vertices?
    Definitions: [x261_choosable_b G k] - G is k-choosable with lists from the palette ['I_(#|G| * k)] (this file),
      equivalent to GTBase's [choosable G k] (grounding_X261's g261_choosable_bP and g261_choosable_b_choosable);
      [fg_labelled_sgraph E], [fg_gnp_weight 1 2 n] and [fg_whp] (GTBase finite_graph.v).
    Notes: "almost all graphs on n vertices" is the uniform measure on the labelled graphs on ['I_n], which is
      G(n,1/2): fg_gnp_weight 1 2 gives every labelled graph weight 1.  "chi_L(G) = o(n) for almost all graphs" is
      encoded as: for every q >= 1, with probability tending to 1, chi_L(G) <= n %/ q.  This is equivalent to the
      existence of one f(n) = o(n) with chi_L(G) <= f(n) for almost all graphs (from the q-form, take f(n) = n %/ q on
      the block of n where the q-th bound already holds with probability at least 1 - 1/q).  Lists of at least k
      colours (GTBase's [choosable]) and of exactly k colours (Al92.txt l.32-36) give the same notion (a longer list
      can be shortened).  Literature status: proved before the pin (pinned status solved, "PROVED ... in the
      affirmative").  Alon, Choice numbers of graphs; a probabilistic approach, Combinatorics, Probability and
      Computing 1 (1992) (author manuscript Al92.pdf), Corollary 1.3 (Al92.txt l.66-67): for some c > 0, the
      probability that ch(G_(n,1/2)) <= c n log log n / log n tends to 1; l.69-70: "for almost all the graphs G on n
      vertices, ch(G) = o(n) ... This solves a problem raised in [7]" (Erdos, Rubin and Taylor, ERT80).  The encoded
      clause follows, as c n log log n / log n <= n %/ q once n is large.  Alon, Krivelevich and Sudakov (AKS99, in
      the deposit) later sharpened the order to n / log n. *)
Definition almost_all_graphs_choice_number_sublinear_statement : Prop :=
  forall q : nat, 0 < q ->
    @fg_whp (fun n : nat => {set {set 'I_n}}) (fun n => @fg_gnp_weight 1 2 n)
      (fun n E => x261_choosable_b (fg_labelled_sgraph E) (n %/ q)).

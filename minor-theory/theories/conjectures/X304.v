(** * Minor.conjectures.X304 -- v2 row: Wood's conjecture on the number of cliques in K_t-minor-free graphs,
      the maximum is 2^(t-2)(n-t+3) if and only if t <= 49 (record arXiv:1603.07056) *)

From GTBase Require Import base clique_counts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X304 statement ******************************************************)

(** Reused vocabulary: GTBase.base [minor] (coq-graph-theory's minors) and the complete graphs 'K_n; and
    GTBase.clique_counts [all_clique_count] (the clique-count family's canonical: every clique, the empty one
    included).  X304 declares no helper of its own. *)

(** Corpus row: studies:std_wood_s_conjecture_on_the_maximum_number_of_cliqu
    Site: none
    Review: none
    English statement: (Wood; studies slice of the corpus, record arXiv:1603.07056)
      The maximum number of cliques a K_t-minor free graph on n vertices can have is 2^(t-2)(n-t+3) if and only
      if t <= 49.
    Definitions: [all_clique_count G] - the number of sets of pairwise adjacent vertices of G, the empty set
      included (GTBase.clique_counts); [minor G H] - H is a minor of G: a map from the vertices of G onto those
      of H (or to nothing) whose fibres are connected, with an edge of G between the fibres of x and y whenever
      x and y are adjacent in H (coq-graph-theory), so [~ minor G 'K_t] says that G is K_t-minor-free; 'K_t -
      the complete graph on t vertices.
    Notes: encoded as stated, with the sources' definitions.  The conjecture is Wood's (arXiv:1511.04655v2,
      CliquesMinors.tex l.532-534, Conjecture 17: "$\cliques(n,t)=2^{t-2}(n-t+3)$ if and only if $t\leq 49$",
      where cliques(n,t) is the maximum number of cliques of a K_t-minor-free graph on n vertices, l.112-113),
      and the record (Fox and Wei, arXiv:1603.07056v1, arxiv.tex l.77) states it in the pinned words; the
      record's concluding remarks (l.749) print "t >= 49", against l.77 and Wood.  A clique is a set of
      pairwise adjacent vertices and cliques(G,0) = 1 (Wood l.96, l.102), so the empty clique counts, and K_n
      has 2^n cliques (l.114-117).  Wood proves the equality for t in {3, ..., 9} and n >= t - 2 (Theorem 3,
      l.168-170); the (t-2)-trees attain the bound for every t and n >= t - 2 (l.127-133); for t >= 50 a
      complete multipartite graph K_(c x 2), K_(1, c x 2) or K_(1,1, c x 2) beats it (l.530), so the open part
      is the "if" half for 10 <= t <= 49.  The maximum is split into an upper bound for every K_t-minor-free
      graph on n vertices and one such graph attaining it (no maximum operator), for every n >= t - 2, the range
      of Wood's results (l.127-133, l.169), which the displayed conjecture leaves implicit.  t >= 2: at t = 1
      the power 2^(t-2) is not a natural number (and no graph with a vertex is K_1-minor-free); at t = 2 the
      left side holds (a K_2-minor-free graph has no edge, so n + 1 cliques).  The bound is written with the
      natural subtraction last, n + 3 - t, which equals n - t + 3 for every n >= t - 2 (the guard t - 2 <= n),
      so no truncation enters the bound; t - 2 is exact for t >= 2. *)
Definition wood_kt_minor_clique_count_statement : Prop :=
  forall t : nat, 2 <= t ->
    ((forall n : nat, t - 2 <= n ->
        (forall G : sgraph, #|G| = n -> ~ minor G 'K_t ->
           all_clique_count G <= 2 ^ (t - 2) * (n + 3 - t)) /\
        (exists G : sgraph,
           [/\ #|G| = n, ~ minor G 'K_t & all_clique_count G = 2 ^ (t - 2) * (n + 3 - t)])) <->
     t <= 49).

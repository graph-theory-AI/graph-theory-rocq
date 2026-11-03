(** * GTMisc.conjectures.X283 -- v2 rows: Sivaraman's cop-number conjecture for P_t-free graphs, strongly-separating
    path systems of size 2n, pivot Gray codes of spanning trees *)

From GTBase Require Import base induced_paths walks_paths finite_graph spanning_trees.
From GTMisc.foundations Require Import cops.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X283 statements *****************************************************)

(** Corpus row: studies:std_sivaraman_s_conjecture_cop_number_of_p_t_free_gr
    Site: none
    Review: none
    English statement: (Sivaraman; studies slice of the corpus, record arXiv:2301.13175)
      Two cops can win on connected P_5-free graphs; more generally, the cop number of connected P_t-free graphs is
      at most t - 3 for t >= 5.
    Definitions: [has_induced_path_of_order G t] - some nonempty induced path of G (distinct vertices, consecutive
      ones adjacent, no other adjacency among them) has exactly t vertices, i.e. G contains P_t, the path on t
      vertices, as an induced subgraph (GTBase induced_paths); P_t-free is its negation; [cop_number_le G k] - some
      j <= k such that j cops win on G, i.e. c(G) <= k (GTMisc foundations/cops.v); [cops_win G j] - the j cops
      capture after finitely many rounds (same file): the cops are placed first (several may share a vertex), then
      the robber; the cops move first; in each move every piece stays or slides along an edge; a cop landing on the
      robber captures him; [connected [set: G]] - G is connected (coq-graph-theory).
    Notes: encoded as stated.  Source: Sivaraman, "An application of the Gyarfas path argument", arXiv:1903.01338v1
      (4 March 2019, its only version), source.tex l.114-116 (printed Conjecture 0.1: a connected P_t-free graph,
      t >= 5, t - 3 cops can capture the robber), l.98 (the game as above; c(G) is the minimum number of cops with
      a winning strategy), l.101 (finite simple graphs; H-free: no induced H; P_t has t vertices).  "t - 3 cops can
      capture" is read as c(G) <= t - 3, the record's wording; the two agree since an extra cop can shadow another,
      and the encoding needs no such monotonicity.  OPEN at the pin for t >= 6: Chudnovsky, Norin, Seymour and
      Turcotte, "Cops and robbers on P_5-free graphs", arXiv:2301.13175v1 (30 January 2023), paper.tex l.117-119
      (Theorem 1.1: every connected P_5-free graph has c(G) <= 2) settle t = 5 only (l.109, l.115); the proved
      general bound is t - 2 for t >= 3 (Joret, Kaminski and Theis; Sivaraman l.104-106, printed Theorem 0.1).
      The empty graph is connected and needs no cop (it has no robber start).  The bound fails at t = 4: C_4 is
      P_4-free and needs two cops.  The guard 5 <= t also keeps t - 3 from truncating. *)
Definition sivaraman_cop_number_pt_free_statement : Prop :=
  forall t : nat, 5 <= t ->
    forall G : sgraph, connected [set: G] ->
      ~ has_induced_path_of_order G t -> cop_number_le G (t - 3).

(** Corpus row: arxiv:2301.08707#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2301.08707__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2301.08707__00.json
    English statement: (Bonamy, Botler, Dross, Naia and Skokan, arXiv:2301.08707, Problem 3)
      Does every graph on n vertices admit a strongly-separating path system of size 2n?
    Definitions: [seq_simple_path p] - p is a nonempty sequence of distinct vertices, consecutive ones adjacent: a
      path of G (GTBase walks_paths); [seq_edge_set p] - the edges {p_i, p_(i+1)} of the consecutive entries of p,
      the edges of that path (same file); [E(G)] - the edge set of G, the sets {x, y} with x -- y
      (coq-graph-theory).  A collection P of paths of G is strongly separating if for any two distinct edges e and
      f there are paths P_e and P_f in P with e in P_e, f not in P_e, f in P_f and e not in P_f
      (separating_paths_aic_template.tex l.147); its size is the number of paths (l.149).
    Notes: encoded as the affirmative answer, n = #|G|, the paths listed in a sequence P of length at most 2n.  The
      quantifier over ordered pairs (e, f) of distinct edges gives P_e from (e, f) and P_f from (f, e), so it is
      exactly strong separation.  "Size 2n" is an upper bound: repeated paths and paths without an edge separate
      nothing, and a sequence can repeat a path to reach length 2n when G has a vertex; asking for exactly 2n
      distinct paths would fail for small graphs (K_1 has one path).  A one-vertex path is allowed and separates
      nothing.  Source: arXiv:2301.08707v3 (10 October 2023, the last version before the pin), l.185-187 (printed
      Problem 3); the paper proves size 19n (Theorem 2, l.170-172) and quotes the lower bound 2(1 - 2 eps)n for
      K_(eps n, (1 - eps)n) (l.181-183).  Simple graphs, the source's setting.  OPEN at the pin. *)
Definition strongly_separating_path_system_2n_statement : Prop :=
  forall G : sgraph, exists P : seq (seq G),
    [/\ size P <= 2 * #|G|,
        forall p : seq G, p \in P -> seq_simple_path p
      & forall e f : {set G}, e \in E(G) -> f \in E(G) -> e != f ->
          exists2 p : seq G, p \in P & (e \in seq_edge_set p) && (f \notin seq_edge_set p)].

(** Corpus row: arxiv:2603.28614#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2603.28614__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2603.28614__00.json
    English statement: (Bonamy, Hoffmann, Legrand-Duchesne and Rote, arXiv:2603.28614, Problem 1)
      Does every graph G admit a pivot Gray code on its spanning trees?
    Definitions: [fg_spanning_tree T] - T is a set of edges of G whose graph on all the vertices of G is a tree
      (GTBase spanning_trees, imported explicitly).  A pivot Gray code on the spanning trees lists each of them
      exactly once, each obtained from the previous one by removing an edge and adding another, the two sharing an
      endpoint (main.tex l.97-101, the edge exchange; l.114-117, the strong revolving door property).
    Notes: encoded as the affirmative answer: a duplicate-free sequence s whose members are exactly the spanning
      trees of G, with T_(i+1) = (T_i \ {e}) + {f} for consecutive members, e in T_i, f not in T_i and
      e :&: f != set0 (two distinct edges meeting in one vertex).  f is an edge of G, as T_(i+1) is a spanning tree.
      A Gray code is "a linear or cyclic order" (l.86): a linear listing answers the question (a Hamiltonian path of
      the flip graph, l.91-92), and a cyclic one would strengthen the row (grounding_X283 refutes the cyclic variant
      at K_1).  A disconnected graph has no spanning tree and is listed by the empty sequence; the empty graph and
      K_1 have exactly one, the empty edge set (GTBase spanning_trees, l.15-16).  Simple graphs, the corpus's
      graphs; the paper's own results are about arborescences of directed graphs (Knuth's question, l.139-149), a
      different statement.  Source: arXiv:2603.28614v1 (30 March 2026, its only version before the pin),
      l.119-122 (printed Problem 1).  OPEN at the pin (l.125-127); constructions exist for fan graphs and
      outerplanar graphs (l.134-137). *)
Definition pivot_gray_code_spanning_trees_statement : Prop :=
  forall G : sgraph, exists s : seq {set {set G}},
    [/\ uniq s,
        forall T : {set {set G}}, T \in s <-> fg_spanning_tree T
      & forall i : nat, i.+1 < size s ->
          exists e f : {set G},
            [/\ e \in nth set0 s i, f \notin nth set0 s i,
                nth set0 s i.+1 = (nth set0 s i :\ e) :|: [set f] & e :&: f != set0]].

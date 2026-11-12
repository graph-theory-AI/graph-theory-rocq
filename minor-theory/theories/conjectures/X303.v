(** * Minor.conjectures.X303 -- v2 row: Seymour's pathwidth conjecture, 2-connected graphs of large pathwidth
      contain a given apex-forest or a given outerplanar graph as a minor (record arXiv:1801.01833) *)

From GTBase Require Import base pathwidth.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X303 statement ******************************************************)

(** Reused vocabulary: GTBase.base [minor] (coq-graph-theory's minors), [is_forest], [k_connected], the
    complete graphs 'K_n and the complete bipartite graphs [KB], and GTBase.pathwidth [pathwidth_at_most] (the
    pathwidth family's canonical).  Apex-forests and outerplanar graphs are written out in the statement, as
    hypotheses.  X303 declares no helper of its own. *)

(** Corpus row: studies:std_seymour_s_pathwidth_conjecture
    Site: none
    Review: none
    English statement: (Seymour, 1993; studies slice of the corpus, record arXiv:1801.01833)
      For every apex-forest H1 and outerplanar graph H2 there is an integer p such that every 2-connected
      graph of pathwidth at least p contains H1 or H2 as a minor.
    Definitions: [is_forest S] - any two vertices are joined by at most one irredundant path inside S, i.e. the
      subgraph induced on S has no cycle (coq-graph-theory), so [exists v : H1, is_forest ([set: H1] :\ v)]
      says that H1 - v is a forest for some vertex v of H1, i.e. H1 is an apex-forest; [minor G H] - H is a
      minor of G: a map from the vertices of G onto those of H (or to nothing) whose fibres are connected, with
      an edge of G between the fibres of x and y whenever x and y are adjacent in H (coq-graph-theory);
      [~ minor H2 'K_4 /\ ~ minor H2 (KB 2 3)] - H2 has neither K_4 nor K_{2,3} as a minor, i.e. H2 is
      outerplanar ([KB 2 3] is the complete bipartite graph with parts of 2 and 3 vertices); [k_connected G 2] -
      G has more than 2 vertices and stays connected after deleting any fewer than 2 of them, i.e. G is
      2-connected (GTBase.base); [pathwidth_at_most G p] - G has a decomposition indexed by a path whose bags
      have at most p + 1 vertices (GTBase.pathwidth), so [~ pathwidth_at_most G p] says that G has pathwidth
      above p.
    Notes: encoded as stated (arXiv:1801.01833v4, Huynh, Joret, Micek and Wood, CombinatoricaSubmission.tex
      l.179-182, Theorem SeymourConj: "For every apex-forest $H_1$ and outerplanar graph $H_2$ there is an
      integer $p$ such that every 2-connected graph of pathwidth at least $p$ contains $H_1$ or $H_2$ as a
      minor"), with the record's definitions: graphs are finite and simple (l.334); an apex-forest is a graph H
      with H - v a forest for some vertex v (l.176), so the graph with no vertex is not one (that instance would
      hold anyway: every graph has it as a minor); a graph is outerplanar if it has a plane embedding with all
      its vertices on the outer face (l.176), rendered by Chartrand and Harary's characterization, no K_4 and
      no K_{2,3} minor, which is exact for finite graphs (as X82 renders outerplanarity); pathwidth is the
      least k with a path decomposition whose bags have at most k + 1 vertices (l.163).  "Pathwidth at least p"
      is read as pathwidth above p: a p for the source gives the same p here, and a p here gives p + 1 for the
      source.  Small graphs that "2-connected" might count differently (K_2) have pathwidth at most 1, so the
      choice of p absorbs them.  The order of the quantifiers is the source's: p depends on H1 and H2.  Solved
      in the record: l.188 ("In this paper we prove" the conjecture; an independent proof is Dang and Thomas's,
      arXiv:1712.04549); l.1195-1196 give p = 2^(9l^2 - 3l + 2) - 2 for the two universal families of order l
      (lit30's ERRATA tuple).  The record key also names 2604.13700, which states a different problem of
      Seymour's (CORPUS_FEEDBACK item 95); this encoding follows 1801.01833. *)
Definition seymour_two_connected_pathwidth_statement : Prop :=
  forall H1 H2 : sgraph,
    (exists v : H1, is_forest ([set: H1] :\ v)) ->
    ~ minor H2 'K_4 -> ~ minor H2 (KB 2 3) ->
    exists p : nat,
      forall G : sgraph,
        k_connected G 2 -> ~ pathwidth_at_most G p ->
        minor G H1 \/ minor G H2.

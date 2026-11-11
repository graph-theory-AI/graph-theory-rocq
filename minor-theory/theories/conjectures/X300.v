(** * Minor.conjectures.X300 -- v2 row: Grytczuk's conjecture, bounded nonrepetitive chromatic number of graphs
      excluding a minor (record arXiv:1904.05269) *)

From GTBase Require Import base.
From GraphTheory Require Import minor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X300 statement ******************************************************)

(** Reused vocabulary: coq-graph-theory's [minor] (re-exported by GTBase base) and GTBase.walks_paths
    [seq_simple_path] (the simple-path family's canonical).  The nonrepetitive colouring is written out in the
    statement, in the form of X126's.  X300 declares no helper of its own. *)

(** Corpus row: studies:std_grytczuk_s_conjecture_nonrepetitive_chromatic_nu
    Site: none
    Review: none
    English statement: (Grytczuk; studies slice of the corpus, record arXiv:1904.05269)
      For every graph X, there is an integer k such that every X-minor-free graph G satisfies pi(G) <= k.
    Definitions: [minor G X] - X is a minor of G (coq-graph-theory: a map from the vertices of G onto those of X,
      defined on a part of G, whose fibres are connected and joined by an edge whenever their images are
      adjacent), so [~ minor G X] says that G is X-minor-free; [seq_simple_path p] - p is a non-empty sequence of
      distinct vertices, consecutive ones adjacent: a path on [size p] vertices (GTBase.walks_paths); a colouring
      [col : G -> 'I_k] is nonrepetitive when no path p on 2t vertices (t > 0) has the colours of its first t
      vertices, [map col (take t p)], equal to those of its last t, [map col (drop t p)]; pi(G) <= k means that G
      has a nonrepetitive colouring with k colours.
    Notes: encoded as stated (arXiv:1904.05269v4, Dujmovic, Esperet, Joret, Walczak and Wood,
      NonrepetitivePlanar-AiC-SecondRevision.tex l.113-116, their Theorem 3, which l.106 says confirms Grytczuk's
      conjecture), with the record's definitions (l.85-86): a k-colouring gives one of k colours to each vertex;
      a path (v_1, ..., v_2t) of even order is repetitively coloured when phi(v_i) = phi(v_(t+i)) for
      i = 1, ..., t; a colouring is nonrepetitive when no path is repetitively coloured; pi(G) is the least k such
      that G has a nonrepetitive k-colouring.  So pi(G) <= k is the existence of a nonrepetitive colouring into
      ['I_k] (a colouring with fewer colours is one with k).  Every graph has the graph with no vertex as a minor,
      so for X = K_0 the class is empty.  X23's planar row ([planar_bounded_nonrepetitive_chromatic_statement])
      is the case of the K_5-minor-free graphs that also exclude K_(3,3); a later edge item may record it.
      Pinned status solved: proved in the record (Theorem 3). *)
Definition grytczuk_minor_free_nonrepetitive_statement : Prop :=
  forall X : sgraph, exists k : nat,
    forall G : sgraph, ~ minor G X ->
      exists col : G -> 'I_k,
        forall (p : seq G) (t : nat),
          seq_simple_path p -> size p = 2 * t -> 0 < t ->
          map col (take t p) != map col (drop t p).

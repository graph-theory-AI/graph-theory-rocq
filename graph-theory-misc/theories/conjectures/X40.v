(** * GTMisc.conjectures.X40 -- v2 coarse Menger c=2 row *)

From GTBase Require Export base.
From GTMisc.conjectures Require Import X39.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X40 statements ******************************************************)

(** Corpus row: arxiv:2508.14332#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2508.14332__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2508.14332__00.json
    English statement: (Nguyen, Scott and Seymour 2025, "Asymptotic structure. IV. A
      counterexample to the weak coarse Menger conjecture", the open case c = 2 of
      Conjecture 1.1)
      For every k >= 1 there is an l > 0 such that for every finite simple graph G and all
      vertex sets S and T, either G contains k distinct S-T paths pairwise at distance at
      least 2, or there is a vertex set X with |X| <= k-1 such that the closed l-ball around X
      meets every S-T path.
    Definitions: [x39_ball], [x39_set_ball], [x39_path_vertices], [x39_xy_path],
      [x39_pairwise_distant_paths], [x39_has_k_distant_xy_paths], [x39_separates_xy] - the
      coarse-path vocabulary reused from graph-theory-misc/theories/conjectures/X39.v: closed
      balls, the vertex set of a walk, simple S-T paths, pairwise distance of paths, the
      existence of k such distant paths, and separation of S from T by a vertex set.
    Notes: this is the c = 2 instance of the coarse Menger conjecture, so the distance
      parameter is the literal constant 2, and l depends only on k.  "Every S-T path contains a
      vertex within distance l of X" is stated in the equivalent separation form "the l-ball
      around X separates S from T". *)
Definition coarse_menger_distance_two_separator_statement : Prop :=
  forall k : nat,
    1 <= k ->
    exists ell : nat,
      0 < ell /\
      forall (G : sgraph) (S T : {set G}),
        x39_has_k_distant_xy_paths 2 k S T \/
        exists X : {set G},
          #|X| <= k - 1 /\
          x39_separates_xy S T (x39_set_ball ell X).

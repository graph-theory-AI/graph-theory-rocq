(** * Chromatic.conjectures.X186 -- v2 subdivision or chi2 row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X186 vocabulary ***********************************************)

Definition x186_chi2 (G : sgraph) : nat :=
  \max_(v : G) χ([set: induced (rel_ball (--) 2 v)]).

Definition x186_contains_induced_subdivision (G J : sgraph) : Prop :=
  exists branch : J -> G,
    injective branch /\
    forall x y : J,
      x -- y ->
      exists p : seq G,
        [/\ path (--) (branch x) p,
            last (branch x) p = branch y,
            uniq (branch x :: p) &
            forall z : G,
              z \in p -> z != branch y -> forall u : J, z != branch u].

(** ** X186 statements *****************************************************)

(** Corpus row: arxiv:1701.05597#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1701.05597__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1701.05597__01.json
    English statement: (Scott and Seymour 2019, Conjecture 1.10, arXiv:1701.05597)
      For every finite simple graph J and every tau there is a c such that every graph G with
      chromatic number greater than c either contains a subdivision of J, realised by a branch map
      and internally branch-free connecting paths, or has local chromatic number chi_2(G) greater
      than tau, where chi_2(G) is the maximum over vertices of the chromatic number of the ball of
      radius 2.
    Definitions: [x186_chi2 G] - the maximum over vertices v of chi of the subgraph induced on the
      ball of radius 2 around v (this file); [x186_contains_induced_subdivision G J] - an injective
      branch map from the vertices of J into G with, for each edge of J, a simple path between the
      corresponding branch vertices whose internal vertices are not branch vertices (this file);
      [rel_ball] (coq-graph-theory / GTBase).
    Notes: KNOWN UNFAITHFUL ENCODING, corpus leg blocked. The faithfulness audit of 2026-07-17,
      meta/BLOCKED_RETARGETING_AUDIT.md and the row's verification_note, found that the load-bearing
      qualifier INDUCED of the source, "some induced subgraph of G is a subdivision of J", is absent
      from [x186_contains_induced_subdivision]: there is no chord-freeness condition and no internal
      disjointness between the paths of different edges, so the predicate is strictly weaker than
      containing an induced subdivision and the disjunction is easier to satisfy than the source's.
      The body is left untouched here, WP4 changes comments only. *)
Definition subdivision_or_local_chi_two_statement : Prop :=
  forall (J : sgraph) (tau : nat),
    exists c : nat,
      forall G : sgraph,
        c < χ([set: G]) ->
        x186_contains_induced_subdivision G J \/ tau < x186_chi2 G.

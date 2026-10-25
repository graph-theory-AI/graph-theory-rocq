(** * Digraph.conjectures.X179 -- v2 kappa-maderian digraph row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph dipath.
From GTBase Require Import walks_paths.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X179 vocabulary ***********************************************)

Definition x179_strongly_connected_after_deleting (G : diGraphType) (S : {set G}) : Prop :=
  forall x y : G,
    x \notin S -> y \notin S ->
    connect (fun u v => (u --> v) && (u \notin S) && (v \notin S)) x y.

Definition x179_k_vertex_strongly_connected (G : diGraphType) (k : nat) : Prop :=
  forall S : {set G}, #|S| < k -> x179_strongly_connected_after_deleting S.

Definition x179_out_cut (G : diGraphType) (S : {set G}) : {set G * G} :=
  [set e : G * G | (e.1 \in S) && (e.2 \notin S) && (e.1 --> e.2)].

Definition x179_k_arc_strongly_connected (G : diGraphType) (k : nat) : Prop :=
  forall S : {set G}, S != set0 -> S != [set: G] -> k <= #|x179_out_cut S|.

Definition x179_directed_path (G : diGraphType) (s t : G) (p : seq G) : Prop :=
  path (fun x y => x --> y) s p /\ last s p = t /\ uniq (s :: p).

(** A subdivision of [D] in [G]: injective branch vertices and, for every arc [x --> y] of [D],
    a nonempty directed path ([dipath]) from the branch vertex of [x] to that of [y] whose
    interior avoids every branch vertex, the interiors of the paths of distinct arcs being
    disjoint.  This is [X2.contains_subdivision D G] unfolded (X2's helpers inlined), kept
    local so that X179 does not become a consumer of the migrated X2 helpers. *)
Definition x179_directed_subdivision (G D : diGraphType) : Prop :=
  exists branch : D -> G,
    injective branch /\
    exists paths : D -> D -> seq G,
      (forall x y : D, x --> y ->
        [/\ 0 < size (paths x y),
            dipath (branch x) (paths x y),
            last (branch x) (paths x y) = branch y
          & [disjoint seq_interior (branch x) (branch y) (branch x :: paths x y)
             & [set z | [exists u : D, branch u == z]]]]) /\
      (forall x y x' y' : D, x --> y -> x' --> y' ->
        (x != x') || (y != y') ->
        [disjoint seq_interior (branch x) (branch y) (branch x :: paths x y)
         & seq_interior (branch x') (branch y') (branch x' :: paths x' y')]).

(** A k-strong digraph has at least [k + 1] vertices; the helper above leaves that part of the
    definition out, so the hosts carry the guard [k < #|G|]. *)
Definition x179_kappa_maderian (D : diGraphType) : Prop :=
  exists k : nat,
    forall G : diGraphType,
      k < #|G| -> x179_k_vertex_strongly_connected G k -> x179_directed_subdivision G D.

(** The same host guard: without it the one-vertex digraph, which has no nonempty proper vertex
    set, would be k-arc-strong for every k.  A k-arc-strong digraph with at least two vertices
    has out-degrees at least k, hence at least [k + 1] vertices, so for [k >= 1] the guard only
    excludes the hosts with fewer than two vertices. *)
Definition x179_arc_kappa_maderian (D : diGraphType) : Prop :=
  exists k : nat,
    forall G : diGraphType,
      k < #|G| -> x179_k_arc_strongly_connected G k -> x179_directed_subdivision G D.

(** ** X179 statements *****************************************************)

(** Corpus row: arxiv:1610.00876#05
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1610.00876__05/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1610.00876__05.json
    English statement: (Aboulker, Cohen, Havet, Lochet, Moura, Thomasse 2016, arXiv:1610.00876, Problem 16)
      Every finite digraph D is kappa-maderian and kappa-prime-maderian: there is a k such that
      every k-strongly-connected digraph contains a subdivision of D, and there is a k such that
      every k-arc-strongly-connected digraph contains a subdivision of D.
    Definitions: [x179_k_vertex_strongly_connected G k] - deleting fewer than k vertices leaves
      every remaining ordered pair mutually reachable (this file);
      [x179_k_arc_strongly_connected G k] - every nonempty proper vertex set has out-cut at
      least k (this file); [x179_directed_subdivision G D] - injective branch vertices in G
      and, for every arc of D, a nonempty directed path whose interior avoids the branch
      vertices, with pairwise disjoint interiors ([X2.contains_subdivision D G] unfolded; this
      file); [x179_kappa_maderian] / [x179_arc_kappa_maderian] - some k such that every host
      with more than k vertices and of strong (arc-)connectivity at least k contains a
      subdivision of D (this file).
    Notes: The corpus poses two questions (are all digraphs kappa-maderian,
      kappa-prime-maderian); the body encodes the conjunction of the two affirmative answers.
      Re-encoded 2026-10-25: the hosts have more than k vertices (a k-strong digraph has at
      least k + 1 vertices; without the guard the one-vertex digraph is k-strong for every k
      and refutes the body, meta/probe_hints/digraph_kappa_maderian_statement.v); the
      replacement paths of a subdivision have pairwise disjoint interiors (before, interiors
      could be shared); D is loopless ([irreflexive (@arc D)]), as the source's digraphs are:
      a loop has no subdivision by a nonempty directed path. The pinned review records that
      Gishboliner, Steiner and Szabo (arXiv:2008.13224, Propositions 10-11) answered the
      kappa-prime question negatively; not formalized here. *)
Definition digraph_kappa_maderian_statement : Prop :=
  forall D : diGraphType, irreflexive (@arc D) ->
    x179_kappa_maderian D /\ x179_arc_kappa_maderian D.

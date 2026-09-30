(** * Chromatic.conjectures.X194 -- v2 clustered colouring minor row *)

From GraphTheory Require Import minor.
From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X194 vocabulary ***********************************************)

Definition x194_vertex_ranking (G : sgraph) (k : nat) (rank : G -> 'I_k) : Prop :=
  forall (x y : G) (p : seq G),
    x != y ->
    path (--) x p ->
    last x p = y ->
    rank x = rank y ->
    exists z : G, z \in p /\ rank x < rank z.

Definition x194_treedepth_at_most (G : sgraph) (k : nat) : Prop :=
  exists rank : G -> 'I_k, x194_vertex_ranking rank.

Definition x194_clustered_chromatic_minor_class_le (H : sgraph) (k : nat) : Prop :=
  exists c : nat,
    forall G : sgraph, ~ minor G H -> clustered_colouring G k c.

(** ** X194 statements *****************************************************)

(** Norin-Scott-Seymour-Wood Conjecture 4: the clustered chromatic number of
    the [H]-minor-free class is at most [2*td(H)-2]. *)
(** Corpus row: arxiv:1708.02370#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1708.02370__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1708.02370__00.json
    English statement: (Norin, Scott, Seymour and Wood 2018, Conjecture 4, arXiv:1708.02370)
      For every finite simple graph H and every k >= 2 such that H has treedepth at most k, the
      class of H-minor-free graphs has clustered chromatic number at most 2k - 2: there is a
      clustering bound c such that every H-minor-free graph has a colouring with 2k - 2 colours all
      of whose monochromatic connected sets have at most c vertices.
    Definitions: [x194_treedepth_at_most H k] - there is a ranking of the vertices by ['I_k] such
      that on every path between two vertices of equal rank some internal vertex has strictly larger
      rank (this file); [x194_vertex_ranking] (this file); [x194_clustered_chromatic_minor_class_le
      H k] - there is one clustering constant c, chosen before the graphs, with [clustered_colouring
      G k c] for every H-minor-free G (this file); [clustered_colouring G k c] - a k-colouring in
      which every connected monochromatic vertex set has at most c vertices (GTBase
      base/theories/surface.v); [minor] (coq-graph-theory minor.v).
    Notes: The clustering constant is CLASS-UNIFORM, quantified before the graphs, which is the
      intended reading of the clustered chromatic number of a class; this was a 2026-07-17 re-
      encoding. The guard 2 <= k is load-bearing: at treedepth 1, i.e. edgeless H, the bound 2k-2
      truncates to 0 colours and the one-vertex graph refutes the unguarded statement, so the
      source's domain, H with at least one edge, is imposed explicitly, see
      meta/BLOCKED_RETARGETING_AUDIT.md. Corpus status: partial, proved for bounded treedepth and
      bounded pathwidth classes. *)
Definition clustered_chromatic_minor_class_treedepth_bound_statement : Prop :=
  forall H : sgraph,
    forall k : nat,
      2 <= k ->
      x194_treedepth_at_most H k ->
      x194_clustered_chromatic_minor_class_le H (2 * k - 2).

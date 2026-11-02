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

(** CONNECTED tree-depth at most [k] (arXiv:1708.02370v2, ClusteredColouring.arXiv2.tex
    l.147): a rooted tree of depth at most [k] whose closure contains [H].  Removing its
    root [r] leaves a rooted forest of [H - r] of depth at most [k - 1], and a new root above
    such a forest gives back such a tree; so: [0 < k] and some [r] with td(H - r) <= k - 1
    ([x194_treedepth_at_most], ordinary tree-depth).  The body of X218's
    [x218_ctd_at_most]; X218 imports this file, not the reverse. *)
Definition x194_ctd_at_most (H : sgraph) (k : nat) : Prop :=
  0 < k /\ exists r : H, x194_treedepth_at_most (induced (~: [set r])) k.-1.

Definition x194_clustered_chromatic_minor_class_le (H : sgraph) (k : nat) : Prop :=
  exists c : nat,
    forall G : sgraph, ~ minor G H -> clustered_colouring G k c.

(** ** X194 statements *****************************************************)

(** Norin-Scott-Seymour-Wood Conjecture 4: the clustered chromatic number of
    the [H]-minor-free class is at most [2*ctd(H)-2]. *)
(** Corpus row: arxiv:1708.02370#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1708.02370__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1708.02370__00.json
    English statement: (Norin, Scott, Seymour and Wood 2018, Conjecture 4, arXiv:1708.02370)
      For every finite simple graph H, the class of H-minor-free graphs has clustered chromatic
      number at most 2 ctd(H) - 2, with ctd the connected tree-depth: for every k such that H has
      connected tree-depth at most k there is one clustering bound c such that every H-minor-free
      graph has a colouring with 2k - 2 colours all of whose monochromatic connected sets have at
      most c vertices.
    Definitions: [x194_ctd_at_most H k] - 0 < k and some vertex r of H with tree-depth of H - r at
      most k - 1 (this file); [x194_treedepth_at_most H k] - there is a ranking of the vertices by
      ['I_k] such that on every path between two vertices of equal rank some internal vertex has
      strictly larger rank (this file); [x194_vertex_ranking] (this file);
      [x194_clustered_chromatic_minor_class_le H k] - there is one clustering constant c, chosen
      before the graphs, with [clustered_colouring G k c] for every H-minor-free G (this file);
      [clustered_colouring G k c] - a k-colouring in which every connected monochromatic vertex set
      has at most c vertices (GTBase base/theories/surface.v); [minor] and [induced]
      (coq-graph-theory).
    Notes: encoded as printed in arXiv:1708.02370v2 (ClusteredColouring.arXiv2.tex l.182-186,
      statement l.184), with the connected tree-depth of l.147 (the least depth of a rooted tree
      whose closure contains H; deleting its root, or adding one above a rooted forest of H - r,
      gives the encoded form). "For every k with ctd(H) <= k, at most 2k - 2" is the bound
      2 ctd(H) - 2 (take k = ctd(H); more colours keep the clustering). The clustering constant is
      CLASS-UNIFORM, quantified before the graphs (the 2026-07-17 re-encoding). No guard is needed:
      ctd(H) = 1 forces H = K_1, whose minor-free class holds only the graph with no vertex (0
      colours); the graph with no vertex has no such tree, so the body is vacuous there (and true
      under ctd = 1). RE-ENCODED 2026-11-02 (coordination/PROGRAMME.md section 3, A2, direction
      weaken; the earlier body is frozen as X194Legacy in theories/migration/monochromatic.v): it
      used ordinary tree-depth with the guard 2 <= k, which is stronger than the source for H with
      two components of tree-depth td(H) >= 2, where ctd(H) = td(H) + 1 (informally; the paper's
      commented-out l.185 considers 2 td(H) - 1 there). The frozen body implies this one
      (kernel-checked: monochromatic.v). Corpus status: partial, proved for bounded treedepth and
      bounded pathwidth classes. *)
Definition clustered_chromatic_minor_class_treedepth_bound_statement : Prop :=
  forall H : sgraph,
    forall k : nat,
      x194_ctd_at_most H k ->
      x194_clustered_chromatic_minor_class_le H (2 * k - 2).

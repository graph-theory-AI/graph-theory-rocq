(** * Minor.conjectures.X67 -- v2 theta-triangle bounded-treewidth row *)

From GTBase Require Export base.
From Minor.conjectures Require Import X27.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X67 vocabulary ************************************************)

Definition x67_consecutive_in_path (G : sgraph) (p : seq G) (u v : G) : Prop :=
  (u, v) \in zip p (behead p) \/ (v, u) \in zip p (behead p).

Definition x67_path_vertices (G : sgraph) (p : seq G) : {set G} :=
  [set x : G | x \in p].

Definition x67_internal_vertices (G : sgraph) (a b : G) (p : seq G) : {set G} :=
  x67_path_vertices p :\: [set a; b].

Definition x67_induced_path_between (G : sgraph) (a b : G) (p : seq G) : Prop :=
  match p with
  | [::] => False
  | x :: q =>
      x = a /\
      last x q = b /\
      3 <= size p /\
      uniq p /\
      path (--) x q /\
      forall u v : G,
        u \in p -> v \in p -> u -- v -> u != v ->
        x67_consecutive_in_path p u v
  end.

Definition x67_no_cross_edges
    (G : sgraph) (a b : G) (p q : seq G) : Prop :=
  forall u v : G,
    u \in x67_internal_vertices a b p ->
    v \in x67_internal_vertices a b q ->
    ~~ (u -- v).

Definition x67_theta (G : sgraph) : Prop :=
  exists (a b : G) (p1 p2 p3 : seq G),
    a != b /\
    x67_induced_path_between a b p1 /\
    x67_induced_path_between a b p2 /\
    x67_induced_path_between a b p3 /\
    [disjoint x67_internal_vertices a b p1 & x67_internal_vertices a b p2] /\
    [disjoint x67_internal_vertices a b p1 & x67_internal_vertices a b p3] /\
    [disjoint x67_internal_vertices a b p2 & x67_internal_vertices a b p3] /\
    x67_no_cross_edges a b p1 p2 /\
    x67_no_cross_edges a b p1 p3 /\
    x67_no_cross_edges a b p2 p3.

(** ** X67 statements ******************************************************)

(** Corpus row: arxiv:2001.01607#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2001.01607__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2001.01607__01.json
    English statement: (Pilipczuk, Sintiari, Thomasse and Trotignon 2020, open question in
      "(Theta, triangle)-free and (even hole, K_4)-free graphs. Part 2: bounds on treewidth")
      There is a function f from the naturals to the naturals such that for every t at least 4,
      every triangle-free finite simple graph that contains no theta and has maximum degree at
      most t has treewidth at most f(t).
    Definitions: [x67_consecutive_in_path p u v] - u and v are consecutive entries of the
      sequence p (minor-theory/theories/conjectures/X67.v); [x67_path_vertices p] - the set of
      vertices occurring in p (same file); [x67_internal_vertices a b p] - the vertices of p
      other than a and b (same file); [x67_induced_path_between a b p] - p is a path of at least
      three pairwise distinct vertices from a to b whose only edges are the consecutive ones,
      i.e. an induced path of length at least 2 (same file); [x67_no_cross_edges a b p q] - no
      edge joins an internal vertex of p to an internal vertex of q (same file);
      [x67_theta G] - G contains a theta: two distinct vertices joined by three induced paths of
      length at least 2 with pairwise disjoint interiors and no edges between those interiors
      (same file); [x27_treewidth_at_most G k] (minor-theory/theories/conjectures/X27.v);
      [triangle_free G], [Delta G] (base/theories/base.v).
    Notes: the function f is quantified before t and G.  The guard [4 <= t] is the source's own
      domain; the cases t <= 3 are known.  Requiring the three branch paths to be induced, to
      have disjoint interiors and to have no edges between their interiors makes their union an
      INDUCED theta, matching the source's induced-subgraph reading.  The corpus records this
      row as solved (Abrishami et al., arXiv:2108.01162). *)
Definition theta_triangle_free_bounded_degree_treewidth_statement : Prop :=
  exists f : nat -> nat,
    forall (t : nat) (G : sgraph),
      4 <= t ->
      Delta G <= t ->
      triangle_free G ->
      ~ x67_theta G ->
      x27_treewidth_at_most G (f t).

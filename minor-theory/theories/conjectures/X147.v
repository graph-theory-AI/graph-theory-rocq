(** * Minor.conjectures.X147 -- v2 fat-minor/quasi-isometry row *)

From GraphTheory Require Import minor.
From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X147 vocabulary ***********************************************)

Definition x147_c_fat_minor (G H : sgraph) (c : nat) : Prop :=
  exists branch : H -> {set G},
    (forall h : H, branch h != set0) /\
    (forall h : H, connected (branch h)) /\
    (forall h1 h2 : H, h1 != h2 -> branch h1 :&: branch h2 = set0) /\
    (forall h1 h2 : H, h1 -- h2 ->
      exists x y : G, [/\ x \in branch h1, y \in branch h2 & x -- y]) /\
    (forall h1 h2 : H, h1 != h2 -> ~~ (h1 -- h2) ->
      forall x y : G, x \in branch h1 -> y \in branch h2 -> c <= @graph_dist G x y).

Definition x147_quasi_isometric_to_H_minor_free
    (G H : sgraph) (L C : nat) : Prop :=
  exists Q : sgraph,
    ~ minor Q H /\
    exists (f : G -> Q) (g : Q -> G),
      (forall x y : G,
        @graph_dist Q (f x) (f y) <= L * @graph_dist G x y + C) /\
      (forall x y : Q,
        @graph_dist G (g x) (g y) <= L * @graph_dist Q x y + C) /\
      (forall y : Q, exists x : G, @graph_dist Q (f x) y <= C) /\
      (forall x : G, exists y : Q, @graph_dist G (g y) x <= C).

(** ** X147 statements *****************************************************)

(** Corpus row: studies:std_georgakopoulos_papasoglu_conjecture_fat_minors
    Site: none
    Review: none
    English statement: (Georgakopoulos and Papasoglu, conjecture on fat minors)
      For every finite simple graph H and every fatness parameter c there are constants L and
      C such that every finite simple graph G that does not contain H as a c-fat minor is
      related, by maps with the (L,C) bounds recorded below, to some graph with no H minor.
    Definitions: [x147_c_fat_minor G H c] - there is an assignment of nonempty, connected,
      pairwise disjoint branch sets to the vertices of H such that adjacent vertices of H have
      an edge between their branch sets and distinct non-adjacent vertices of H have their
      branch sets at graph distance at least c (minor-theory/theories/conjectures/X147.v);
      [x147_quasi_isometric_to_H_minor_free G H L C] - there is a graph Q with no H minor and
      maps f from G to Q and g from Q to G, each satisfying only the upper bound
      dist(f x, f y) <= L * dist(x,y) + C (respectively for g) and each coarsely surjective
      within C (same file); [graph_dist x y] - the graph metric, defined as the least radius
      of a ball around x containing y, saturating at the number of vertices when y is
      unreachable (base/theories/graph_metric.v).
    Notes: PROXY, weaker than the source (faithfulness audit 2026-07-17,
      meta/BLOCKED_RETARGETING_AUDIT.md).  A genuine (L,C)-quasi-isometry also requires the
      lower bound dist(x,y)/L - C <= dist(f x, f y) and that g be a quasi-inverse of f; the
      encoding supplies neither, giving two decoupled coarsely surjective maps with upper
      Lipschitz bounds only.  The conclusion is therefore strictly weaker than "G admits an
      (L,C)-quasi-isometry to an H-minor-free graph".  A second modelling choice: distances
      between vertices in different components are capped at the number of vertices rather
      than infinite. *)
Definition georgakopoulos_papasoglu_fat_minor_quasi_isometry_statement : Prop :=
  forall (H : sgraph) (c : nat),
    exists L C : nat,
      forall G : sgraph,
        ~ x147_c_fat_minor G H c ->
        x147_quasi_isometric_to_H_minor_free G H L C.

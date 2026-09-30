(** * Extremal.conjectures.X61 -- v2 finite induced-saturation exceptions row *)

From GTBase Require Export base.
From Extremal.conjectures Require Import X49 X60.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X61 vocabulary ************************************************)

Definition x61_induced_free (G H : sgraph) : Prop :=
  forall S : {set G}, ~ inhabited (induced S ≃ H).

Definition x61_neither_clique_nor_stable (H : sgraph) : Prop :=
  (exists a b : H, a != b /\ ~~ (a -- b)) /\
  (exists a b : H, a != b /\ a -- b).

Definition x61_induced_saturated (H G : sgraph) : Prop :=
  x61_induced_free G H /\
  (forall a b : G,
    a != b ->
    ~~ (a -- b) ->
    x61_induced_free (@x49_add_edge_graph G a b) H -> False) /\
  forall e : {set G},
    e \in x60_edge_set G ->
    x61_induced_free (@x60_delete_edge_graph G e) H -> False.

Definition x61_infinite_family (F : sgraph -> Prop) : Prop :=
  forall n : nat, exists H : sgraph, F H /\ n <= #|H|.

(** Corpus row: arxiv:2506.08810#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2506.08810__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2506.08810__00.json
    English statement: (Bonamy, Groenland, Johnston, Morrison, Scott 2025, arXiv:2506.08810 Problem 21)
      There is a family F of finite graphs containing graphs of arbitrarily many vertices such
      that every member H of F has both an edge and a non-edge (so it is neither a clique nor
      an independent set) and no finite graph is H-induced-saturated.
    Definitions: [x61_induced_free G H] - no vertex set of G induces a copy of H (X61.v);
      [x61_neither_clique_nor_stable H] - H has two distinct non-adjacent vertices and two
      adjacent vertices (X61.v); [x61_induced_saturated H G] - G is H-induced-free while adding
      any non-edge and deleting any edge both create an induced copy of H, using
      [x49_add_edge_graph] (X49.v) and [x60_delete_edge_graph], [x60_edge_set] (X60.v)
      (X61.v); [x61_infinite_family F] - for every n some member has at least n vertices
      (X61.v).
    Notes: "infinite family" is rendered as a family with members of unbounded size, which is the
      usable finite-type reading (a genuine infinite set of isomorphism types is not expressible
      here). The family is a predicate on sgraph rather than a set, since [sgraph] is not an
      eqType. *)
Definition infinite_family_without_finite_induced_saturation_statement : Prop :=
  exists F : sgraph -> Prop,
    x61_infinite_family F /\
    forall H : sgraph,
      F H ->
      x61_neither_clique_nor_stable H /\
      forall G : sgraph, ~ x61_induced_saturated H G.

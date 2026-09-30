(** * Infinite.conjectures.D4inf1 — unfriendly partitions & unions of triangle-free graphs.

    Two OPEN infinite-combinatorics rows, faithfully stated over the Prop-level
    [iGraph] carrier with NO smuggled choice / cardinal arithmetic / topology.
    "At least as many … as …" and "a union of ℵ₀ …" are rendered by the
    definitional injection ([card_le]) and by a [nat]-indexed edge colouring —
    both first-order [Prop]s.  Vocabulary is in [Infinite.foundations.igraph]. *)

From GTBase Require Export base.
From Infinite Require Import foundations.igraph.
From mathcomp Require Import all_boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Corpus row: opg:unfriendly_partitions
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/unfriendly_partitions/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/unfriendly_partitions.json
    English statement: (Open Problem Garden, "Unfriendly partitions") Every
      countable graph has an unfriendly partition into two classes: a map p from
      vertices to booleans such that every vertex has at least as many
      neighbours in the other class as in its own, "at least as many" meaning
      that its same-class neighbours inject into its other-class neighbours.
    Definitions: [iGraph]/[iV]/[iadj] - a possibly infinite simple graph
      (infinite-graph-theory/theories/foundations/igraph.v);
      [countable_graph G] - the vertex type injects into nat (igraph.v);
      [own_nbr p x] and [cross_nbr p x] - the same-class and other-class
      neighbourhoods of x (igraph.v); [unfriendly p] - at every vertex,
      [card_le (own_nbr p x) (cross_nbr p x)] (igraph.v); [card_le P Q] - there
      is an injection from the subtype of P into the subtype of Q, the
      choice-free definition of "at most as many" (igraph.v).
    Notes: [countable_graph] means "injects into nat", so FINITE graphs also
      satisfy the hypothesis, whereas the source restricts to countably infinite
      graphs; the formal statement is therefore slightly STRONGER than the
      source (harmlessly, since finite graphs do have unfriendly partitions).
      The source is a Problem (a question) and the body asserts the affirmative
      answer.  No choice, cardinal arithmetic or topology is used. *)
Definition unfriendly_partitions_statement : Prop :=
  forall G : iGraph, countable_graph G -> exists p : iV G -> bool, unfriendly p.

(** Corpus row: opg:unions_of_triangle_free_graphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/unions_of_triangle_free_graphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/unions_of_triangle_free_graphs.json
    English statement: (Open Problem Garden, "Unions of triangle free graphs")
      There exists a graph containing no K_4 - no four pairwise adjacent
      vertices - whose edges cannot be covered by countably many triangle-free
      graphs.
    Definitions: [iGraph]/[iadj] - a possibly infinite simple graph
      (infinite-graph-theory/theories/foundations/igraph.v); [K4_free G] - there
      are no a, b, c, d with all six pairs adjacent, distinctness being free
      from irreflexivity (igraph.v); [ctf_cover G] - "G is a union of countably
      many triangle-free graphs", rendered as a symmetric colouring of the
      vertex pairs by naturals with no monochromatic triangle (igraph.v).
    Notes: "a union of aleph_0 triangle-free graphs" is encoded as a PARTITION
      of the edges into countably many triangle-free classes; a cover into
      triangle-free subgraphs exists exactly when such a colouring does, so this
      is faithful.  The source is a Problem (a question); the body asserts the
      existence of a witness graph, and nothing about its truth is proved. *)
Definition unions_of_triangle_free_graphs_statement : Prop :=
  exists G : iGraph, K4_free G /\ ~ ctf_cover G.

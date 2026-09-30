(** * Infinite.conjectures.D4_unblocked -- legacy blocked OPG rows *)

From mathcomp Require Import all_boot.
From Infinite Require Import foundations.igraph.
From Infinite.conjectures Require Import D4inf4.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition i_neighbourhood (G : iGraph) (x : iV G) (y : iV G) : Prop :=
  iadj x y.

Definition countably_infinite_neighbourhood (G : iGraph) (x : iV G) : Prop :=
  exists f : nat -> {y : iV G | i_neighbourhood x y},
    injective f /\
    forall y : {y : iV G | i_neighbourhood x y}, exists n : nat, f n = y.

Definition uncountable_neighbourhood (G : iGraph) (x : iV G) : Prop :=
  ~ exists f : {y : iV G | i_neighbourhood x y} -> nat, injective f.

Definition aleph0_aleph1_bipartition (G : iGraph) (A B : iV G -> Prop) : Prop :=
  (forall x : iV G, A x \/ B x) /\
  (forall x : iV G, ~(A x /\ B x)) /\
  (forall x y : iV G, iadj x y -> (A x /\ B y) \/ (B x /\ A y)) /\
  (forall x : iV G, A x -> countably_infinite_neighbourhood x) /\
  (forall x : iV G, B x -> uncountable_neighbourhood x).

Definition aleph0_aleph1_graph (G : iGraph) : Prop :=
  exists A B : iV G -> Prop, aleph0_aleph1_bipartition A B.

(** Corpus row: opg:characterizing_aleph_0_aleph_1_graphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/characterizing_aleph_0_aleph_1_graphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/characterizing_aleph_0_aleph_1_graphs.json
    English statement: (Open Problem Garden, "Characterizing (aleph_0,aleph_1)-
      graphs") Call a graph an (aleph_0, aleph_1)-graph when its vertices split
      into two classes A and B such that every edge runs between the classes,
      every A-vertex has countably infinite degree and every B-vertex has
      uncountable degree.  The problem asks for a characterisation of these
      graphs; the Rocq body renders "characterize" as: there exists a predicate
      on graphs that holds of exactly the (aleph_0, aleph_1)-graphs.
    Definitions: [iGraph], [iV], [iadj] - a possibly infinite simple graph as a
      Type of vertices with a symmetric irreflexive Prop-valued adjacency
      (infinite-graph-theory/theories/foundations/igraph.v);
      [i_neighbourhood x y] - y is a neighbour of x (this file, D4_unblocked.v);
      [countably_infinite_neighbourhood x] - the neighbours of x are enumerated
      by an injective surjective map from nat (D4_unblocked.v);
      [uncountable_neighbourhood x] - the neighbours of x do not inject into nat
      (D4_unblocked.v); [aleph0_aleph1_bipartition A B] and
      [aleph0_aleph1_graph G] - the bipartition conditions above
      (D4_unblocked.v).
    Notes: PROXY, and the reason the corpus leg for this row is BLOCKED.  "Find
      a characterisation" has no faithful first-order rendering: as written the
      statement is TRIVIALLY PROVABLE by instantiating [Characterized] with
      [aleph0_aleph1_graph] itself, so it has no mathematical content.  A second
      proxy: degree aleph_1 is rendered as "uncountable" rather than "exactly
      aleph_1", which agrees with the source only under the continuum
      hypothesis. *)
Definition characterizing_aleph_0_aleph_1_graphs_statement : Prop :=
  exists Characterized : iGraph -> Prop,
    forall G : iGraph, Characterized G <-> aleph0_aleph1_graph G.

Definition d_two_ended (G : iDigraph) : Prop :=
  exists r1 r2 : nat -> dV G,
    injective r1 /\ injective r2 /\
    (forall n : nat, darc (r1 n) (r1 n.+1)) /\
    (forall n : nat, darc (r2 n.+1) (r2 n)).

Definition d_tile (G : iDigraph) (A B : dV G -> Prop) : Prop :=
  (exists a : dV G, A a) /\ (exists b : dV G, B b) /\
  forall x y : dV G, A x -> B y -> darc x y \/ darc y x \/ (~ darc x y /\ ~ darc y x).

Definition d_tile_complete_bipartite_union (G : iDigraph) (A B : dV G -> Prop) : Prop :=
  d_tile A B /\
  forall x y : dV G, A x -> B y -> darc x y \/ darc y x.

(** Corpus row: opg:highly_arc_transitive_two_ended_digraphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/highly_arc_transitive_two_ended_digraphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/highly_arc_transitive_two_ended_digraphs.json
    English statement: (Open Problem Garden, "Highly arc transitive two ended
      digraphs") If G is a highly arc transitive digraph with two ends, then
      every tile of G is a disjoint union of complete bipartite graphs.  Back-
      translating the Rocq body: for every digraph G that is highly arc
      transitive, locally finite and "two-ended", and for all vertex classes A
      and B forming a "tile", every vertex of A and every vertex of B are joined
      by an arc in one direction or the other.
    Definitions: [iDigraph], [dV], [darc] - a possibly infinite irreflexive
      digraph (infinite-graph-theory/theories/conjectures/D4inf4.v);
      [highly_arc_transitive G] and [d_locally_finite G] (D4inf4.v);
      [d_two_ended G] - there are an injective forward ray and an injective
      backward ray (this file, D4_unblocked.v); [d_tile A B] and
      [d_tile_complete_bipartite_union A B] (D4_unblocked.v).
    Notes: PROXY, and the reason the corpus leg for this row is BLOCKED; three
      load-bearing defects, all recorded in meta/STATEMENT_IMPROVEMENTS.md.
      (1) [d_tile A B] is VACUOUS beyond nonemptiness: its third conjunct
      "darc x y or darc y x or (not darc x y and not darc y x)" is a classical
      tautology, so the hypothesis reduces to "A and B are both nonempty".
      (2) The conclusion renders "disjoint union of complete bipartite graphs"
      as the single complete-bipartite condition, which is strictly stronger.
      (3) [d_two_ended] only asks for one forward and one backward ray, not for
      exactly two ends.  As a result the formal statement is much stronger than
      the source and is refutable. *)
Definition highly_arc_transitive_two_ended_digraphs_statement : Prop :=
  forall G : iDigraph,
    highly_arc_transitive G ->
    d_locally_finite G ->
    d_two_ended G ->
    forall A B : dV G -> Prop,
      d_tile A B -> d_tile_complete_bipartite_union A B.


(** * Infinite.conjectures.X216 -- reconstruction rows (wave X216, 2026-09-23) *)

From GTBase Require Export base.
From Infinite Require Import foundations.igraph.
From mathcomp Require Import all_boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x216 vocabulary ***********************************************

    The carrier is [iGraph] (infinite-graph-theory/theories/foundations/
    igraph.v): a [Prop]-valued symmetric irreflexive relation on an ARBITRARY
    vertex type, with [infinite_graph] (Dedekind infiniteness) already owned
    there.  Only the two reconstruction notions of this row are new — subgraph
    embedding and hypomorphism — and both are first-order [Prop]s, so the file
    stays axiom-free.

    DELIBERATELY NOT mathcomp-classical: [classical_sets] / [cardinality] would
    give [#<=] and [countable] off the shelf, but every one of their predicates
    goes through [boolp.asbool], so a [Print Assumptions] on any lemma about
    them reports the three classical axioms.  This wave keeps the standing
    axiom-free constraint and therefore reuses igraph.v's hand-rolled
    [infinite_graph]. *)

(** [x216_embeds G H]: [G] is isomorphic to a SUBGRAPH of [H] — an injective
    map on vertices sending every edge of [G] to an edge of [H].  The subgraph
    need NOT be induced (nothing forbids extra [H]-edges between images), which
    is the reading of "isomorphic to a subgraph of" in the source, and the one
    under which the known counterexample is stated. *)
Definition x216_embeds (G H : iGraph) : Prop :=
  exists f : iV G -> iV H,
    injective f /\ forall x y : iV G, iadj x y -> iadj (f x) (f y).

(** [x216_del_iso G H v w]: the vertex-deleted graph [G - v] is isomorphic to
    [H - w].  Spelled out on the ambient vertex types (no subtypes, so no
    [eqType] is needed): a map [f] that sends the vertices other than [v] to
    vertices other than [w], injectively, onto all of them, and preserves AND
    reflects adjacency there (vertex deletion leaves an INDUCED subgraph). *)
Definition x216_del_iso (G H : iGraph) (v : iV G) (w : iV H) : Prop :=
  exists f : iV G -> iV H,
    [/\ forall x, x <> v -> f x <> w,
        forall x y, x <> v -> y <> v -> f x = f y -> x = y,
        forall y, y <> w -> exists x, x <> v /\ f x = y &
        forall x y, x <> v -> y <> v -> (iadj x y <-> iadj (f x) (f y))].

(** [x216_hypomorphic G H]: a bijection [phi] between the vertex sets such that
    deleting any vertex [v] from [G] gives a graph isomorphic to [H] with
    [phi v] deleted — the standard hypomorphism of reconstruction theory. *)
Definition x216_hypomorphic (G H : iGraph) : Prop :=
  exists phi : iV G -> iV H,
    bijective phi /\ forall v : iV G, @x216_del_iso G H v (phi v).

(** ** X216 statements *****************************************************)

(** Corpus row: bm:bm-003
    Site: https://graph-theory-ai.github.io/graph-conjectures/bm/bm-003/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/bondy_murty_reviews/bm-003.json
    English statement: (R. Halin 1970; Bondy-Murty, Appendix A, Unsolved Problem 3)
      Let G and H be two graphs with infinitely many vertices, and suppose they
      are hypomorphic: there is a bijection phi from the vertices of G to the
      vertices of H such that, for every vertex v of G, the graph obtained from
      G by deleting v is isomorphic to the graph obtained from H by deleting
      phi(v).  Then G is isomorphic to a subgraph of H, and H is isomorphic to a
      subgraph of G.
    Definitions: [iGraph], [iadj], [infinite_graph] - the Prop-level infinite
      graph carrier, its adjacency, and Dedekind infiniteness (the naturals
      inject into the vertices)
      (infinite-graph-theory/theories/foundations/igraph.v); [x216_embeds G H] -
      G is isomorphic to a (not necessarily induced) subgraph of H, i.e. an
      injective adjacency-preserving vertex map (this file, X216.v);
      [x216_del_iso G H v w] - the vertex-deleted graphs G - v and H - w are
      isomorphic, as a bijection between the two complements of the deleted
      vertices preserving and reflecting adjacency (this file, X216.v);
      [x216_hypomorphic G H] - a vertex bijection phi with G - v isomorphic to
      H - phi(v) for every v (this file, X216.v).
    Notes: STATUS DISPROVED.  Bowler, Erde, Heinig, Lehner and Pitz (2017,
      Theorem 1.6) build two hypomorphic locally finite trees of maximum degree
      3 neither of which embeds in the other, a negative answer to Halin's
      Problem 1.5.  The row is authored here as a faithful STATEMENT (a
      refutation target), not as a proof target; no refutation is committed.
      MODELLING: "infinite" is Dedekind infiniteness on BOTH graphs (the source
      says "two infinite graphs"); "isomorphic to a subgraph" is the non-induced
      containment (an isomorphism onto a subgraph), whereas the hypomorphism
      clause uses INDUCED vertex-deleted subgraphs, as in the source's own
      definition of G - v.  Nothing is said about connectivity, local finiteness
      or cardinality beyond infiniteness, so the formal row is exactly as
      general as the source (in particular the known counterexample, a pair of
      locally finite trees, is an instance of it). *)
Definition halin_hypomorphic_infinite_subgraph_statement : Prop :=
  forall G H : iGraph,
    infinite_graph G -> infinite_graph H ->
    x216_hypomorphic G H ->
    x216_embeds G H /\ x216_embeds H G.

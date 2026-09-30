(** * Hypergraph.conjectures.implications_X217 -- implication edges for wave X217

    Wave X217 (hypergraph half) has ONE node,
    [hypergraph_cop_number_sqrt_n_over_k_statement] (arxiv:2307.15512#00).

    The corpus records exactly one relation with that row as an endpoint:

      e243  arxiv:2307.15512#00  --implies-->  others:meyniels-conjecture
            (confirmed, high confidence; "In the hypergraph game, players move along
             hyperedges instead of edges.  A connected 2-uniform hypergraph is a connected
             graph, and there the game is the usual Cops and Robbers game.  The conjectured
             bound c(H) = O(sqrt(n/k)) uses an absolute implied constant.  At k = 2 it gives
             c(G) <= C sqrt(n/2) = O(sqrt n) for every connected graph, which is Meyniel's
             conjecture.")

    Its TARGET is Meyniel's conjecture, whose Rocq statement is authored CONCURRENTLY in the
    graph-theory-misc package (wave X217:graph-theory-misc, formal name
    [meyniel_cop_number_sqrt_statement]) on that package's own cops-and-robbers foundation for
    graphs.  hypergraph-theory has no Makefile dependency on graph-theory-misc and must not
    import it, so the edge CANNOT be discharged here: the target node is not in scope in this
    compilation unit.  The annotation below therefore records the edge as a CANDIDATE, citing
    the corpus relation; it claims nothing.

    What a proof would need, beyond the two statements: (i) the identification of the
    hypergraph game on a 2-uniform hypergraph with the graph game on the corresponding graph
    (a bridge between two packages' primitives -- in this package's vocabulary, [hg_link E] of
    a 2-uniform E is the adjacency of the graph whose edges are the hyperedges), and (ii) the
    constant bookkeeping [c^2 * 2 <= C^2 * n  ==>  c^2 <= C^2 * n], which is immediate.  The
    first is not available without importing the other package, so nothing is claimed here.

    This file declares the X217 implication-edge set of hypergraph-theory to be EMPTY of
    verified edges.  It is axiom-free and contains no [Theorem] / [Axiom] / [Parameter] /
    [Admitted]. *)

From GTBase Require Import base.
From Hypergraph.foundations Require Import hypergraph.
From Hypergraph.conjectures Require Import X217.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Anchor: the X217 node type-checks as a [Prop].  [Check] is a pure query: it introduces no
    constant and no assumption. *)
Check hypergraph_cop_number_sqrt_n_over_k_statement : Prop.

(* cross-package edge hypergraph_cop_number_sqrt_n_over_k_statement -> meyniel_cop_number_sqrt_statement: annotation and proof now live in atlas/theories/conjectures/implications_A1.v or A2.v (wave A1, 2026-09-24) *)

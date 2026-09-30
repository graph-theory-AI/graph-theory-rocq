(** * Infinite.conjectures.X228 -- induced-saturation rows (wave X228, 2026-09-23) *)

From GTBase Require Export base.
From mathcomp Require Import all_boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x228 vocabulary ***********************************************

    The FINITE tournament of the row is a [diGraph] carrying GTBase.common's
    [tournament] (loopless, exactly one arc between distinct vertices), so no
    finite vocabulary is re-declared here.  What is new is the COUNTABLY
    INFINITE side: a countable tournament is a boolean relation on [nat] (the
    vertex set is [nat], hence countably infinite by construction), and
    "locally finite perturbation" has no counterpart anywhere in the
    federation.  The [iGraph] carrier of
    infinite-graph-theory/theories/foundations/igraph.v is deliberately NOT used
    here: it carries a [Prop]-valued relation on an arbitrary vertex type, while
    this row needs a DECIDABLE relation on a fixed countable vertex set, which
    keeps the perturbation and the "finitely many changes at each vertex"
    clauses first-order and axiom-free. *)

(** A COUNTABLY INFINITE TOURNAMENT: an irreflexive relation on [nat] with
    exactly one arc between any two distinct vertices.  Same shape as
    GTBase.common's [tournament], transported from [diGraph] to [rel nat]. *)
Definition x228_ctournament (R : rel nat) : Prop :=
  irreflexive R /\ forall x y : nat, (x != y) = R x y (+) R y x.

(** A TRANSITIVE tournament (the linear orders; the excluded case of the row). *)
Definition x228_transitive (D : diGraph) : Prop :=
  forall x y z : D, x -- y -> y -- z -> x -- z.

(** An INDUCED COPY of the finite tournament [D] in the countable tournament
    [R]: an injective vertex map under which arcs of [D] and arcs of [R] agree
    on distinct vertices.  In tournaments containment and induced containment
    coincide, so this is the source's "induced copy of T". *)
Definition x228_induced_copy (D : diGraph) (R : rel nat) : Prop :=
  exists f : D -> nat,
    injective f /\ forall x y : D, x != y -> (x -- y) = R (f x) (f y).

(** A LOCALLY FINITE PERTURBATION of [R]: another countable tournament [R']
    that (i) differs from [R] on at least one pair — the source perturbs a
    NONEMPTY set of pairs, and without this clause the conjecture would be
    self-contradictory, since [R] itself is T-free — and (ii) differs from [R]
    at each vertex [v] on only finitely many pairs, which on [nat] is exactly
    "all sufficiently large [u] keep their arc". *)
Definition x228_lf_perturbation (R R' : rel nat) : Prop :=
  [/\ x228_ctournament R',
      (exists x y : nat, x != y /\ R x y != R' x y) &
      forall v : nat, exists N : nat, forall u : nat, N <= u -> R' v u = R v u].

(** ** X228 statements *****************************************************)

(** Corpus row: arxiv:2506.08810#03
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2506.08810__03/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2506.08810__03.json
    English statement: (Bonamy, Groenland, Johnston, Morrison, Scott,
      arXiv:2506.08810, Conjecture 24)
      Let T be a finite tournament that is not transitive.  Then there is a
      tournament S on the vertex set of the natural numbers which contains no
      induced copy of T, and such that every locally finite perturbation of S -
      every tournament on the naturals that differs from S on at least one pair
      of vertices, and at each vertex differs from S on only finitely many pairs
      - does contain an induced copy of T.
    Definitions: [tournament D] - a finite tournament: an irreflexive digraph
      with exactly one arc between any two distinct vertices
      (base/theories/common.v); [x228_transitive D] - the arc relation is
      transitive (this file, X228.v); [x228_ctournament R] - a countably
      infinite tournament, the same conditions for a relation on nat (this file,
      X228.v); [x228_induced_copy D R] - an injective map from the vertices of D
      to the naturals under which arcs of D and arcs of R agree on distinct
      vertices (this file, X228.v); [x228_lf_perturbation R R'] - R' is a
      countable tournament differing from R on at least one pair and, at each
      vertex, on only finitely many pairs (this file, X228.v).
    Notes: MODELLING.  "Countably infinite tournament" is a tournament on the
      vertex set [nat], which is countably infinite by construction, so no
      cardinality layer is needed; "T-free" and "induced copy" coincide for
      tournaments, as the source's own discussion notes.  The NONEMPTINESS
      clause of the perturbation is load-bearing and is taken from the source's
      definition (a perturbation perturbs a nonempty locally finite set of
      pairs): without it, S itself would be a perturbation of S and the
      conjecture would assert both "S is T-free" and "S contains T".  "Locally
      finite" is rendered as "at each vertex, all but finitely many arcs are
      unchanged", which on nat is "beyond some threshold N the arcs at v are
      unchanged"; this is exactly finiteness of the changed set at each vertex.
      The finite tournament T is a [diGraph], whose vertex type is a finite
      type, so "finite tournament" is structural. *)
Definition infinite_tournament_induced_saturation_statement : Prop :=
  forall D : diGraph,
    tournament D -> ~ x228_transitive D ->
    exists R : rel nat,
      [/\ x228_ctournament R,
          ~ x228_induced_copy D R &
          forall R' : rel nat,
            x228_lf_perturbation R R' -> x228_induced_copy D R'].

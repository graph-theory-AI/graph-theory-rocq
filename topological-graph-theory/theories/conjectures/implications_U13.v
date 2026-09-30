(** * Topological.conjectures.implications_U13 — milestone U13 edges

    Implication / refutation EDGES among the four U13 planar nodes
    (large induced forest; Earth–Moon; Wegner square-colouring; degenerate
    colouring), as Qed-closed RELATIVE theorems where one exists.

    OUTCOME (honest).  The four U13 rows are four MUTUALLY-INDEPENDENT famous
    open problems, grouped only by topic (planarity).  The verified-literature
    edge table of OPG_FULL_FORMALIZATION_PLAN.md §6 lists NONE of them: there is
    no textbook "A ⟹ B" between any pair.  Consequently this milestone schedules
    ZERO verified edges — there is no real [Theorem A_implies_B. Qed] to add,
    because forcing one would either fail to compile or misstate the
    mathematics.  Per the edge policy a false/unclosing edge must NOT be forced.

    The single literature-MOTIVATED direction is recorded as a CANDIDATE
    annotation only (proved=false): the degenerate-colouring conjecture's k = 2
    clause makes the union of any two colour classes 1-degenerate, i.e. an
    induced forest (this is exactly an acyclic 5-colouring).  Taking the two
    largest of the five classes yields an induced forest on ≥ 2n/5 vertices
    (Albertson–Berman / Borodin), which is STRICTLY short of the n/2 (i.e.
    [#|G| <= 2*#|S|]) demanded by [large_induced_forest_in_a_planar_graph_statement].
    The constant gap 2/5 < 1/2 is real (five equal colour classes is a witness:
    every 2-class union has exactly 2n/5 vertices), so the implication does NOT
    close as a relative theorem and the edge stays a candidate, never scheduled.
    This is the same "looks-like-an-edge but the constant is wrong" pattern as
    the §6 withdrawn edges (list-total ⟹ Behzad, list-Hadwiger ⟹ Hadwiger).

    The file is self-contained (it re-states the four U13 nodes verbatim so the
    edge endpoints are in scope) and axiom-free: no Conjecture/Axiom/Parameter/
    Admitted, and no [Theorem … Qed] asserting an unproven edge. *)

From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** U13 nodes (verbatim from Topological.conjectures.U13) *)

(** Corpus row: opg:large_induced_forest_in_a_planar_graph
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/large_induced_forest_in_a_planar_graph/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/large_induced_forest_in_a_planar_graph.json
    English statement: (Open Problem Garden, "Large induced forest in a planar graph";
      Albertson-Berman)
      Every planar graph on n vertices has an induced forest on at least n/2 vertices.  In
      this file's copy: for every predicate [is_planar] on finite simple graphs and every
      graph G satisfying it, there is a vertex set S inducing an acyclic subgraph with
      |V(G)| <= 2 * |S|.
    Definitions: [is_planar] - a universally-quantified ORACLE predicate standing for
      planarity (this file); [is_forest S] - coq-graph-theory sgraph.v.
    Notes: RE-STATED COPY.  This file re-states the four U13 nodes so that the edge
      endpoints are in scope; the header calls them verbatim copies, but they have since
      DIVERGED from topological-graph-theory/theories/conjectures/U13.v, which now uses the
      concrete [wagner_planar].  Here planarity is still the universally-quantified ORACLE
      [is_planar : sgraph -> Prop] of the pre-G2 encoding, which makes each copy STRICTLY
      STRONGER than the corresponding U13.v statement (it must hold for every predicate
      whatsoever, including degenerate ones).  See the ledger.  The file schedules ZERO
      verified edges: the four rows are mutually independent open problems and the verified
      literature table lists no implication between any pair.  The one literature-motivated
      direction is recorded as a candidate annotation only (degenerate colouring gives an
      induced forest on at least 2n/5 vertices, short of the n/2 demanded by the
      induced-forest row - the constant gap is real, so the edge does not close). *)
Definition large_induced_forest_in_a_planar_graph_statement : Prop :=
  forall (is_planar : sgraph -> Prop) (G : sgraph),
    is_planar G ->
    exists S : {set G}, is_forest S /\ (#|G| <= 2 * #|S|)%N.

Definition union_of_two_planar
    (is_planar : sgraph -> Prop) (G : sgraph) : Prop :=
  exists (e1 e2 : rel G)
         (s1 : symmetric e1) (i1 : irreflexive e1)
         (s2 : symmetric e2) (i2 : irreflexive e2),
    [/\ is_planar (SGraph s1 i1),
        is_planar (SGraph s2 i2)
      & forall x y : G, (x -- y) = e1 x y || e2 x y ].

(** Corpus row: opg:earth_moon_problem
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/earth_moon_problem/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/earth_moon_problem.json
    English statement: (Open Problem Garden, "Earth-Moon Problem"; Ringel)
      What is the maximum chromatic number of a graph that is the edge-union of two planar
      graphs on a common vertex set (equivalently, of a map in which each country has one
      region on earth and one on the moon)?  In this file's copy: for every predicate
      [is_planar], assuming at least one graph is the edge-union of two [is_planar] graphs,
      there is a number m that bounds the chromatic number of every such graph and is
      attained by one of them.
    Definitions: [is_planar] - a universally-quantified ORACLE predicate standing for
      planarity (this file); [union_of_two_planar is_planar G] - the adjacency of G is the
      disjunction of two symmetric irreflexive relations, each planar when read as an sgraph
      on the same vertex type (this file); the chromatic number is coq-graph-theory's
      [chi(A)] on the full vertex set.
    Notes: RE-STATED COPY.  This file re-states the four U13 nodes so that the edge
      endpoints are in scope; the header calls them verbatim copies, but they have since
      DIVERGED from topological-graph-theory/theories/conjectures/U13.v, which now uses the
      concrete [wagner_planar].  Here planarity is still the universally-quantified ORACLE
      [is_planar : sgraph -> Prop] of the pre-G2 encoding, which makes each copy STRICTLY
      STRONGER than the corresponding U13.v statement (it must hold for every predicate
      whatsoever, including degenerate ones).  See the ledger.  The file schedules ZERO
      verified edges: the four rows are mutually independent open problems and the verified
      literature table lists no implication between any pair.  The one literature-motivated
      direction is recorded as a candidate annotation only (degenerate colouring gives an
      induced forest on at least 2n/5 vertices, short of the n/2 demanded by the
      induced-forest row - the constant gap is real, so the edge does not close). *)
Definition earth_moon_statement : Prop :=
  forall (is_planar : sgraph -> Prop),
    (exists G0 : sgraph, union_of_two_planar is_planar G0) ->
    exists m : nat,
      (forall G : sgraph, union_of_two_planar is_planar G -> (χ([set: G]) <= m)%N)
   /\ (exists G : sgraph, union_of_two_planar is_planar G /\ χ([set: G]) = m).

(** Corpus row: opg:colouring_the_square_of_a_planar_graph
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/colouring_the_square_of_a_planar_graph/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/colouring_the_square_of_a_planar_graph.json
    English statement: (Open Problem Garden, "Colouring the square of a planar graph";
      Wegner's conjecture)
      For every planar graph G with at least one vertex and maximum degree D, the chromatic
      number of the square of G is at most 7 when D = 3, at most D + 5 when 4 <= D <= 7, and
      at most floor(3D/2) + 1 when D >= 8.  This file's copy states the same three-regime
      conjunction with planarity replaced by an oracle predicate.
    Definitions: [is_planar] - a universally-quantified ORACLE predicate standing for
      planarity (this file); [Delta G] and [graph_power G 2] (the square) -
      base/theories/base.v; [chi(A)] - coq-graph-theory colouring.
    Notes: RE-STATED COPY.  This file re-states the four U13 nodes so that the edge
      endpoints are in scope; the header calls them verbatim copies, but they have since
      DIVERGED from topological-graph-theory/theories/conjectures/U13.v, which now uses the
      concrete [wagner_planar].  Here planarity is still the universally-quantified ORACLE
      [is_planar : sgraph -> Prop] of the pre-G2 encoding, which makes each copy STRICTLY
      STRONGER than the corresponding U13.v statement (it must hold for every predicate
      whatsoever, including degenerate ones).  See the ledger.  The file schedules ZERO
      verified edges: the four rows are mutually independent open problems and the verified
      literature table lists no implication between any pair.  The one literature-motivated
      direction is recorded as a candidate annotation only (degenerate colouring gives an
      induced forest on at least 2n/5 vertices, short of the n/2 demanded by the
      induced-forest row - the constant gap is real, so the edge does not close). *)
Definition colouring_the_square_of_a_planar_graph_statement : Prop :=
  forall (is_planar : sgraph -> Prop) (G : sgraph),
    is_planar G -> (0 < #|G|)%N ->
    [/\ ( Delta G = 3 -> (χ([set: graph_power G 2]) <= 7)%N ),
        ( (4 <= Delta G)%N -> (Delta G <= 7)%N ->
            (χ([set: graph_power G 2]) <= Delta G + 5)%N )
      & ( (8 <= Delta G)%N ->
            (χ([set: graph_power G 2]) <= (3 * Delta G)./2 + 1)%N ) ].

Definition k_degenerate_on (G : sgraph) (W : {set G}) (k : nat) : Prop :=
  forall S : {set G},
    S \subset W -> S != set0 ->
    exists x : G, x \in S /\ (#|N(x) :&: S| <= k)%N.

Definition k_degenerate (G : sgraph) (k : nat) : Prop :=
  k_degenerate_on [set: G] k.
Arguments k_degenerate_on {G} W k.

(** Corpus row: opg:degenerate_colorings_of_planar_graphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/degenerate_colorings_of_planar_graphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/degenerate_colorings_of_planar_graphs.json
    English statement: (Open Problem Garden, "Degenerate colorings of planar graphs")
      Every simple planar graph has a 5-colouring such that for every k between 1 and 4 the
      union of any k colour classes induces a (k-1)-degenerate graph.  In this file's copy:
      for every predicate [is_planar] and every graph G satisfying it there is a proper
      colouring col by five colours such that for every palette T of between 1 and 4 colours
      the vertex set {v : col v in T} is (|T| - 1)-degenerate.
    Definitions: [is_planar] - a universally-quantified ORACLE predicate standing for
      planarity (this file); [k_degenerate_on W k] - every non-empty subset of W has a vertex
      with at most k neighbours inside it, re-declared locally here although it now lives in
      base/theories/base.v (see the ledger).
    Notes: RE-STATED COPY.  This file re-states the four U13 nodes so that the edge
      endpoints are in scope; the header calls them verbatim copies, but they have since
      DIVERGED from topological-graph-theory/theories/conjectures/U13.v, which now uses the
      concrete [wagner_planar].  Here planarity is still the universally-quantified ORACLE
      [is_planar : sgraph -> Prop] of the pre-G2 encoding, which makes each copy STRICTLY
      STRONGER than the corresponding U13.v statement (it must hold for every predicate
      whatsoever, including degenerate ones).  See the ledger.  The file schedules ZERO
      verified edges: the four rows are mutually independent open problems and the verified
      literature table lists no implication between any pair.  The one literature-motivated
      direction is recorded as a candidate annotation only (degenerate colouring gives an
      induced forest on at least 2n/5 vertices, short of the n/2 demanded by the
      induced-forest row - the constant gap is real, so the edge does not close). *)
Definition degenerate_colorings_of_planar_graphs_statement : Prop :=
  forall (is_planar : sgraph -> Prop) (G : sgraph),
    is_planar G ->
    exists col : G -> 'I_5,
      (forall x y : G, x -- y -> col x != col y)
   /\ (forall T : {set 'I_5},
         (1 <= #|T|)%N -> (#|T| <= 4)%N ->
         k_degenerate_on [set v : G | col v \in T] (#|T| - 1)).

(** ** Edges

    No verified-literature edge exists among the four nodes (plan §6 lists
    none).  The only literature-motivated direction is a CANDIDATE blocked by a
    constant gap, recorded as an annotation only — there is no Qed theorem for
    it because it does not logically close. *)

(*@EDGE from=degenerate_colorings_of_planar_graphs_statement to=large_induced_forest_in_a_planar_graph_statement kind=implies status=refuted-direction cite="Albertson & Berman 1979 (induced-forest conj.); Borodin 1979 (acyclic 5-colouring of planar graphs)" note="REFUTED-DIRECTION (metadata wave M, 2026-09-24): strict weakening: the best 2-class union gives 2n/5 < n/2 (five equal classes show 2/5 is unimprovable by this route). Earlier note: k=2 clause: union of any two of the five colour classes is 1-degenerate, i.e. an induced forest (acyclic colouring). Largest 2-class union has only >= 2n/5 vertices, strictly short of the n/2 (#|G| <= 2*#|S|) required by the target. Five equal classes is a witness that 2/5 cannot be improved by this argument, so the edge does NOT close; candidate, never scheduled." *)

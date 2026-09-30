(** * Digraph.conjectures.classic_core — P9 "classic digraph core"

    The cheapest-to-state, highest-fame open digraph conjectures: they need only a few
    new primitives on top of the existing core (out-degree, directed cycles).
    See docs/CONJECTURES_FORMALIZATION_PLAN.md §4 (P9), §5.

    New primitives (digraph level, mirroring [outdeg]):
      - [Nout v] / [Nin v]      : out- / in-neighbourhood sets
      - [indeg v]               : in-degree (the lib had [N_in] only for tournaments)
      - [Nout2 v]               : second out-neighbourhood (directed distance exactly 2)
      - [diregular d]           : in-degree = out-degree = d at every vertex

    Nodes (Definitions of type Prop):
      - [seymour_second_neighbourhood_statement] : every oriented graph has a vertex v
            with |N⁺⁺(v)| ≥ |N⁺(v)|  (Seymour's Second Neighbourhood Conjecture).
      - [caccetta_haggkvist_statement]           : a loopless digraph with min out-degree
            ≥ r has a directed cycle of length ≤ ⌈n/r⌉  (Caccetta–Häggkvist).
      - [caccetta_haggkvist_triangle_statement]  : an oriented graph with min out-degree
            ≥ n/3 has a directed triangle  (the famous CH triangle case). *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented dipath strong.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** New degree / neighbourhood primitives (general digraph level) *)

Section Degrees.
Variable D : diGraphType.
Implicit Types (v w : D).

Definition Nout v : {set D} := [set w | v --> w].
Definition Nin  v : {set D} := [set u | u --> v].

(** In-degree (companion of [outdeg], which is [#|Nout v|] by definition). *)
Definition indeg v : nat := #|Nin v|.

(** Second out-neighbourhood: vertices at directed distance exactly two from [v]
    (an out-neighbour of an out-neighbour, distinct from [v] and not itself an
    out-neighbour). *)
Definition Nout2 v : {set D} :=
  [set w | [&& w != v, w \notin Nout v & [exists u, (u \in Nout v) && (u --> w)]]].

(** Diregular of degree [d]: every vertex has in-degree and out-degree exactly [d]. *)
Definition diregular (d : nat) : bool := [forall v, (outdeg v == d) && (indeg v == d)].

End Degrees.

(** ** Oriented girth ≥ 3 (reusable)

    An oriented graph has no loops (irreflexive) and no digons (asymmetric), so every
    directed cycle has length at least 3. This is the crux of the eventual
    Caccetta–Häggkvist ⟹ triangle edge (a CH cycle of length ≤ 3 in an oriented graph
    must be exactly a triangle). *)
Lemma oriented_dicycle_size_ge3 (D : orientedDigraph) (c : seq D) :
  dicycle c -> 3 <= size c.
Proof.
move=> /and3P[cn cc cu]; case: c cn cc cu => [|x [|y [|z t]]] //=.
- by move=> _; rewrite andbT arc_irrefl.
- by move=> _ /and3P[axy ayx _]; rewrite (arc_asymm _ _ axy) in ayx.
Qed.

(** ** Seymour's Second Neighbourhood Conjecture *)

(** Corpus row: opg:seymours_second_neighbourhood_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/seymours_second_neighbourhood_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/seymours_second_neighbourhood_conjecture.json
    English statement: (Open Problem Garden, Seymour's Second Neighbourhood Conjecture)
      Every finite oriented graph D with at least one vertex has a vertex v whose second
      out-neighbourhood is at least as large as its out-neighbourhood, that is outdeg v <=
      |Nout2 v|.
    Definitions: [orientedDigraph] - a finite digraph whose arc relation is irreflexive and
      asymmetric, so no loops and no digons (core/oriented.v); [outdeg v] - the number of
      out-neighbours of v (core/oriented.v); [Nout2 v] - the second out-neighbourhood of v, the
      vertices w distinct from v, not out-neighbours of v, that are out-neighbours of an
      out-neighbour of v (this file).
    Notes: The guard 0 < #|D| rules out the empty digraph, where no vertex exists and the
      existential would be unsatisfiable. *)
Definition seymour_second_neighbourhood_statement : Prop :=
  forall D : orientedDigraph,
    (0 < #|D|)%N -> exists v : D, (outdeg v <= #|Nout2 v|)%N.

(** ** Caccetta–Häggkvist Conjecture *)

(** Corpus row: opg:caccetta_haggkvist_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/caccetta_haggkvist_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/caccetta_haggkvist_conjecture.json
    English statement: (Open Problem Garden, Caccetta-Haggkvist Conjecture)
      For every finite digraph D with at least one vertex and no loops, and every r >= 1, if
      every vertex has out-degree at least r then D has a directed cycle with at most
      ceiling(n/r) vertices, where n is the number of vertices; the ceiling is written in
      natural-number arithmetic as (n + r - 1) divided by r.
    Definitions: [dicycle c] - c is a nonempty duplicate-free vertex sequence that is a directed
      cycle (core/dipath.v); [outdeg v] - out-degree (core/oriented.v).
    Notes: The corpus says simple digraph; here simplicity is the looplessness hypothesis forall
      v, ~~ (v --> v), parallel arcs being impossible because arcs are a relation on vertices.
      The cycle length is counted in vertices (size c). *)
Definition caccetta_haggkvist_statement : Prop :=
  forall (D : diGraphType) (r : nat),
    (0 < #|D|)%N -> (forall v : D, ~~ (v --> v)) -> (0 < r)%N ->
    (forall v : D, (r <= outdeg v)%N) ->
    exists c : seq D, dicycle c /\ (size c <= (#|D| + r - 1) %/ r)%N.

(** No corpus row: the famous triangle case (n <= 3 * outdeg at every vertex forces a directed
    triangle) of opg:caccetta_haggkvist_conjecture, kept as a separate node so the implication
    edges of this folder can be stated; the corpus row is documented on
    [caccetta_haggkvist_statement] above. *)
Definition caccetta_haggkvist_triangle_statement : Prop :=
  forall D : orientedDigraph,
    (0 < #|D|)%N -> (forall v : D, (#|D| <= 3 * outdeg v)%N) ->
    exists c : seq D, dicycle c /\ size c = 3.

(** ** Long directed cycles in diregular digraphs (Bermond–Germa–Heydemann–Sotteau) *)

(** Corpus row: opg:long_directed_cycles_in_digraph_with_minimum_in_and_out_degree
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/long_directed_cycles_in_digraph_with_minimum_in_and_out_degree/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/long_directed_cycles_in_digraph_with_minimum_in_and_out_degree.json
    English statement: (Open Problem Garden, Long directed cycles in diregular digraphs (Bermond-Germa-Heydemann-Sotteau))
      For every finite oriented graph D with at least one vertex and every d >= 1, if D is
      strongly connected and every vertex has in-degree at least d and out-degree at least d,
      then D has a directed cycle with at least 2d+1 vertices.
    Definitions: [orientedDigraph] - finite digraph with irreflexive asymmetric arc relation
      (core/oriented.v); [strongb] - strong connectivity, every vertex reaches every other along
      arcs (invariants/strong.v); [indeg v] - in-degree (this file); [outdeg v] - out-degree
      (core/oriented.v); [dicycle c] - directed cycle as a duplicate-free vertex sequence
      (core/dipath.v).
    Notes: The bound is on the number of vertices of the cycle (size c). *)
Definition long_dicycle_diregular_statement : Prop :=
  forall (D : orientedDigraph) (d : nat),
    (0 < #|D|)%N -> (0 < d)%N -> strongb D ->
    (forall v : D, (d <= indeg v)%N) -> (forall v : D, (d <= outdeg v)%N) ->
    exists c : seq D, dicycle c /\ (2 * d + 1 <= size c)%N.

(** ** Hamilton cycle in small diregular oriented graphs (Jackson) *)

(** No corpus row: the corpus row opg:hamilton_cycle_in_small_d_diregular_graphs is carried by
    [hamilton_cycle_in_small_d_diregular_graphs_statement] in conjectures/P9.v, which is defined
    as an alias of this statement (Jackson: for d > 2, every d-diregular oriented graph on at
    most 4d+1 vertices has a directed cycle through every vertex). *)
Definition jackson_hamilton_small_diregular_statement : Prop :=
  forall (D : orientedDigraph) (d : nat),
    (0 < #|D|)%N -> 2 < d -> diregular D d -> (#|D| <= 4 * d + 1)%N ->
    exists c : seq D, dicycle c /\ size c = #|D|.

(** ** Splitting a digraph under minimum-out-degree constraints (Alon) *)

(** Corpus row: opg:splitting_a_digraph_with_minimum_outdegree_constraints
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/splitting_a_digraph_with_minimum_outdegree_constraints/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/splitting_a_digraph_with_minimum_outdegree_constraints.json
    English statement: (Open Problem Garden, Splitting a digraph with minimum outdegree constraints (Alon))
      There is a function f from naturals to naturals such that for every natural d and every
      finite digraph D in which every vertex has out-degree at least f(d), the vertex set of D
      splits into a set V1 and its complement, both nonempty, such that every vertex of V1 has
      at least d out-neighbours inside V1 and every vertex outside V1 has at least d
      out-neighbours outside V1.
    Definitions: [outdeg_in A v] - the number of out-neighbours of v lying in A, i.e. the
      out-degree of v in the subdigraph induced by A (core/oriented.v).
    Notes: Both parts are required to be nonempty. Without that guard, V1 := setT satisfies the
      complement clause vacuously and the statement is trivially true, so the guard is a
      deliberate (and standard) reading of partitioned into two classes. The corpus text writes
      the hypothesis degree as d rather than f(d); the Rocq body uses the standard reading in
      which the existential function f gives the forcing degree and d is the degree demanded
      inside each class. *)
Definition splitting_min_outdegree_statement : Prop :=
  exists f : nat -> nat,
    forall (D : diGraphType) (d : nat),
      (forall v : D, (f d <= outdeg v)%N) ->
      exists V1 : {set D},
        [/\ (* a PROPER bipartition: both parts nonempty (without this, V1 := setT makes
               the complement-side constraint vacuous, trivializing the statement) *)
            V1 != set0,
            V1 != [set: D],
            (forall v : D, v \in V1 -> (d <= outdeg_in V1 v)%N)
          & (forall v : D, v \notin V1 -> (d <= outdeg_in (~: V1) v)%N)].

(** ** Stable set meeting all longest directed paths (Laborde–Payan–Xuong) *)

(** A [stable] (independent) set has no arc between any two of its members. *)
Definition stable (D : diGraphType) (S : {set D}) : bool :=
  [forall u in S, [forall v in S, ~~ (u --> v)]].

(** Corpus row: opg:stable_set_meeting_all_longest_directed_paths
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/stable_set_meeting_all_longest_directed_paths/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/stable_set_meeting_all_longest_directed_paths.json
    English statement: (Open Problem Garden, Stable set meeting all longest directed paths (Laborde-Payan-Xuong))
      Every finite digraph D has a stable vertex set S, that is a set with no arc between any
      two of its members, such that every longest directed path of D contains a vertex of S; a
      directed path is longest when its number of arcs equals ell(D), the maximum number of arcs
      of a directed path of D.
    Definitions: [stable S] - no arc joins two members of S, loops inside S included (this
      file); [dipath x s] - x :: s is a duplicate-free vertex sequence following arcs
      (core/dipath.v); [ell D] - the maximum number of arcs of a directed path of D
      (core/dipath.v).
    Notes: Path length is counted in arcs (size s), so a single vertex is a path of length 0; on
      a digraph with no arcs ell D = 0 and the condition is that S meets every vertex, forcing S
      = setT, which is stable there. *)
Definition stable_meeting_longest_dipaths_statement : Prop :=
  forall D : diGraphType,
    exists S : {set D}, stable S /\
      forall (x : D) (s : seq D), dipath x s -> size s = ell D ->
        exists2 v : D, v \in S & v \in x :: s.

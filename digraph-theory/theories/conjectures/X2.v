(** * Digraph.conjectures.X2 -- v2 milestone X2, clean arXiv statement wave

    This file states the first clean X2 batch: the eleven open arXiv rows whose
    statements are self-contained enough to author before the bounded /
    needs-primitive followups.  The missing-statement row arXiv:2602.16333#03
    is intentionally not represented here. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude interop_graph_theory digraph oriented dipath tournament.
From Digraph Require Import automorphism domination strong.
From Digraph Require Import classic_core heroes chi_bounded dichromatic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Generic embeddings and directed subdivisions **************************)

(** Non-induced subdigraph containment: arcs of [H] are preserved injectively in
    [D].  This is the containment notion for path/tree appearances, distinct from
    [heroes.ind_subdigraph], which is induced. *)
Definition subdigraph_embed (H D : diGraphType) : Prop :=
  exists f : H -> D, injective f /\ forall u v : H, u --> v -> f u --> f v.

Section SubdivisionModel.
Variables (F D : diGraphType) (branch : F -> D).

Definition x2_path_vertices (x : D) (s : seq D) : {set D} :=
  [set y | y \in x :: s].

Definition x2_branch_set : {set D} :=
  [set y | [exists x : F, branch x == y]].

Definition x2_path_internal (u v : F) (s : seq D) : {set D} :=
  x2_path_vertices (branch u) s :\: [set branch u; branch v].

End SubdivisionModel.

(** A subdivision model maps each vertex of [F] to a branch vertex of [D] and
    replaces every arc [u -> v] of [F] by a directed path from [u]'s branch to
    [v]'s branch.  The internal vertices of all replacement paths are
    vertex-disjoint and avoid every branch vertex. *)
Definition contains_subdivision (F D : diGraphType) : Prop :=
  exists branch : F -> D,
    injective branch /\
    exists paths : F -> F -> seq D,
      (forall u v : F, u --> v ->
        [/\ (0 < size (paths u v))%N,
            dipath (branch u) (paths u v),
            last (branch u) (paths u v) = branch v
          & [disjoint x2_path_internal branch u v (paths u v)
             & x2_branch_set branch]]) /\
      (forall u v x y : F, u --> v -> x --> y ->
        ((u != x) || (v != y)) ->
        [disjoint x2_path_internal branch u v (paths u v)
         & x2_path_internal branch x y (paths x y)]).

Definition min_outdegree_at_least (D : diGraphType) (m : nat) : Prop :=
  forall v : D, (m <= outdeg v)%N.

Definition min_semidegree_at_least (D : diGraphType) (m : nat) : Prop :=
  forall v : D, (m <= outdeg v)%N /\ (m <= indeg v)%N.

(** The host [D] is guarded by [0 < #|D|]: see the GUARD REPAIR notes of the two
    rows below.  A pointwise minimum-degree condition is satisfied VACUOUSLY by the
    empty digraph, which contains no subdivision of a nonempty [F], so without the
    guard no [m] is ever a bound and both rows are refutable. *)
Definition mader_delta_plus_bound (F : diGraphType) (m : nat) : Prop :=
  forall D : diGraphType, (0 < #|D|)%N ->
    min_outdegree_at_least D m -> contains_subdivision F D.

Definition mader_delta_zero_bound (F : diGraphType) (m : nat) : Prop :=
  forall D : diGraphType, (0 < #|D|)%N ->
    min_semidegree_at_least D m -> contains_subdivision F D.

Definition delta_plus_maderian (F : diGraphType) : Prop :=
  exists m : nat, mader_delta_plus_bound F m.

Definition least_mader_delta_zero (F : diGraphType) (m : nat) : Prop :=
  mader_delta_zero_bound F m /\
  forall c : nat, mader_delta_zero_bound F c -> (m <= c)%N.

(** Corpus row: arxiv:1610.00876#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1610.00876__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1610.00876__00.json
    English statement: (Aboulker, Cohen, Havet, Lochet, Moura, Thomasse 2016, Subdivisions in digraphs of large out-degree or large dichromatic number, arXiv:1610.00876, Conjecture 3)
      For every k there is a LEAST natural number m such that every finite NON-EMPTY digraph
      whose minimum semidegree (the smaller of its minimum in-degree and its minimum out-degree)
      is at least m contains a subdivision of the transitive tournament on k vertices.
    Definitions: [contains_subdivision F D] - there are injective branch vertices in D and, for
      every arc u -> v of F, a nonempty directed path from the branch vertex of u to that of v
      whose internal vertices avoid every branch vertex and are disjoint from the internal
      vertices of every other replacement path (this file); [min_outdegree_at_least D m] and
      [min_semidegree_at_least D m] - every out-degree, resp. every out-degree and every
      in-degree, is at least m (this file); [mader_delta_zero_bound F m] - every NON-EMPTY
      digraph of minimum semidegree at least m contains a subdivision of F (this file);
      [least_mader_delta_zero F m] - m is such a bound and is minimal among them (this file);
      [TT k] - the transitive tournament on k vertices (core/tournament.v); [indeg]
      (conjectures/classic_core.v); [outdeg] (core/oriented.v).
    Notes: The corpus phrase there exists a least integer mader is encoded literally by the
      minimality clause of [least_mader_delta_zero], so the content is that SOME finite bound
      exists (a least one then exists by well-ordering).
      GUARD REPAIR (2026-09-24, wave E4): [mader_delta_zero_bound] now guards its host by
      0 < #|D|. Without that guard the row is FALSE for every k >= 1, refuted by the EMPTY
      digraph: [min_semidegree_at_least D m] is a pointwise condition, so it holds VACUOUSLY on a
      digraph with no vertex, while [contains_subdivision (TT k) D] needs an injective branch map
      out of the nonempty TT k; hence no m is a bound at all (wave-E3 scratch refutation
      degeneracy.v: X2_mader_delta0_false, kept in the wave report, not committed). The paper
      quantifies over digraphs of minimum semidegree at least mader, i.e. over digraphs that HAVE
      vertices of that degree; the guard excludes exactly the vertexless degenerate host that the
      pointwise encoding admits, and nothing else. Teeth and non-vacuity:
      grounding_X2.v (x2_delta0_unguarded_false, x2_delta0_hyps_nonvacuous). *)
Definition mader_delta0_transitive_tournament_statement : Prop :=
  forall k : nat, exists m : nat, least_mader_delta_zero (TT k) m.

Definition oriented_tree (F : orientedDigraph) : Prop :=
  [/\ (0 < #|F|)%N,
      chi_bounded.oriented_dg F,
      is_forest [set: chi_bounded.underlying F]
    & connected [set: chi_bounded.underlying F]].

(** Corpus row: arxiv:1610.00876#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1610.00876__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1610.00876__01.json
    English statement: (Aboulker, Cohen, Havet, Lochet, Moura, Thomasse 2016, Subdivisions in digraphs of large out-degree or large dichromatic number, arXiv:1610.00876, Conjecture 4)
      Every oriented tree F, that is every nonempty orientation of a tree, is
      delta-plus-maderian: there is a natural number m such that every finite NON-EMPTY digraph
      of minimum out-degree at least m contains a subdivision of F.
    Definitions: [contains_subdivision F D] - there are injective branch vertices in D and, for
      every arc u -> v of F, a nonempty directed path from the branch vertex of u to that of v
      whose internal vertices avoid every branch vertex and are disjoint from the internal
      vertices of every other replacement path (this file); [min_outdegree_at_least D m] and
      [min_semidegree_at_least D m] - every out-degree, resp. every out-degree and every
      in-degree, is at least m (this file); [delta_plus_maderian F] - some minimum out-degree
      bound forces a subdivision of F in every NON-EMPTY host (this file); [oriented_tree F] - nonempty, asymmetric arc
      relation, and underlying simple graph both a forest and connected (this file);
      [chi_bounded.underlying] and [chi_bounded.oriented_dg] (conjectures/chi_bounded.v);
      [is_forest] and [connected] (coq-graph-theory).
    Notes: Being a tree is stated as forest plus connected on the underlying simple graph, which
      avoids counting arcs.
      GUARD REPAIR (2026-09-24, wave E4): [mader_delta_plus_bound] now guards its host by
      0 < #|D|, for the same reason as row arxiv:1610.00876#00: the EMPTY digraph satisfies the
      pointwise [min_outdegree_at_least D m] vacuously for every m and contains no subdivision of
      a nonempty F, so without the guard the row is FALSE already for the one-vertex oriented tree
      (wave-E3 scratch refutation degeneracy.v: X2_trees_delta_plus_false, kept in the wave
      report, not committed). Mader's conjecture speaks of digraphs of large minimum out-degree,
      which have vertices; the guard removes exactly the vertexless host. Teeth and non-vacuity:
      grounding_X2.v (x2_delta_plus_unguarded_false, x2_delta_plus_hyps_nonvacuous,
      x2_oriented_tree_TT2). *)
Definition oriented_trees_delta_plus_maderian_statement : Prop :=
  forall F : orientedDigraph, oriented_tree F -> delta_plus_maderian F.

Section DisjointUnion.
Variables D1 D2 : diGraphType.

Definition x2_disjoint_union : Type := (D1 + D2)%type.
HB.instance Definition _ := Finite.on x2_disjoint_union.

Definition x2_disjoint_union_rel (x y : D1 + D2) : bool :=
  match x, y with
  | inl a, inl b => a --> b
  | inr a, inr b => a --> b
  | _, _ => false
  end.

HB.instance Definition _ := HasArc.Build x2_disjoint_union x2_disjoint_union_rel.

End DisjointUnion.

(** Corpus row: arxiv:1610.00876#02
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1610.00876__02/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1610.00876__02.json
    English statement: (Aboulker, Cohen, Havet, Lochet, Moura, Thomasse 2016, Subdivisions in digraphs of large out-degree or large dichromatic number, arXiv:1610.00876, Conjecture 7)
      If two finite digraphs F1 and F2 are both delta-plus-maderian (each has a minimum
      out-degree bound forcing a subdivision of it), then their disjoint union is
      delta-plus-maderian too.
    Definitions: [delta_plus_maderian F] (this file); [x2_disjoint_union D1 D2] - the digraph on
      the sum type whose arcs are the arcs of D1 and of D2, with no arc between the two sides
      (this file).
    Notes: The body is unchanged by the wave-E4 guard repair, but it inherits it through
      [delta_plus_maderian]: the hosts are now the NON-EMPTY digraphs of minimum out-degree at
      least m. The repair strictly strengthens this row - with the unguarded notion
      [delta_plus_maderian F] is false for every nonempty F, so the implication was vacuously
      true. *)
Definition delta_plus_maderian_disjoint_union_statement : Prop :=
  forall F1 F2 : diGraphType,
    delta_plus_maderian F1 -> delta_plus_maderian F2 ->
    delta_plus_maderian (x2_disjoint_union F1 F2).

(** ** Dominating-number tournament problems *******************************)

Fixpoint Si_tournament (i : nat) : diGraphType -> Prop :=
  match i with
  | 0 => fun _ => False
  | i'.+1 =>
      match i' with
      | 0 => fun S => dgiso S K1
      | _ => fun S => exists P : diGraphType,
          Si_tournament i' P /\ dgiso S (c3sub P P K1)
      end
  end.

Definition contains_Si (T : tournament) (i : nat) : Prop :=
  exists S : diGraphType, Si_tournament i S /\ ind_subdigraph S T.

(** Corpus row: arxiv:1702.01607#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1702.01607__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1702.01607__00.json
    English statement: (Harutyunyan, Le, Thomasse, Wu 2017, Coloring tournaments: from local to global, arXiv:1702.01607, Problem 3)
      For every i >= 1 there is a bound f such that every finite tournament whose domination
      number is at least f contains a copy of the tournament S_i as an induced subdigraph, where
      S_1 is a single vertex and S_{i+1} is obtained from a directed triangle by blowing up two
      of its vertices into copies of S_i.
    Definitions: [Si_tournament i S] - S is isomorphic to the i-th member of the family, built
      recursively with [c3sub P P K1] (this file); [contains_Si T i] - some such S embeds into T
      as an INDUCED subdigraph (this file); [ind_subdigraph] - injective map preserving and
      reflecting arcs (conjectures/heroes.v); [domnum T] - the directed domination number, the
      least size of a set dominating every vertex (invariants/domination.v); [dgiso]
      (core/digraph.v); [K1] and [c3sub] (core/tournament.v and constructions).
    Notes: The corpus says isomorphic copy; the body uses INDUCED containment, which for a
      subtournament of a tournament is the same thing, every pair of vertices carrying exactly
      one arc. The bound f depends on i only, as in the corpus. *)
Definition large_domination_contains_Si_statement : Prop :=
  forall i : nat, (1 <= i)%N ->
    exists f : nat,
      forall T : tournament, (f <= domnum T)%N -> contains_Si T i.

(** Corpus row: arxiv:1702.01607#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1702.01607__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1702.01607__01.json
    English statement: (Harutyunyan, Le, Thomasse, Wu 2017, Coloring tournaments: from local to global, arXiv:1702.01607, Problem 4)
      For every k >= 1 there are bounds K and ell such that every finite tournament whose
      domination number is at least K has a vertex set of size exactly ell inducing a
      subtournament with domination number at least k.
    Definitions: [domnum T] - directed domination number (invariants/domination.v);
      [sub_tournament S] - the subtournament induced by S (core/tournament.v).
    Notes: The size of the witness is pinned to exactly ell, which is the corpus reading (a
      subtournament with ell vertices); the existential over both K and ell is inside the
      quantifier on k. *)
Definition large_domination_contains_large_dom_subtournament_statement : Prop :=
  forall k : nat, (1 <= k)%N ->
    exists K ell : nat,
      forall T : tournament, (K <= domnum T)%N ->
        exists S : {set T},
          #|S| = ell /\ (k <= domnum (sub_tournament S))%N.

(** ** Directed Kneser existence ********************************************)

Definition bsubset (k b : nat) := {S : {set 'I_k} | #|S| == b}.

Section KneserDigraph.
Variables (k b : nat) (R : rel (bsubset k b)).

Definition kneser_digraph : Type := bsubset k b.
HB.instance Definition _ := Finite.on kneser_digraph.
HB.instance Definition _ := HasArc.Build kneser_digraph R.

Definition common_intersection_nonempty (X : {set kneser_digraph}) : Prop :=
  exists i : 'I_k, forall B : kneser_digraph, B \in X -> i \in val B.

Definition directed_kneser_property : Prop :=
  forall X : {set kneser_digraph},
    acyclicb (induced_digraph X) <-> common_intersection_nonempty X.

End KneserDigraph.

(** Corpus row: arxiv:1812.02420#03
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1812.02420__03/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1812.02420__03.json
    English statement: (Hochstattler, Schroder, Steiner 2018, On the Complexity of Digraph Colourings and Vertex Arboricity, arXiv:1812.02420, Problem 5.40)
      For all k and b with 0 < b <= k there is an arc relation on the b-element subsets of a
      k-element set such that, for every family X of b-element subsets, the subdigraph induced
      by X is acyclic if and only if the members of X have a common element.
    Definitions: [bsubset k b] - the b-element subsets of 'I_k as a finite type (this file);
      [kneser_digraph] - that type equipped with a given arc relation R (this file);
      [common_intersection_nonempty X] - some index lies in every member of X (this file);
      [directed_kneser_property R] - the acyclic-iff-intersecting equivalence (this file);
      [acyclicb] (conjectures/dichromatic.v); [induced_digraph] (core/digraph.v).
    Notes: The guard 0 < b makes k positive, which is needed for the empty family: the empty
      induced subdigraph is acyclic, so the equivalence forces the existence of an index,
      vacuously contained in every member. The corpus asks the question; the body encodes the
      affirmative answer. *)
Definition directed_kneser_existence_statement : Prop :=
  forall k b : nat, (0 < b)%N -> (b <= k)%N ->
    exists R : rel (bsubset k b), directed_kneser_property R.

(** ** Same-vertex graph/tournament local chromatic questions ***************)

Definition x2_sgraph (T : finType) (E : rel T)
    (Esym : symmetric E) (Eirr : irreflexive E) : sgraph :=
  SGraph Esym Eirr.

Section X2InducedSGraph.
Variables (T : finType) (E : rel T)
          (Esym : symmetric E) (Eirr : irreflexive E) (S : {set T}).

Definition x2_induced_rel (x y : {x : T | x \in S}) : bool :=
  E (val x) (val y).

Lemma x2_induced_sym : symmetric x2_induced_rel.
Proof. by move=> x y; rewrite /x2_induced_rel Esym. Qed.

Lemma x2_induced_irrefl : irreflexive x2_induced_rel.
Proof. by move=> x; rewrite /x2_induced_rel Eirr. Qed.

Definition x2_induced_sgraph : sgraph :=
  SGraph x2_induced_sym x2_induced_irrefl.

End X2InducedSGraph.

Definition sg_degeneracy_at_least (G : sgraph) (d : nat) : Prop :=
  exists S : {set G},
    S != set0 /\ forall x : G, x \in S -> (d <= #|N(x) :&: S|)%N.

Definition sg_has_cycle (G : sgraph) : Prop :=
  exists c : seq G, ucycle (--) c /\ (2 < size c)%N.

(** Corpus row: arxiv:2305.15585#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2305.15585__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2305.15585__00.json
    English statement: (Girao, Hendrey, Illingworth, Lehner, Michel, Savery, Steiner 2023, Chromatic number is not tournament-local, arXiv:2305.15585, Question 10)
      For every d there is a bound C such that for every finite tournament T and every simple
      graph G on the same vertex set, if the chromatic number of G is at least C then some
      vertex v of T has the property that the subgraph of G induced by the out-neighbourhood of
      v in T has degeneracy at least d, that is contains a nonempty vertex set in which every
      vertex has at least d neighbours.
    Definitions: [x2_sgraph Esym Eirr] - the simple graph on the tournament's vertices given by
      a symmetric irreflexive relation E (this file); [x2_induced_sgraph Esym Eirr S] - its
      subgraph induced by S (this file); [sg_degeneracy_at_least G d] - some nonempty set has
      minimum degree at least d inside itself (this file); [N_out v] - the out-neighbourhood of
      v in the tournament (core/tournament.v); [chi] - coq-graph-theory's chromatic number.
    Notes: The graph and the tournament are made to share a vertex set by putting both
      structures on the same carrier: the tournament is the object T and the graph is built from
      an arbitrary symmetric irreflexive relation E on T. Degeneracy at least d is stated in the
      equivalent form having a subgraph of minimum degree at least d. *)
Definition tournament_outneighborhood_degeneracy_statement : Prop :=
  forall d : nat, exists C : nat,
    forall (T : tournament) (E : rel T)
           (Esym : symmetric E) (Eirr : irreflexive E),
      (C <= χ([set: x2_sgraph Esym Eirr]))%N ->
      exists v : T,
        sg_degeneracy_at_least
          (x2_induced_sgraph Esym Eirr (N_out v)) d.

(** Corpus row: arxiv:2305.15585#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2305.15585__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2305.15585__01.json
    English statement: (Girao, Hendrey, Illingworth, Lehner, Michel, Savery, Steiner 2023, Chromatic number is not tournament-local, arXiv:2305.15585, Conjecture 11)
      There is a bound C such that for every finite tournament T and every simple graph G on the
      same vertex set, if the chromatic number of G is at least C then some vertex v of T has
      the property that the subgraph of G induced by the out-neighbourhood of v in T contains a
      cycle, that is an undirected cycle on more than two vertices.
    Definitions: [x2_sgraph] and [x2_induced_sgraph] (this file); [sg_has_cycle G] - there is a
      [ucycle] of the adjacency relation with more than two vertices (this file); [N_out v]
      (core/tournament.v); [chi] (coq-graph-theory); [ucycle] (MathComp path.v).
    Notes: This is the case d = 2 of [tournament_outneighborhood_degeneracy_statement] in
      spirit; the size guard 2 < size c excludes the degenerate two-vertex closed walk of a
      simple graph. *)
Definition tournament_outneighborhood_cycle_statement : Prop :=
  exists C : nat,
    forall (T : tournament) (E : rel T)
           (Esym : symmetric E) (Eirr : irreflexive E),
      (C <= χ([set: x2_sgraph Esym Eirr]))%N ->
      exists v : T,
        sg_has_cycle (x2_induced_sgraph Esym Eirr (N_out v)).

(** ** Strong 2-kernels in split digraphs **********************************)

Definition x2_arc_stable (D : diGraphType) (S : {set D}) : bool :=
  [forall u in S, [forall v in S, ~~ (u --> v)]].

Definition x2_tournament_on (D : diGraphType) (S : {set D}) : Prop :=
  forall u v : D, u \in S -> v \in S -> u != v -> (u --> v) (+) (v --> u).

Definition split_partition (D : diGraphType) (Tpart : {set D}) : Prop :=
  x2_tournament_on Tpart /\ x2_arc_stable (~: Tpart).

(** The paper's split digraphs are ORIENTED (loopless and digon-free;
    Nguyen–Scott–Seymour "Distant digraph domination", §1).  [diGraphType]
    enforces neither (irreflexivity/asymmetry live only in [orientedDigraph],
    which the [{set D}]-parameterised helpers here do not use), so the statement
    below carries this as an explicit guard.  Without it the conjecture is
    provably FALSE, e.g. the directed triangle with a self-loop at every vertex
    satisfies [split_partition] but admits no strong 2-kernel (every loop vertex
    is barred from [K] by [x2_arc_stable], forcing [K = set0]). *)
Definition x2_oriented (D : diGraphType) : Prop :=
  forall u v : D, u --> v -> (u != v) /\ ~~ (v --> u).

(** A vertex is a source when it has no in-neighbour.  A distinct in-neighbour
    is required so that (absent [x2_oriented]) a self-loop does not spuriously
    make a vertex a non-source. *)
Definition no_sources (D : diGraphType) : Prop :=
  forall v : D, [exists u : D, (u != v) && (u --> v)].

Definition x2_covers1 (D : diGraphType) (K : {set D}) (v : D) : bool :=
  (v \in K) || [exists k in K, k --> v].

Definition x2_covers2 (D : diGraphType) (K : {set D}) (v : D) : bool :=
  x2_covers1 K v || [exists k in K, [exists u : D, (k --> u) && (u --> v)]].

Definition two_kernel (D : diGraphType) (K : {set D}) : Prop :=
  x2_arc_stable K /\ forall v : D, x2_covers2 K v.

Definition strong_two_kernel (D : diGraphType) (Tpart K : {set D}) : Prop :=
  two_kernel K /\
  forall v : D, v \in Tpart ->
    x2_covers1 K v ||
    [exists k in K :&: Tpart, [exists u : D, (k --> u) && (u --> v)]].

(** Corpus row: arxiv:2409.05039#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2409.05039__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2409.05039__00.json
    English statement: (Nguyen, Scott, Seymour 2024, Distant digraph domination, arXiv:2409.05039, open question on strong 2-kernels in split digraphs)
      For every finite digraph D that is oriented (no loops and no two opposite arcs) and every
      vertex set Tpart such that Tpart induces a tournament and no arc joins two vertices
      outside Tpart, if D has no source (every vertex has an in-neighbour distinct from itself)
      then D has a strong 2-kernel K with 2 * #|K| <= #|D|, that is of size at most half the
      order: K has no arc inside it, every vertex is reached from K in at most two steps, and
      every vertex of Tpart is either in K or reached in one step from K or reached in two steps
      from a vertex of K inside Tpart.
    Definitions: [split_partition Tpart] - Tpart induces a tournament and its complement is
      arc-stable (this file); [two_kernel K] - K arc-stable and 2-covering every vertex (this
      file); [strong_two_kernel Tpart K] - the strengthening on the tournament part (this file);
      [x2_covers1] / [x2_covers2] - covering in at most one, resp. two, steps (this file);
      [x2_oriented D] - loopless and digon-free (this file); [no_sources D] - every vertex has a
      distinct in-neighbour (this file).
    Notes: The [x2_oriented] guard is load-bearing: the paper's split digraphs are oriented, and
      [diGraphType] enforces neither irreflexivity nor asymmetry. Without the guard the
      statement is provably false, for instance for the directed triangle with a loop at every
      vertex, where arc-stability forces K to be empty. The no-source condition requires a
      DISTINCT in-neighbour for the same reason. The bound |K| <= |G|/2 is cleared of division
      as 2 * #|K| <= #|D|. *)
Definition split_digraph_strong_two_kernel_statement : Prop :=
  forall (D : diGraphType) (Tpart : {set D}),
    x2_oriented D ->
    split_partition Tpart -> no_sources D ->
    exists K : {set D},
      strong_two_kernel Tpart K /\ (2 * #|K| <= #|D|)%N.

(** ** Oriented paths at the semidegree threshold ***************************)

Definition consecutive_in (D : finType) (p : seq D) (u v : D) : Prop :=
  exists i : nat,
    i.+1 < size p /\
    (((u == nth u p i) && (v == nth u p i.+1)) ||
     ((u == nth u p i.+1) && (v == nth u p i))).

Definition listed_path_underlying (P : diGraphType) (k : nat) (p : seq P) : Prop :=
  [/\ uniq p,
      size p = k.+1,
      (forall v : P, v \in p)
    & forall u v : P, u != v ->
        (chi_bounded.urel u v <-> consecutive_in p u v)].

Definition oriented_path (P : orientedDigraph) (k : nat) : Prop :=
  exists p : seq P, @listed_path_underlying P k p.

Definition antidirected_path (P : diGraphType) : Prop :=
  forall v : P, indeg v = 0 \/ outdeg v = 0.

Definition min_semidegree_half (D : diGraphType) (k : nat) : Prop :=
  forall v : D, (k <= 2 * outdeg v)%N /\ (k <= 2 * indeg v)%N.

(** Corpus row: arxiv:2503.23191#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2503.23191__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2503.23191__00.json
    English statement: (Penev, Taruni, Thomasse, Trujillo-Negrete, Tyomkyn 2025, Two-block paths in oriented graphs of large semidegree, arXiv:2503.23191, Question 5.1)
      For every k and every finite oriented graph G whose minimum semidegree is at least k/2
      (written without division as k <= 2 * outdeg v and k <= 2 * indeg v at every vertex), G
      contains, as a subdigraph, every orientation P of the path with k edges that is not
      antidirected; containment means an injective arc-preserving map from P into G.
    Definitions: [oriented_path P k] - P is an orientation of the path on k+1 vertices, stated
      by listing its vertices in path order and requiring the underlying adjacency to be exactly
      consecutiveness in that list (this file); [antidirected_path P] - every vertex has
      in-degree 0 or out-degree 0 (this file); [min_semidegree_half G k] (this file);
      [subdigraph_embed P G] - injective arc-preserving map (this file); [chi_bounded.urel] -
      the underlying adjacency relation (conjectures/chi_bounded.v).
    Notes: The path is indexed by its number of edges k, so it has k+1 vertices. The exception
      in the corpus (save for the antidirected orientations) is the hypothesis ~
      antidirected_path P. *)
Definition semidegree_oriented_paths_statement : Prop :=
  forall (k : nat) (G : orientedDigraph),
    min_semidegree_half G k ->
    forall P : orientedDigraph,
      oriented_path P k -> ~ antidirected_path P -> subdigraph_embed P G.

(** ** Longest directed cycles in vertex-transitive digraphs ****************)

Definition weakly_connected (D : diGraphType) : Prop :=
  forall u v : D, connect (@chi_bounded.urel D) u v.

Definition longest_dicycle (D : diGraphType) (c : seq D) : Prop :=
  dicycle c /\ forall c' : seq D, dicycle c' -> (size c' <= size c)%N.

(** Corpus row: arxiv:2602.16333#02
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2602.16333__02/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2602.16333__02.json
    English statement: (Bucic, Hendrey, Mohar, Steiner, Yepremyan, Long cycles in vertex transitive digraphs, arXiv:2602.16333, Question 4.3)
      In every finite connected vertex-transitive digraph, any two longest directed cycles share
      a vertex: if c1 and c2 are directed cycles of maximum size, then some vertex belongs to
      both.
    Definitions: [weakly_connected D] - any two vertices are joined by a path in the underlying
      adjacency, i.e. the digraph is connected when directions are forgotten (this file);
      [vertex_transitiveb D] - the automorphism group acts transitively on vertices
      (constructions/automorphism.v); [longest_dicycle D c] - c is a directed cycle and no
      directed cycle has more vertices (this file); [dicycle] (core/dipath.v).
    Notes: Connected is read as weak connectivity; on a finite vertex-transitive digraph weak
      and strong connectivity agree, so this matches the corpus. The statement is vacuously true
      on digraphs with no directed cycle. Cycle length is counted in vertices. *)
Definition vertex_transitive_longest_dicycles_intersect_statement : Prop :=
  forall D : diGraphType,
    weakly_connected D -> vertex_transitiveb D ->
    forall c1 c2 : seq D,
      longest_dicycle c1 -> longest_dicycle c2 ->
      exists v : D, v \in c1 /\ v \in c2.

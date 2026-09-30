(** * Digraph.conjectures.P9 — milestone P9 (plan v4), namespace [Digraph]

    Statement-only (axiom-free) formalisation of 20 open OPG digraph
    conjectures/problems. Each node is a [Definition <formal_name> : Prop],
    carrier type chosen per the manifest's [rocq_idiom] (tournament /
    orientedDigraph / diGraphType, never a blanket undirected [sgraph]).

    The file REUSES the existing directed core and the already-committed
    conjecture primitives wherever possible:
      - core/{digraph,oriented,tournament,dipath,strong}: [arc], [outdeg],
        [outdeg_in], [outsel], [dipath], [dicycle], [strongb], [induced_digraph],
        [del_vertex], [dgiso], [sub_tournament], [TT], [converse], [next];
      - conjectures/classic_core: [stable], [indeg], [diregular]
        (note: [indeg] is defined in BOTH classic_core and colouring_variants,
         so use sites below qualify it as [classic_core.indeg] — a base-reuse
         duplication to be consolidated to one canonical in-degree at G3);
      - conjectures/chi_bounded: [underlying] (the underlying simple graph of a
        digraph) and graph-theory's ordinary chromatic number [χ(_)] (row 18);
      - conjectures/dichromatic: [acyclicb], [dicolorableb];
      - conjectures/packing: [real_sel], [selindeg], [arc_disjoint_sel],
        [out_branching], [in_branching];
      - conjectures/colouring_variants: [oriented_kcolouring],
        [mono_reach_or_rainbow_statement] (row 3), [dhom];
      - conjectures/two_extremal: [loopless], [underlyingG], [planar_sg]
        (the repo's Wagner-minor combinatorial planarity, so the three
        planarity rows compile in this switch WITHOUT coq-fourcolor).

    Three nodes are aliases onto already-present constants (no restating):
    [hoand_reed_statement] (= packing.hoang_reed_statement),
    [hamilton_cycle_in_small_d_diregular_graphs_statement]
    (= classic_core.jackson_hamilton_small_diregular_statement) and
    [monochromatic_reachability_vs_rainbow_triangles_statement]
    (= colouring_variants.mono_reach_or_rainbow_statement). *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented tournament dipath strong.
From Digraph Require Import classic_core dichromatic packing colouring_variants two_extremal.
From Digraph Require Import interop_graph_theory chi_bounded.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Shared NEW primitives — base candidates, to migrate at G3

    BASE-MOVE: every general, conjecture-agnostic primitive in this section is a
    candidate for relocation to the directed base on the G3 base move:
      - invariant-style scalars/predicates ([nb_arcs], [weakly_connected],
        [tree_digraph], [cyc_arcs], [ham], [kstrong], [arccut], [karcstrong],
        [alpha], [cyclomatic]/[nb_wcc]/[wadj], [dipath_arcs], [arcset_outdeg],
        [arcset_indeg], [single_dicycle_arcset], [ndicycles], [nonedge_count],
        [short_dicycle_free], [set_partition], [arc_decomp])
        -> theories/invariants/ at G3;
    Each is greppable via the "BASE-MOVE:" tag. NB: [alpha]/[stable]/[indeg]
    collide with GraphTheory.core.dom and the classic_core/colouring_variants
    duplicate of [indeg]; the move must pick one canonical name and qualify. *)

(* BASE-MOVE: relocate to theories/invariants/ at G3 (general diGraph primitives). *)
Section Primitives.
Variable D : diGraphType.
Implicit Types (v w : D) (c : seq D) (f : D -> {set D}).

(** Number of arcs of [D] (ordered head/tail pairs). *)
Definition nb_arcs : nat := #|[set p : D * D | p.1 --> p.2]|.

(** Weak connectivity: reachability under the symmetric closure of [arc]. *)
Definition weakly_connected : bool :=
  [forall u : D, [forall v : D, connect (fun x y : D => (x --> y) || (y --> x)) u v]].

(** Underlying undirected tree: weakly connected with [#V - 1] arcs. (On an
    oriented digraph arcs are in bijection with the underlying edges, so this is
    "the underlying graph is a tree".) *)
Definition tree_digraph : bool := weakly_connected && (nb_arcs == #|D| - 1).

(** Arc set [{(u,v) : u\in c, v = next}] traversed by a directed cycle [c]
    (the EDGES of the cycle, for arc-/edge-disjointness). *)
Definition cyc_arcs c : {set D * D} :=
  [set p : D * D | (p.1 \in c) && (next c p.1 == p.2)].

(** A Hamiltonian directed cycle: a [dicycle] through every vertex. *)
Definition ham c : bool := dicycle c && (size c == #|D|).

(** Vertex [k]-strong connectivity: more than [k] vertices and removing any set
    of fewer than [k] vertices leaves a strongly connected digraph. *)
Definition kstrong (k : nat) : bool :=
  (k < #|D|) && [forall S : {set D}, (#|S| < k) ==> strongb (induced_digraph (~: S))].

(** Number of forward-crossing arcs out of [B] (its out-cut). *)
Definition arccut (B : {set D}) : nat :=
  #|[set p : D * D | [&& p.1 \in B, p.2 \notin B & p.1 --> p.2]]|.

(** [k]-arc-strong connectivity: every nonempty proper [B] has out-cut ≥ [k]
    (Menger form of arc-connectivity ≥ [k]). Guard [1 < #|D|] (not just [0 < #|D|])
    so the predicate is non-vacuous: on a 1-vertex digraph there is no nonempty
    proper [B], which would make every [k] hold. *)
Definition karcstrong (k : nat) : bool :=
  (1 < #|D|) && [forall B : {set D}, ((B != set0) && (B != [set: D])) ==> (k <= arccut B)].

(** Independence number α(D): largest [stable] (arc-free) vertex set. *)
Definition alpha : nat := \max_(S : {set D} | stable S) #|S|.

(** Spanning CYCLIC subdigraph as an arc selector [f]: real arcs only and every
    vertex has positive kept in- and out-degree (so every vertex lies on a
    cycle of the kept subdigraph). *)
Definition cyclic_sel f : bool :=
  real_sel f && [forall v : D, (0 < #|f v|) && (0 < selindeg f v)].

(** Cyclomatic number (circuit rank) of an arc selector [f]: [m + c - n] with
    [m] kept arcs, [c] weakly-connected components, [n = #V]. *)
Definition wadj f : rel D := fun u w => (w \in f u) || (u \in f w).
Definition nb_wcc f : nat := #|[set [set y | connect (wadj f) x y] | x in [set: D]]|.
Definition cyclomatic f : nat := (\sum_(v : D) #|f v|) + nb_wcc f - #|D|.

(** Arcs of a directed path [x :: s] (consecutive vertex pairs). *)
Definition dipath_arcs (x : D) (s : seq D) : {set D * D} := [set p in zip (x :: s) s].

(** Out-/in-degree of a vertex inside a fixed arc set [A]. *)
Definition arcset_outdeg (A : {set D * D}) v : nat := #|[set w | (v, w) \in A]|.
Definition arcset_indeg (A : {set D * D}) v : nat := #|[set u | (u, v) \in A]|.

(** [A] is the arc set of a SINGLE directed cycle: nonempty, all real arcs,
    in-degree = out-degree ≤ 1 at every vertex, and its support is connected
    (so it is one cycle, not a union of several). *)
Definition single_dicycle_arcset (A : {set D * D}) : bool :=
  [&& A != set0,
      [forall p : D * D, (p \in A) ==> (p.1 --> p.2)],
      [forall v : D, (arcset_outdeg A v == arcset_indeg A v) && (arcset_outdeg A v <= 1)] &
      [forall u : D, [forall w : D,
         ((0 < arcset_outdeg A u) && (0 < arcset_outdeg A w)) ==>
         connect (fun a b : D => (a, b) \in A) u w]]].

(** Number of directed cycles of [D] (counted by their arc sets). *)
Definition ndicycles : nat := #|[set A : {set D * D} | single_dicycle_arcset A]|.

(** Number of NON-EDGES: unordered nonadjacent vertex pairs. *)
Definition nonedge_count : nat :=
  #|[set e : {set D} | (#|e| == 2) && [forall u in e, [forall v in e, ~~ (u --> v)]]]|.

(** No directed cycle of length ≤ 3 (no loop, no digon, no directed triangle). *)
Definition short_dicycle_free : bool :=
  [&& [forall u : D, ~~ (u --> u)],
      [forall u : D, [forall v : D, ~~ ((u --> v) && (v --> u))]] &
      [forall u : D, [forall v : D, [forall w : D, ~~ [&& u --> v, v --> w & w --> u]]]]].

(** A vertex partition (each vertex in exactly one part). *)
Definition set_partition (part : seq {set D}) : bool :=
  [forall v : D, count (fun A : {set D} => v \in A) part == 1].

(** An arc decomposition by selectors [fs]: real arcs only, every arc kept by
    exactly one selector. *)
Definition arc_decomp (fs : seq (D -> {set D})) : bool :=
  all (@real_sel D) fs &&
  [forall e : D * D, (\sum_(f <- fs) (e.2 \in f e.1)) == (e.1 --> e.2)].

End Primitives.

(** ** Subdigraph containment and subdivision *)

(* BASE-MOVE: relocate to theories/core or theories/invariants at G3. *)
(** [D] contains [H] as a subdigraph: an injective arc-preserving map. *)
Definition contains_subdig (D H : diGraphType) : Prop :=
  exists phi : H -> D, injective phi /\ (forall u v : H, u --> v -> phi u --> phi v).

(** [D] contains a SUBDIVISION of [H]: injective branch vertices [b] and, for
    every arc [u --> v] of [H], an internally-disjoint directed path of [D] from
    [b u] to [b v] avoiding all other branch vertices. *)
Definition subdivides (D H : diGraphType) : Prop :=
  exists (b : H -> D) (p : H -> H -> seq D),
    [/\ injective b,
        (forall u v : H, u --> v -> dipath (b u) (p u v) /\ last (b u) (p u v) = b v),
        (forall u v : H, u --> v -> forall x : H, b x \notin behead (belast (b u) (p u v))) &
        (forall u v u' v' : H, u --> v -> u' --> v' -> (u != u') || (v != v') ->
           ~~ has (mem (behead (belast (b u') (p u' v'))))
                  (behead (belast (b u) (p u v))))].

(** ** Oriented / antidirected trees (orientations of trees) *)

Definition oriented_tree (T : orientedDigraph) : bool := tree_digraph T.

Definition antidirected_tree (T : orientedDigraph) : bool :=
  (* [classic_core.indeg] qualified: [indeg] is declared in both classic_core and
     colouring_variants (base-reuse duplicate, to consolidate at G3). *)
  tree_digraph T && [forall v : T, (outdeg v == 0) || (classic_core.indeg v == 0)].

(** ** Switching of digraphs (Seidel-style switching reconstruction) *)

(* BASE-MOVE: relocate to theories/constructions/ at G3. *)
(** [switched S]: reverse every arc with exactly one endpoint in [S]. *)
Definition switched (D : diGraphType) (S : {set D}) : Type := D.
Section Switched.
Variables (D : diGraphType) (S : {set D}).
HB.instance Definition _ := Finite.on (switched S).
HB.instance Definition _ :=
  HasArc.Build (switched S) (fun u v : D => if (u \in S) (+) (v \in S) then arc v u else arc u v).
End Switched.

(** Switching equivalence: isomorphic after switching on some vertex set. *)
Definition sw_iso (D1 D2 : diGraphType) : Prop := exists S : {set D1}, dgiso (switched S) D2.

(** Same switching deck: a vertex bijection matching the switching classes of
    all vertex-deleted cards. *)
Definition same_deck (D1 D2 : diGraphType) : Prop :=
  exists g : D1 -> D2, bijective g /\ forall i : D1, sw_iso (del_vertex i) (del_vertex (g i)).

(** Switching-reconstructible: determined up to switching by its deck. *)
Definition switching_reconstructible (D : diGraphType) : Prop :=
  forall D' : diGraphType, same_deck D D' -> sw_iso D D'.

(** ** Arc removal / arc reversal (for feedback sets and Ádám's conjecture) *)

(* BASE-MOVE: relocate to theories/constructions/ at G3. *)
(** [remove_arcs F]: [D] with the arcs in [F] deleted. *)
Definition remove_arcs (D : diGraphType) (F : {set D * D}) : Type := D.
Section RemoveArcs.
Variables (D : diGraphType) (F : {set D * D}).
HB.instance Definition _ := Finite.on (remove_arcs F).
HB.instance Definition _ :=
  HasArc.Build (remove_arcs F) (fun u v : D => (u --> v) && ((u, v) \notin F)).
End RemoveArcs.

(* BASE-MOVE: relocate to theories/invariants/ at G3 (general diGraph invariant). *)
(** [F] is a feedback arc set iff deleting it makes [D] acyclic; the minimum
    feedback-arc-set size [β(D)]. *)
Definition min_feedback (D : diGraphType) : nat :=
  #|[arg min_(F < [set: D * D] | acyclicb (remove_arcs F)) #|F|]|.

(* BASE-MOVE: relocate to theories/constructions/ at G3. *)
(** [rev_arc a]: [D] with the single arc [a] reversed (a tournament stays a
    tournament; modelled at digraph level). *)
Definition rev_arc (D : diGraphType) (a : D * D) : Type := D.
Section RevArc.
Variables (D : diGraphType) (a : D * D).
HB.instance Definition _ := Finite.on (rev_arc a).
HB.instance Definition _ :=
  HasArc.Build (rev_arc a)
    (fun u v : D => if (u == a.1) && (v == a.2) then false
                    else if (u == a.2) && (v == a.1) then true else u --> v).
End RevArc.

(** ** Transitive triangles [TT3] for arc-disjoint packings *)

(** A transitive subtournament of order 3: [a --> b], [b --> c], [a --> c]. *)
Definition tt3 (T : tournament) (t : T * T * T) : bool :=
  [&& t.1.1 --> t.1.2, t.1.2 --> t.2 & t.1.1 --> t.2].

(** Its three arcs. *)
Definition tt3_arcs (T : tournament) (t : T * T * T) : {set T * T} :=
  [set (t.1.1, t.1.2); (t.1.2, t.2); (t.1.1, t.2)].

(** ** The 20 milestone statements ****************************************** *)

(** Corpus row: opg:minimum_number_of_transitive_subtournaments_of_order_3_in_a_tournament
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/minimum_number_of_transitive_subtournaments_of_order_3_in_a_tournament/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/minimum_number_of_transitive_subtournaments_of_order_3_in_a_tournament.json
    English statement: (Open Problem Garden, Minimum number of arc-disjoint transitive subtournaments of order 3 in a tournament)
      Every finite tournament T on n >= 3 vertices contains a list of pairwise arc-disjoint
      transitive subtournaments of order 3 (transitive triangles a -> b, b -> c, a -> c) whose
      length is at least (n * (n - 3) + 5) divided by 6 in natural-number arithmetic, that is
      the ceiling of n(n-3)/6.
    Definitions: [tournament] - finite digraph, irreflexive, with exactly one arc between any
      two distinct vertices (core/tournament.v); [tt3 T t] - the triple t is a transitive
      triangle (this file); [tt3_arcs t] - the set of its three arcs (this file); [pairwise] and
      [disjoint] are MathComp.
    Notes: The corpus bound ceil(n(n-1)/6 - n/3) equals ceil(n(n-3)/6), which is what the body
      writes; the guard 3 <= #|T| keeps the natural-number subtraction n - 3 from truncating.
      Arc-disjointness is required pairwise on the list, so repeated triangles cannot pad it. *)
Definition minimum_number_of_transitive_subtournaments_of_order_statement : Prop :=
  forall T : tournament, 3 <= #|T| ->
    exists P : seq (T * T * T),
      [/\ all (@tt3 T) P,
          pairwise (fun a b => [disjoint tt3_arcs a & tt3_arcs b]) P &
          (#|T| * (#|T| - 3) + 5) %/ 6 <= size P].

(** Corpus row: opg:cyclic_spanning_subdigraph_with_small_cyclomatic_number
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/cyclic_spanning_subdigraph_with_small_cyclomatic_number/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/cyclic_spanning_subdigraph_with_small_cyclomatic_number.json
    English statement: (Open Problem Garden, Cyclic spanning subdigraph with small cyclomatic number)
      For every finite digraph D in which every vertex lies on a directed cycle (equivalently,
      all strong components are nontrivial) there is a spanning subdigraph, given as an arc
      selector keeping only real arcs and leaving every vertex with positive kept in-degree and
      positive kept out-degree, whose cyclomatic number (number of kept arcs, plus number of
      weakly connected components of the kept subdigraph, minus number of vertices) is at most
      the independence number of D.
    Definitions: [cyclic_sel f] - the arc selector f keeps only real arcs and leaves positive
      in- and out-degree at every vertex (this file); [cyclomatic f] - kept arcs + weakly
      connected components - vertices (this file); [nb_wcc f] / [wadj f] - weakly connected
      components of the kept subdigraph (this file); [alpha D] - the independence number, the
      maximum size of an arc-free vertex set (this file); [stable S]
      (conjectures/classic_core.v).
    Notes: The corpus hypothesis all strong components are nontrivial is encoded by the
      equivalent every vertex lies on a directed cycle. A spanning subdigraph is modelled by an
      arc selector f : D -> {set D} rather than by a new carrier type. *)
Definition cyclic_spanning_subdigraph_with_small_cyclomatic_num_statement : Prop :=
  forall D : diGraphType,
    (forall v : D, exists c : seq D, dicycle c /\ v \in c) ->
    exists f : D -> {set D}, cyclic_sel f /\ (cyclomatic f <= alpha D).

(** Corpus row: opg:monochromatic_reachability_vs_rainbow_triangles
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/monochromatic_reachability_vs_rainbow_triangles/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/monochromatic_reachability_vs_rainbow_triangles.json
    English statement: (Open Problem Garden, Monochromatic reachability or rainbow triangles)
      For every finite tournament T with at least one vertex whose arcs are coloured with three
      colours, either T has a rainbow directed triangle (a directed 3-cycle whose three arcs
      carry three distinct colours) or T has a vertex from which every vertex is reached by a
      directed path all of whose arcs share one colour.
    Definitions: [mono_reach_or_rainbow_statement] - the statement this definition aliases, with
      [arc_colouring], [rainbow_triangle], [mono_reach] and [mono_root]
      (conjectures/colouring_variants.v); [tournament] (core/tournament.v).
    Notes: This node is an alias: its body is exactly
      [colouring_variants.mono_reach_or_rainbow_statement], so the two names denote the same
      proposition. The manifest attaches to that other name the row
      opg:monochromatoc_reachability_in_arc_colored_digraphs, whose text is the general
      Sands-Sauer-Woodrow statement; see the note there and meta/STATEMENT_IMPROVEMENTS.md. *)
Definition monochromatic_reachability_vs_rainbow_triangles_statement : Prop :=
  mono_reach_or_rainbow_statement.

(** Corpus row: opg:subdivision_of_a_transitive_tournament_in_digraphs_with_large_outdegree
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/subdivision_of_a_transitive_tournament_in_digraphs_with_large_outdegree/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/subdivision_of_a_transitive_tournament_in_digraphs_with_large_outdegree.json
    English statement: (Open Problem Garden, Subdivision of a transitive tournament in digraphs with large outdegree)
      There is a function f from naturals to naturals such that for every k and every finite
      NON-EMPTY digraph D in which every vertex has out-degree at least f(k), D contains a
      subdivision of the transitive tournament on k vertices: injective branch vertices together
      with, for each arc of the tournament, a directed path of D joining the corresponding branch
      vertices, whose interiors avoid all branch vertices and are pairwise disjoint.
    Definitions: [subdivides D H] - D contains a subdivision of H in the above sense (this
      file); [TT k] - the transitive tournament on k vertices, ordered by the ordinals
      (core/tournament.v); [outdeg v] (core/oriented.v); [dipath] (core/dipath.v).
    Notes: The quantifier order is the corpus one: a single f works for every k and every D. The
      minimum out-degree condition is phrased pointwise.
      GUARD REPAIR (2026-09-24, wave E4): the host carries the guard 0 < #|D|. Without it the row
      is FALSE: the pointwise condition [forall v : D, f k <= outdeg v] holds VACUOUSLY on the
      EMPTY digraph, whereas [subdivides D (TT k)] needs an injective branch map out of the
      nonempty TT k, so no f can work (wave-E3 scratch refutation degeneracy.v:
      P9_subdivision_TT_false, kept in the wave report, not committed). Mader's question is about
      digraphs of large minimum out-degree, which have vertices; the guard excludes exactly the
      vertexless host that a pointwise degree condition admits. Teeth and non-vacuity:
      grounding_P9.v (p9_subdivision_TT_unguarded_false, p9_outdeg_host_nonvacuous). *)
Definition subdivision_of_a_transitive_tournament_in_digraphs_w_statement : Prop :=
  exists f : nat -> nat,
    forall (k : nat) (D : diGraphType), (0 < #|D|)%N ->
      (forall v : D, f k <= outdeg v) -> subdivides D (TT k : diGraphType).

(** Corpus row: opg:antidirected_trees_in_digraphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/antidirected_trees_in_digraphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/antidirected_trees_in_digraphs.json
    English statement: (Open Problem Garden, Antidirected trees in digraphs)
      For every finite digraph D and every k >= 2, if the number of arcs of D exceeds (k-2)
      times the number of its vertices, then D contains, as a subdigraph, every antidirected
      tree T on k vertices, that is every orientation of a tree in which each vertex has
      in-degree 0 or out-degree 0; containment means an injective arc-preserving map from T to
      D.
    Definitions: [nb_arcs D] - the number of ordered pairs forming an arc (this file);
      [antidirected_tree T] - the underlying graph is a tree (weakly connected with #V - 1 arcs)
      and every vertex has in-degree 0 or out-degree 0 (this file); [tree_digraph] and
      [weakly_connected] (this file); [contains_subdig D T] - an injective arc-preserving map T
      -> D (this file); [orientedDigraph] (core/oriented.v).
    Notes: The guard 2 <= k keeps the natural-number subtraction k - 2 faithful; at k < 2 the
      corpus hypothesis is negative and the statement would be about all digraphs. Containment
      is as a subdigraph (arcs preserved, not reflected), as in the corpus. *)
Definition antidirected_trees_in_digraphs_statement : Prop :=
  forall (D : diGraphType) (k : nat), 2 <= k ->
    (k - 2) * #|D| < nb_arcs D ->
    forall T : orientedDigraph, antidirected_tree T -> #|T| = k -> contains_subdig D T.

(** Corpus row: opg:edge_disjoint_hamilton_cycles
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/edge_disjoint_hamilton_cycles/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/edge_disjoint_hamilton_cycles.json
    English statement: (Open Problem Garden, Edge-disjoint Hamilton cycles in highly strongly connected tournaments)
      For every k >= 2 there is a function f such that every finite tournament that is
      f(k)-strongly connected has k pairwise arc-disjoint Hamilton cycles, that is k directed
      cycles through all vertices no two of which use a common arc.
    Definitions: [kstrong T k] - more than k vertices and deleting any fewer than k vertices
      leaves a strongly connected digraph (this file); [ham c] - c is a directed cycle through
      every vertex (this file); [cyc_arcs c] - the arc set traversed by the cycle c (this file);
      [dicycle] (core/dipath.v); [strongb] (invariants/strong.v).
    Notes: The corpus puts the existential for f outside the quantifier on k (there is an
      integer f(k) for every k); the body quantifies k first and then exhibits a function f,
      which is equivalent since only the value f(k) is used. *)
Definition edge_disjoint_hamilton_cycles_statement : Prop :=
  forall k : nat, 2 <= k ->
    exists f : nat -> nat,
      forall T : tournament, kstrong T (f k) ->
        exists Cs : seq (seq T),
          [/\ all (@ham T) Cs,
              pairwise (fun a b => [disjoint cyc_arcs a & cyc_arcs b]) Cs &
              size Cs = k].

(** Corpus row: opg:partitioning_planar_digraphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/partitioning_planar_digraphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/partitioning_planar_digraphs.json
    English statement: (Open Problem Garden, The Two Color Conjecture, partitioning planar digraphs)
      For every finite loopless digraph D whose arc relation is asymmetric (an orientation of a
      simple graph) and whose underlying simple graph is planar, the vertex set splits into a
      set X and its complement, each inducing an acyclic subdigraph.
    Definitions: [loopless D] and [underlyingG llD] - the underlying simple graph of a loopless
      digraph (conjectures/two_extremal.v); [planar_sg G] - planarity in the Wagner form, no K_5
      minor and no K_3,3 minor (conjectures/two_extremal.v); [acyclicb] - no directed cycle
      (conjectures/dichromatic.v); [induced_digraph X] (core/digraph.v).
    Notes: Being an orientation of a simple graph is the explicit hypothesis that no two
      opposite arcs occur, together with looplessness. Planarity uses the repo's Wagner-minor
      characterisation so the file compiles without coq-fourcolor. *)
Definition partitioning_planar_digraphs_statement : Prop :=
  forall (D : diGraphType) (llD : loopless D),
    (forall u v : D, u --> v -> ~~ (v --> u)) ->
    planar_sg (underlyingG llD) ->
    exists X : {set D}, acyclicb (induced_digraph X) /\ acyclicb (induced_digraph (~: X)).

(** Corpus row: opg:partitionning_a_tournament_into_k_strongly_connected_subtournaments
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/partitionning_a_tournament_into_k_strongly_connected_subtournaments/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/partitionning_a_tournament_into_k_strongly_connected_subtournaments.json
    English statement: (Open Problem Garden, Partitioning a tournament into k-strongly connected subtournaments)
      There is a function g from finite lists of positive integers to naturals such that for
      every list k_1, ..., k_p of positive integers and every tournament T that is
      g(k_1,...,k_p)-strongly connected, the vertex set of T partitions into p parts V_1, ...,
      V_p such that each V_i has more than one vertex and the subtournament it induces is
      k_i-strongly connected.
    Definitions: [kstrong T k] (this file); [set_partition part] - every vertex lies in exactly
      one part (this file); [sub_tournament S] - the subtournament induced by S
      (core/tournament.v).
    Notes: Nontriviality of each part is encoded as 1 < #|V_i|; note that [kstrong] itself
      already requires k < #|V_i|. *)
Definition partitionning_a_tournament_into_k_strongly_connected_statement : Prop :=
  exists g : seq nat -> nat,
    forall ks : seq nat, all (fun k => 0 < k) ks ->
      forall T : tournament, kstrong T (g ks) ->
        exists part : seq {set T},
          [/\ size part = size ks, set_partition part &
              forall i : 'I_(size ks),
                (1 < #|nth set0 part i|) /\
                kstrong (sub_tournament (nth set0 part i)) (nth 0 ks i)].

(** Corpus row: opg:switching_reconstruction_of_digraphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/switching_reconstruction_of_digraphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/switching_reconstruction_of_digraphs.json
    English statement: (Open Problem Garden, Switching reconstruction of digraphs)
      There is a finite digraph on at least twelve vertices that is not switching
      reconstructible, that is a digraph D such that some digraph D' has the same switching deck
      (a bijection matching, for each vertex, the switching class of the corresponding
      vertex-deleted digraph) without D and D' being switching isomorphic.
    Definitions: [switched S] - the digraph obtained by reversing every arc with exactly one
      endpoint in S (this file); [sw_iso D1 D2] - isomorphic after switching on some vertex set
      (this file); [same_deck D1 D2] - a vertex bijection matching the switching classes of all
      vertex-deleted digraphs (this file); [switching_reconstructible D] - every digraph with
      the same deck is switching isomorphic to D (this file); [dgiso] and [del_vertex]
      (core/digraph.v).
    Notes: The corpus asks a question (are there switching-nonreconstructible digraphs on twelve
      or more vertices); the body encodes the affirmative answer, so proving the definition
      means answering yes and refuting it means answering no. *)
Definition switching_reconstruction_of_digraphs_statement : Prop :=
  exists D : diGraphType, (12 <= #|D|) /\ ~ switching_reconstructible D.

(** Corpus row: opg:arc_disjoint_directed_cycles_in_regular_directed_graphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/arc_disjoint_directed_cycles_in_regular_directed_graphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/arc_disjoint_directed_cycles_in_regular_directed_graphs.json
    English statement: (Open Problem Garden, Arc-disjoint directed cycles in regular directed graphs)
      For every finite digraph D and every k, if D is k-diregular (every vertex has in-degree
      and out-degree exactly k) then D has a list of at least binomial(k+1, 2) pairwise
      arc-disjoint directed cycles.
    Definitions: [diregular D k] - in-degree and out-degree equal k at every vertex
      (conjectures/classic_core.v); [cyc_arcs c] - the arcs traversed by the cycle c (this
      file); [dicycle] (core/dipath.v).
    Notes: No parallel arcs is automatic here, arcs being a relation on vertices, so k-regular
      of the corpus is exactly [diregular]. The list is required to have at least, not exactly,
      binomial(k+1,2) members. *)
Definition arc_disjoint_directed_cycles_in_regular_directed_gra_statement : Prop :=
  forall (D : diGraphType) (k : nat), diregular D k ->
    exists P : seq (seq D),
      [/\ all (@dicycle D) P,
          pairwise (fun a b => [disjoint cyc_arcs a & cyc_arcs b]) P &
          'C(k.+1, 2) <= size P].

(** Corpus row: opg:decomposing_an_even_tournament_in_directed_paths
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/decomposing_an_even_tournament_in_directed_paths/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/decomposing_an_even_tournament_in_directed_paths.json
    English statement: (Open Problem Garden, Decomposing an even tournament in directed paths)
      Every finite tournament T on an even number of vertices decomposes into exactly sum over v
      of (out-degree of v minus in-degree of v, truncated at zero) directed paths: there is a
      list of directed paths of T such that every arc of T is used by exactly one of them and no
      non-arc is used.
    Definitions: [dipath x s] - directed path given by its first vertex and the rest
      (core/dipath.v); [dipath_arcs x s] - the set of consecutive pairs of the path (this file);
      [classic_core.indeg] - in-degree, qualified because [indeg] is declared both in
      conjectures/classic_core.v and in conjectures/colouring_variants.v; [outdeg]
      (core/oriented.v).
    Notes: The decomposition condition is stated arcwise: for every ordered pair e, the number
      of paths using e equals the boolean saying that e is an arc, which forces both cover and
      disjointness. The subtraction outdeg v - indeg v is natural-number subtraction, so it is
      already the max(0, .) of the corpus formula. *)
Definition decomposing_an_even_tournament_in_directed_paths_statement : Prop :=
  forall T : tournament, ~~ odd #|T| ->
    exists Q : seq (T * seq T),
      [/\ all (fun p => dipath p.1 p.2) Q,
          [forall e : T * T, (\sum_(p <- Q) (e \in dipath_arcs p.1 p.2)) == (e.1 --> e.2)] &
          size Q = \sum_(v : T) (outdeg v - classic_core.indeg v)].

(** Corpus row: opg:hoand_reed_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/hoand_reed_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/hoand_reed_conjecture.json
    English statement: (Open Problem Garden, Hoang-Reed Conjecture)
      For every finite digraph D with at least one vertex and every k, if every vertex has
      out-degree at least k then D has k directed cycles C_1, ..., C_k such that for every j >=
      2 the cycle C_j meets the union of C_1, ..., C_{j-1} in at most one vertex.
    Definitions: [hoang_reed_statement] - the statement this definition aliases, with
      [cycle_pack] (conjectures/packing.v); [dicycle] (core/dipath.v); [outdeg]
      (core/oriented.v).
    Notes: This node is an alias: its body is exactly [packing.hoang_reed_statement], which owns
      no row of its own. The laminar condition is indexed by position in the list, with j
      ranging over the ordinals below the list length. *)
Definition hoand_reed_statement : Prop := hoang_reed_statement.

(** Corpus row: opg:arc_disjoint_out_branching_and_in_branching
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/arc_disjoint_out_branching_and_in_branching/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/arc_disjoint_out_branching_and_in_branching.json
    English statement: (Open Problem Garden, Arc-disjoint out-branching and in-branching)
      There is an integer k such that for every finite digraph D that is k-arc-strong and every
      choice of vertices u and v, D contains a spanning out-branching rooted at u and a spanning
      in-branching rooted at v that share no arc.
    Definitions: [karcstrong D k] - more than one vertex and every nonempty proper vertex set
      has out-cut at least k, the Menger form of arc-connectivity at least k (this file);
      [arccut B] - the number of arcs leaving B (this file); [out_branching f u] / [in_branching
      g v] - spanning arborescences described by arc selectors (conjectures/packing.v);
      [arc_disjoint_sel f g] - no common kept arc (conjectures/packing.v).
    Notes: [karcstrong] guards 1 < #|D|: on a one-vertex digraph there is no nonempty proper
      subset and every k would hold vacuously. *)
Definition arc_disjoint_out_branching_and_in_branching_statement : Prop :=
  exists k : nat,
    forall (D : diGraphType) (u v : D), karcstrong D k ->
      exists f g : D -> {set D},
        [/\ out_branching f u, in_branching g v & arc_disjoint_sel f g].

(** Corpus row: opg:decomposing_k_arc_strong_tournament_into_k_spanning_strong_digraphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/decomposing_k_arc_strong_tournament_into_k_spanning_strong_digraphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/decomposing_k_arc_strong_tournament_into_k_spanning_strong_digraphs.json
    English statement: (Open Problem Garden, Decomposing k-arc-strong tournament into k spanning strong digraphs)
      For every finite tournament T and every k >= 1, if T is k-arc-strong then its arc set
      decomposes into k parts, each part keeping all vertices and inducing a strongly connected
      spanning subdigraph.
    Definitions: [karcstrong T k] (this file); [arc_decomp fs] - the selectors of the list fs
      keep only real arcs and every arc is kept by exactly one of them (this file); [outsel f] -
      the digraph on the same vertices whose arcs are the ones kept by f (core/oriented.v);
      [strongb] (invariants/strong.v).
    Notes: Spanning is automatic: an arc selector keeps the whole vertex set. The decomposition
      is exact (every arc used once), as in the corpus word decomposes. *)
Definition decomposing_k_arc_strong_tournament_into_k_spanning_statement : Prop :=
  forall (T : tournament) (k : nat), 0 < k -> karcstrong T k ->
    exists fs : seq (T -> {set T}),
      [/\ size fs = k, arc_decomp fs & all (fun f => strongb (outsel f)) fs].

(** Corpus row: opg:non_edges_vs_feedback_edge_sets_in_digraphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/non_edges_vs_feedback_edge_sets_in_digraphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/non_edges_vs_feedback_edge_sets_in_digraphs.json
    English statement: (Open Problem Garden, Non-edges vs. feedback edge sets in digraphs)
      For every finite digraph D without directed cycles of length at most 3 (no loop, no digon,
      no directed triangle), twice the minimum size of a feedback arc set of D is at most the
      number of unordered pairs of nonadjacent vertices of D; this is the integer-arithmetic
      form of beta(D) <= gamma(D)/2.
    Definitions: [short_dicycle_free D] - no loop, no pair of opposite arcs and no directed
      triangle (this file); [min_feedback D] - the minimum size of an arc set whose deletion
      makes D acyclic (this file); [remove_arcs F] - D with the arcs of F deleted (this file);
      [nonedge_count D] - the number of two-element vertex sets with no arc inside (this file);
      [acyclicb] (conjectures/dichromatic.v).
    Notes: Nonadjacency is read on unordered pairs, matching the corpus gamma; feedback arc sets
      are minimised over all subsets of ordered pairs via [arg min]. *)
Definition non_edges_vs_feedback_edge_sets_in_digraphs_statement : Prop :=
  forall D : diGraphType, short_dicycle_free D -> 2 * min_feedback D <= nonedge_count D.

(** Corpus row: opg:hamilton_cycle_in_small_d_diregular_graphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/hamilton_cycle_in_small_d_diregular_graphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/hamilton_cycle_in_small_d_diregular_graphs.json
    English statement: (Open Problem Garden, Hamilton cycle in small d-diregular graphs (Jackson))
      For every finite oriented graph D with at least one vertex and every d > 2, if D is
      d-diregular (every vertex has in-degree and out-degree exactly d) and D has at most 4d+1
      vertices, then D has a directed cycle through every vertex.
    Definitions: [jackson_hamilton_small_diregular_statement] - the statement this definition
      aliases (conjectures/classic_core.v); [diregular D d] (conjectures/classic_core.v);
      [orientedDigraph] (core/oriented.v); [dicycle] (core/dipath.v).
    Notes: This node is an alias: its body is exactly
      [classic_core.jackson_hamilton_small_diregular_statement], which owns no row of its own.
      The corpus says indegree and outdegree at least d; [diregular] asks for equality, which on
      an oriented graph of the stated order is the usual reading of d-diregular in the source. *)
Definition hamilton_cycle_in_small_d_diregular_graphs_statement : Prop :=
  jackson_hamilton_small_diregular_statement.

(** Corpus row: opg:oriented_chromatic_number_of_planar_graphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/oriented_chromatic_number_of_planar_graphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/oriented_chromatic_number_of_planar_graphs.json
    English statement: (Open Problem Garden, Oriented chromatic number of planar graphs)
      There is a number M that is the maximum oriented chromatic number of an oriented planar
      graph: every loopless digraph with asymmetric arc relation and planar underlying graph has
      a homomorphism onto some tournament with M vertices, and some such digraph has no
      homomorphism onto any tournament with M-1 vertices.
    Definitions: [oriented_kcolouring D k] - there is a tournament on k vertices and an
      arc-preserving map from D to it (conjectures/colouring_variants.v); [dhom] - digraph
      homomorphism, arc-preserving, not required injective (conjectures/colouring_variants.v);
      [loopless] and [underlyingG] and [planar_sg] (conjectures/two_extremal.v).
    Notes: The corpus asks what the maximal oriented chromatic number of an oriented planar
      graph is; the body encodes the assertion that the maximum exists and is attained, which is
      the proposition a value of M would witness. Note M.-1 is natural-number predecessor, so at
      M = 0 the second clause would ask for a graph not 0-colourable. *)
Definition oriented_chromatic_number_of_planar_graphs_statement : Prop :=
  exists M : nat,
    (forall (D : diGraphType) (llD : loopless D),
        (forall u v : D, u --> v -> ~~ (v --> u)) ->
        planar_sg (underlyingG llD) -> oriented_kcolouring D M) /\
    (exists (D : diGraphType) (llD : loopless D),
        [/\ (forall u v : D, u --> v -> ~~ (v --> u)),
            planar_sg (underlyingG llD) & ~ oriented_kcolouring D M.-1]).

(** Corpus row: opg:oriented_trees_in_n_chromatic_digraphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/oriented_trees_in_n_chromatic_digraphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/oriented_trees_in_n_chromatic_digraphs.json
    English statement: (Open Problem Garden, Oriented trees in n-chromatic digraphs (Burr))
      For every finite digraph D and every k >= 2, if the ordinary chromatic number of the
      underlying simple graph of D is at least 2k-2, then D contains as a subdigraph every
      oriented tree T on k vertices, that is every orientation of a tree; containment means an
      injective arc-preserving map from T to D.
    Definitions: [oriented_tree T] - the underlying graph of T is a tree, encoded as weakly
      connected with #V - 1 arcs (this file); [contains_subdig D T] - injective arc-preserving
      map (this file); [underlying D] - the underlying simple graph (conjectures/chi_bounded.v);
      [chi] - coq-graph-theory's ordinary chromatic number of a vertex set.
    Notes: The chromatic number is the ORDINARY chi of the underlying simple graph (the
      Gallai-Roy / Burr lineage), not the dichromatic number: an earlier draft used ~~
      dicolorableb D (2*k-3), which is strictly weaker since the dichromatic number is at most
      chi. The definition of an oriented tree via arc count is valid because an oriented digraph
      has as many arcs as its underlying graph has edges. *)
Definition oriented_trees_in_n_chromatic_digraphs_statement : Prop :=
  forall (D : diGraphType) (k : nat), 2 <= k ->
    (2 * k - 2 <= χ([set: underlying D]))%N ->
    forall T : orientedDigraph, oriented_tree T -> #|T| = k -> contains_subdig D T.

(** Corpus row: opg:adams_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/adams_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/adams_conjecture.json
    English statement: (Open Problem Garden, Adam's Conjecture, tournament case)
      Every finite tournament that has at least one directed cycle has an arc whose reversal
      strictly decreases the number of directed cycles, where directed cycles are counted by
      their arc sets.
    Definitions: [ndicycles D] - the number of arc sets that are the arc set of a single
      directed cycle (this file); [single_dicycle_arcset A] - A is nonempty, made of real arcs,
      has equal in- and out-degree at most one at every vertex, and has connected support (this
      file); [rev_arc a] - the digraph with the single arc a reversed (this file); [tournament]
      (core/tournament.v).
    Notes: The general digraph form of the conjecture is disproved for multidigraphs (Grunbaum);
      this node deliberately encodes the still-open TOURNAMENT case, as the corpus status
      semantics prescribe. Counting cycles by arc sets makes the count independent of the
      starting vertex and of the direction of traversal. *)
Definition adams_statement : Prop :=
  forall T : tournament, (exists c : seq T, dicycle c) ->
    exists a : T * T, (a.1 --> a.2) /\ (ndicycles (rev_arc a) < ndicycles T).

(** Corpus row: opg:large_acyclic_induced_subdigraph_in_a_planar_oriented_graph
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/large_acyclic_induced_subdigraph_in_a_planar_oriented_graph/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/large_acyclic_induced_subdigraph_in_a_planar_oriented_graph.json
    English statement: (Open Problem Garden, Large acyclic induced subdigraph in a planar oriented graph)
      For every finite loopless digraph D with asymmetric arc relation (an oriented graph) whose
      underlying simple graph is planar, there is a vertex set S inducing an acyclic subdigraph
      with 3 * #|D| <= 5 * #|S|, that is with at least three fifths of the vertices.
    Definitions: [loopless] and [underlyingG] and [planar_sg] (conjectures/two_extremal.v);
      [acyclicb] (conjectures/dichromatic.v); [induced_digraph S] (core/digraph.v).
    Notes: The fraction 3/5 is cleared of division as 3 * n <= 5 * #|S|. Planarity is the Wagner
      minor form of the repo. *)
Definition large_acyclic_induced_subdigraph_in_a_planar_oriente_statement : Prop :=
  forall (D : diGraphType) (llD : loopless D),
    (forall u v : D, u --> v -> ~~ (v --> u)) ->
    planar_sg (underlyingG llD) ->
    exists S : {set D}, acyclicb (induced_digraph S) /\ (3 * #|D| <= 5 * #|S|).

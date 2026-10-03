(** * Cycle.foundations.spanning_trees — spanning trees of multigraphs as edge carriers

    Library migration B19, the multigraph contract of family [spanning-tree]
    (meta/library_primitives/spanning-tree.json), factored out of [Cycle.conjectures.U6]:

      [spanning_connected_edge_set G T] := every two vertices of the HOST [G] are joined by an
                                           undirected walk ([uwalk]) using only edges of [T];
      [spanning_tree_edge_set G T]      := [spanning_connected_edge_set T /\ acyclic_edge_set T].

    [T : {set edge G}] is an EDGE CARRIER of the multigraph (upstream [mgraph] edges with their
    reference orientation); connectivity quantifies over ALL host vertices through base's
    orientation-free [uwalk], so an isolated host vertex excludes every spanning tree when
    the host has at least two vertices, and
    [acyclic_edge_set] ([Cycle.foundations.path_subgraphs], the same body as U6's [acyclic])
    forbids every circuit: a selected loop is a circuit of length one and two distinct selected
    parallel edges a circuit of length two ([is_circuit_loop], [is_circuit_parallel]).  Edges
    OUTSIDE [T] are unconstrained: ambient loops and parallel edges are allowed, and no loopless,
    simplicity, [T != set0] or nonempty-host guard is part of the contract.

    Conventions, derived from the definitions and recorded below:
      - the empty host with the empty carrier is accepted vacuously;
      - one vertex with [T = set0] is accepted, even beside an unselected loop;
      - a single non-loop edge spans its two-vertex host in either reference orientation;
      - with a third, isolated vertex the same one-edge carrier is still connected on its
        incident support ([subgraph_connected]) but is NOT spanning-connected: the two notions
        differ exactly there, and [subgraph_connected] must not replace spanning connectivity;
      - a selected loop, two selected parallel edges and a selected digon are rejected.

    This is a different representation from [GTBase.spanning_trees.fg_spanning_tree] (labelled
    sets of unordered vertex pairs of a simple graph); no equivalence between the two is stated.
    [Cycle.foundations.connectivity.walk_in] is the Boolean form of the restricted walk
    ([spanning_connected_edge_setP]).

    IMPORT ORDER: [mgraph] before [base] (see [connectivity]). *)

From GraphTheory Require Import mgraph.
From GTBase Require Import base.
From Cycle.foundations Require Import connectivity path_subgraphs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SpanningTreeEdgeSet.
Variable G : mgraph.
Implicit Types (T : {set edge G}) (e f : edge G).

(** Every two host vertices are joined by an undirected walk inside [T]. *)
Definition spanning_connected_edge_set T : Prop :=
  forall x y : G, exists w, uwalk x y w /\ all (fun e => e \in T) w.

(** The contract: spanning-connected and without circuits. *)
Definition spanning_tree_edge_set T : Prop :=
  spanning_connected_edge_set T /\ acyclic_edge_set T.

Lemma spanning_tree_edge_setI T :
  spanning_connected_edge_set T -> acyclic_edge_set T -> spanning_tree_edge_set T.
Proof. by []. Qed.

Lemma spanning_tree_edge_set_connected T : spanning_tree_edge_set T -> spanning_connected_edge_set T.
Proof. by case. Qed.

Lemma spanning_tree_edge_set_acyclic T : spanning_tree_edge_set T -> acyclic_edge_set T.
Proof. by case. Qed.

(** The restricted walk in its Boolean form [walk_in]. *)
Lemma spanning_connected_edge_setP T :
  spanning_connected_edge_set T <-> forall x y : G, exists w, walk_in T x y w.
Proof.
split=> h x y; have [w hw] := h x y; exists w.
- by apply/andP.
- by apply/andP.
Qed.

(** Spanning connectivity connects the whole host. *)
Lemma spanning_connected_edge_set_mconnected T : spanning_connected_edge_set T -> mconnected G.
Proof. by move=> h x y; have [w [uw _]] := h x y; exists w. Qed.

Lemma spanning_tree_edge_set_mconnected T : spanning_tree_edge_set T -> mconnected G.
Proof. by case=> /spanning_connected_edge_set_mconnected. Qed.

(** Acyclicity is inherited by sub-carriers; connectivity by super-carriers. *)
Lemma spanning_connected_edge_set_sub T T' :
  T \subset T' -> spanning_connected_edge_set T -> spanning_connected_edge_set T'.
Proof.
move=> /subsetP sub h x y; have [w [uw aw]] := h x y; exists w; split=> //.
by apply/allP => e /(allP aw)/sub.
Qed.

(** Rejections: a selected loop, two distinct selected parallel edges. *)
Lemma spanning_tree_edge_set_noloop T e :
  source e = target e -> e \in T -> ~ spanning_tree_edge_set T.
Proof.
move=> loop eT [_ acyc]; apply: (acyc [set e]); last exact: is_circuit_loop.
by rewrite sub1set.
Qed.

Lemma spanning_tree_edge_set_noparallel T e f :
  e != f -> parallel_edges e f -> e \in T -> f \in T -> ~ spanning_tree_edge_set T.
Proof.
move=> ef par eT fT sT.
case: (boolP (source e == target e)) => [/eqP loop|ne].
- exact: spanning_tree_edge_set_noloop loop eT sT.
- case: sT => _ acyc; apply: (acyc [set e; f]); last exact: is_circuit_parallel.
  by apply/subsetP => g; rewrite !inE => /orP[/eqP->|/eqP->].
Qed.

End SpanningTreeEdgeSet.

(** ** Groundings: the conventions on coq-graph-theory's carriers *)

(** The empty host and the empty carrier: accepted vacuously. *)
Definition empty_host : mgraph := void_graph unit unit.

Lemma spanning_tree_edge_set_empty : spanning_tree_edge_set (@set0 (edge empty_host)).
Proof. by split; [move=> x; case: x | exact: acyclic_edge_set0]. Qed.

(** One vertex beside an unselected loop: the empty carrier spans it. *)
Definition one_loop : mgraph := mgraph.add_edge (unit_graph tt) tt tt tt.

Lemma spanning_tree_edge_set_one_vertex : spanning_tree_edge_set (@set0 (edge one_loop)).
Proof.
split; last exact: acyclic_edge_set0.
by move=> x y; exists [::]; split; [case: x; case: y|].
Qed.

(** Selecting the loop is rejected: a loop is a circuit. *)
Lemma not_spanning_tree_edge_set_loop : ~ spanning_tree_edge_set [set (None : edge one_loop)].
Proof. by apply: spanning_tree_edge_set_noloop (set11 _). Qed.

(** Two vertices and one edge, in either reference orientation: the edge spans the host. *)
Definition two_vertices : mgraph := two_graph tt tt.
Definition one_edge : mgraph := mgraph.add_edge two_vertices (inl tt) (inr tt) tt.
Definition one_edge_rev : mgraph := mgraph.add_edge two_vertices (inr tt) (inl tt) tt.

Lemma spanning_tree_edge_set_one_edge : spanning_tree_edge_set [set (None : edge one_edge)].
Proof.
split.
- move=> x y; case: x => -[]; case: y => -[].
  + by exists [::]; split; rewrite /= ?eqxx.
  + by exists [:: None]; split; rewrite /= ?inE ?eqxx ?orbT.
  + by exists [:: None]; split; rewrite /= ?inE ?eqxx ?orbT.
  + by exists [::]; split; rewrite /= ?eqxx.
- exact: path_subgraph_acyclic (path_subgraph_edge _).
Qed.

Lemma spanning_tree_edge_set_one_edge_rev : spanning_tree_edge_set [set (None : edge one_edge_rev)].
Proof.
split.
- move=> x y; case: x => -[]; case: y => -[].
  + by exists [::]; split; rewrite /= ?eqxx.
  + by exists [:: None]; split; rewrite /= ?inE ?eqxx ?orbT.
  + by exists [:: None]; split; rewrite /= ?inE ?eqxx ?orbT.
  + by exists [::]; split; rewrite /= ?eqxx.
- exact: path_subgraph_acyclic (path_subgraph_edge _).
Qed.

(** A third, isolated vertex: the one-edge carrier stays connected on its incident support but
    is no longer spanning-connected, so it is not a spanning tree. *)
Definition one_edge_and_vertex : mgraph := mgraph.add_vertex one_edge tt.

Lemma subgraph_connected_one_edge_and_vertex :
  subgraph_connected [set (inl None : edge one_edge_and_vertex)].
Proof.
move=> x y; rewrite !incident_set1 /incident => /existsP[b /eqP <-] /existsP[c /eqP <-].
case: b; case: c.
+ by exists [::]; rewrite /walk_in /= ?eqxx.
+ by exists [:: inl None]; rewrite /walk_in /= ?inE ?eqxx ?orbT.
+ by exists [:: inl None]; rewrite /walk_in /= ?inE ?eqxx ?orbT.
+ by exists [::]; rewrite /walk_in /= ?eqxx.
Qed.

Lemma uwalk_one_edge_and_vertex (w : seq (edge one_edge_and_vertex)) :
  ~~ uwalk (inr tt : one_edge_and_vertex) (inl (inl tt)) w.
Proof. by elim: w => [|[e|[]] w IH] //=; case: e => [[]|]. Qed.

Lemma not_spanning_connected_one_edge_and_vertex :
  ~ spanning_connected_edge_set [set (inl None : edge one_edge_and_vertex)].
Proof.
move=> /(_ (inr tt) (inl (inl tt))) [w [uw _]].
by move: (uwalk_one_edge_and_vertex w); rewrite uw.
Qed.

Lemma not_spanning_tree_edge_set_one_edge_and_vertex :
  ~ spanning_tree_edge_set [set (inl None : edge one_edge_and_vertex)].
Proof. by move=> /spanning_tree_edge_set_connected; exact: not_spanning_connected_one_edge_and_vertex. Qed.

(** Two distinct parallel edges, pointing the same way or forming a digon, are rejected. *)
Definition parallel_pair : mgraph := mgraph.add_edge one_edge (inl tt) (inr tt) tt.
Definition digon : mgraph := mgraph.add_edge one_edge (inr tt) (inl tt) tt.

Lemma not_spanning_tree_edge_set_parallel_pair : ~ spanning_tree_edge_set [set: edge parallel_pair].
Proof.
by apply: (@spanning_tree_edge_set_noparallel parallel_pair setT None (Some None)) => //;
  rewrite ?in_setT // /parallel_edges /= ?eqxx ?orbT.
Qed.

Lemma not_spanning_tree_edge_set_digon : ~ spanning_tree_edge_set [set: edge digon].
Proof.
by apply: (@spanning_tree_edge_set_noparallel digon setT None (Some None)) => //;
  rewrite ?in_setT // /parallel_edges /= ?eqxx ?orbT.
Qed.

(** Downstream use of the public path-subgraph API of [Cycle.foundations], without
    conjecture imports: the empty edge set, a single edge, a loop, and a digon
    (two parallel edges) on concrete multigraphs built with coq-graph-theory's
    constructors.  Degrees count arc ends, and no looplessness or simplicity
    premise is assumed. *)
From GraphTheory Require Import mgraph.
From GTBase Require Import base.
From Cycle.foundations Require Import connectivity path_subgraphs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Example empty_edge_set_is_no_path (G : mgraph) : ~ path_subgraph (@set0 (edge G)).
Proof. exact: path_subgraph_set0. Qed.

(** One edge between two vertices. *)
Definition one_edge : mgraph := mgraph.add_edge (two_graph tt tt) (inl tt) (inr tt) tt.

Example a_single_edge_is_a_path : path_subgraph [set (None : edge one_edge)].
Proof. exact: path_subgraph_edge. Qed.

(** One vertex with a loop: a loop is a circuit, so it is never part of a path. *)
Definition one_loop : mgraph := mgraph.add_edge (unit_graph tt) tt tt tt.

Example a_loop_is_no_path : ~ path_subgraph [set (None : edge one_loop)].
Proof. by move=> pP; exact: (@path_subgraph_noloop one_loop [set None] None erefl (set11 None) pP). Qed.

(** The digon: two oppositely oriented parallel edges between the same two vertices. *)
Definition digon : mgraph := mgraph.add_edge one_edge (inr tt) (inl tt) tt.

Example the_digon_is_no_path : ~ path_subgraph [set: edge digon].
Proof.
move=> pP.
exact: (@path_subgraph_noparallel digon [set: edge digon] (Some None) None isT isT
  (in_setT _) (in_setT _) pP).
Qed.

Example each_digon_edge_is_a_path : path_subgraph [set (None : edge digon)].
Proof. exact: path_subgraph_edge. Qed.

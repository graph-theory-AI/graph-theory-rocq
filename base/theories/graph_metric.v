(** * GTBase.graph_metric -- finite graph metric lines and bridges *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph.
From GTBase Require Import simple_edges.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Closed ball for an arbitrary finite relation. *)
Fixpoint rel_ball (T : finType) (r : rel T) (k : nat) (x : T) : {set T} :=
  if k is k'.+1 then
    rel_ball r k' x :|: \bigcup_(z in rel_ball r k' x) [set y | r z y]
  else [set x].
Arguments rel_ball {T} r k x.

(** Shortest-path distance in the connected component, truncated by the finite
    search bound.  In connected graphs this is the usual graph metric. *)
Lemma graph_dist_ex (G : sgraph) (x y : G) :
  exists k : nat, (y \in rel_ball (--) k x) || (k == #|G|).
Proof. by exists #|G|; rewrite eqxx orbT. Qed.

Definition graph_dist (G : sgraph) (x y : G) : nat :=
  ex_minn (graph_dist_ex x y).

Definition graph_between (G : sgraph) (u v w : G) : bool :=
  graph_dist u v + graph_dist v w == graph_dist u w.

(** Chen-Chvatal line through [a,b]: all vertices [x] such that one of
    [a,b,x] lies between the other two in the shortest-path metric. *)
Definition metric_line (G : sgraph) (a b : G) : {set G} :=
  [set x : G |
      graph_between a b x || graph_between a x b || graph_between x a b].

Definition metric_line_count (G : sgraph) : nat :=
  #|[set L : {set G} |
      [exists a : G, [exists b : G, (a != b) && (L == metric_line a b)]]]|.

(** Deprecated compatibility name.  New code should use [simple_edge_set]. *)
Definition graph_edge_set (G : sgraph) : {set {set G}} :=
  simple_edge_set G.

Definition edge_deleted_rel (G : sgraph) (e : {set G}) : rel G :=
  fun x y => (x -- y) && ~~ ((x \in e) && (y \in e)).

(** A bridge is an edge whose endpoints are disconnected after deleting that
    edge.  The bounded reachability search is exact for finite simple graphs. *)
Definition graph_bridge (G : sgraph) (e : {set G}) : bool :=
  (e \in graph_edge_set G) &&
  [exists x in e,
    [exists y in e, (x != y) && ~~ (y \in rel_ball (edge_deleted_rel e) #|G| x)]].

Definition bridge_count (G : sgraph) : nat :=
  #|[set e in graph_edge_set G | graph_bridge e]|.

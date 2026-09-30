(** * Digraph.conjectures.X17 -- v2 oriented-path and unavoidability rows *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented tournament.
From Digraph.conjectures Require Import X2 unvd.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X17 vocabulary ************************************************)

Definition x17_min_semidegree_strict_half (D : diGraphType) (k : nat) : Prop :=
  forall v : D, (k < 2 * outdeg v)%N /\ (k < 2 * classic_core.indeg v)%N.

(** ** X17 statements ******************************************************)

(** Corpus row: studies:std_stein_s_conjecture_on_oriented_paths
    Site: none
    Review: none
    English statement: (Stein, conjecture on oriented paths)
      For every k >= 1 and every nonempty finite oriented graph G whose minimum semidegree is
      strictly greater than k/2 (written without division as k < 2 * outdeg v and k < 2 * indeg
      v at every vertex), G contains as a subdigraph every orientation of the path with k edges.
    Definitions: [x17_min_semidegree_strict_half G k] - the strict semidegree condition (this
      file); [oriented_path P k] - P is an orientation of the path with k edges, that is k+1
      vertices (conjectures/X2.v); [subdigraph_embed P G] - injective arc-preserving map
      (conjectures/X2.v); [classic_core.indeg] (conjectures/classic_core.v); [outdeg]
      (core/oriented.v).
    Notes: This is the strict-threshold companion of [semidegree_oriented_paths_statement]
      (conjectures/X2.v), which uses the non-strict threshold and therefore has to exclude
      antidirected paths; at the strict threshold no exception is needed. *)
Definition stein_oriented_paths_strict_semidegree_statement : Prop :=
  forall (k : nat) (G : orientedDigraph),
    0 < k ->
    (0 < #|G|)%N ->
    x17_min_semidegree_strict_half G k ->
    forall P : orientedDigraph,
      oriented_path P k -> subdigraph_embed P G.

(** Corpus row: studies:std_sumner_s_conjecture
    Site: none
    Review: none
    English statement: (Sumner, tournament-unavoidability conjecture)
      Every oriented tree T on n > 1 vertices is (2n-2)-unavoidable: every tournament on 2n-2
      vertices contains T as a subdigraph via an injective arc-preserving map.
    Definitions: [oriented_tree T] - nonempty orientation of a tree, underlying graph a
      connected forest (conjectures/X2.v); [unavoidable D N] - every tournament on exactly N
      vertices contains D (conjectures/unvd.v); [contains_subdigraph] (conjectures/unvd.v).
    Notes: [unavoidable] quantifies over tournaments of exactly N vertices; the subtraction 2 *
      n - 2 is natural-number subtraction, harmless under the guard 1 < n. *)
Definition sumner_oriented_tree_unavoidable_statement : Prop :=
  forall (n : nat) (T : orientedDigraph),
    1 < n ->
    oriented_tree T ->
    #|T| = n ->
    unavoidable T (2 * n - 2).

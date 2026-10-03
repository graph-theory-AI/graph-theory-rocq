(** Downstream use of degree balance ([Digraph.foundations.degree_balance]: [indeg], [balanced],
    [balancedb]), without conjecture imports.  Each example uses public API lemmas only. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra.
From Digraph Require Import prelude digraph oriented tournament.
From Digraph.foundations Require Import degree_balance.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section AnyDigraph.
Variable D : diGraphType.

(** The Boolean and Prop forms agree ... *)
Example forms : reflect (balanced D) (balancedb D).
Proof. exact: balancedP. Qed.

(** ... and the reversed equation is the same condition. *)
Example reversed : (forall v : D, outdeg v = indeg v) <-> balanced D.
Proof. exact: balanced_revE. Qed.

(** Balance is a per-vertex condition, invariant under the converse digraph, and the degree sums
    agree on every digraph. *)
Example per_vertex_converse_handshake (v : D) :
  [/\ balanced D -> indeg v = outdeg v, balanced (converse D) <-> balanced D
    & \sum_(u : D) indeg u = \sum_(u : D) outdeg u].
Proof. by split; [exact: balanced_vertex | exact: balanced_converse | exact: sum_indeg_outdeg]. Qed.

(** No connectivity or looplessness premise: an arcless digraph is balanced. *)
Example arcless_balanced : (forall u v : D, ~~ (u --> v)) -> balanced D.
Proof. exact: balanced_arcless. Qed.

End AnyDigraph.

(** Concrete corners: the empty and the arcless one-vertex digraphs; a vertex with a loop (balanced,
    the loop counting on both sides); two disjoint loops (balanced and disconnected); the digon and
    the directed triangle; and the single arc, which is NOT balanced. *)
Example corners :
  [/\ balanced empty_dg, balanced arcless1, balanced loop1, balanced twoloops & balanced digon].
Proof.
split; [exact: balanced_ground_empty | exact: balanced_ground_arcless | by case: balanced_ground_loop |
  by case: balanced_ground_disconnected | exact: balanced_ground_digon].
Qed.

Example triangle_and_single_arc : balanced C3 /\ ~ balanced (TT 2).
Proof. by split; [exact: balanced_ground_C3 | exact: not_balanced_ground_TT2]. Qed.

Print Assumptions per_vertex_converse_handshake.
Print Assumptions triangle_and_single_arc.

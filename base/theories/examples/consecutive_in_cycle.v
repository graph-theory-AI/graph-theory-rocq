(** Downstream use of the public cyclic-adjacency API, without corpus imports:
    both interfaces (Prop and boolean, related by reflection), the empty sequence,
    a one-vertex sequence relating its vertex to itself, a two-vertex sequence with
    its closing pair, the closing pair of a longer sequence, rotation and reversal,
    the open-path relation as a special case, and the edges of a graph cycle. *)
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PublicClient.
Variable G : sgraph.

Example empty_cycle_has_no_adjacent_pair (u v : G) : ~ seq_cyclic_consecutive [::] u v.
Proof. exact: seq_cyclic_consecutive_nil. Qed.

(** No distinctness premise: a one-vertex sequence relates its vertex to itself. *)
Example one_vertex_is_self_adjacent (x : G) : seq_cyclic_consecutive [:: x] x x.
Proof. exact/seq_cyclic_consecutive_seq1. Qed.

Example two_vertices_both_orders (x y : G) :
  seq_cyclic_consecutive [:: x; y] x y /\ seq_cyclic_consecutive [:: x; y] y x.
Proof. by split; apply/seq_cyclic_consecutive_pair; [left | right]. Qed.

Example closing_pair_is_adjacent (x : G) (s : seq G) :
  seq_cyclic_consecutive (x :: s) (last x s) x.
Proof. exact: seq_cyclic_consecutive_last. Qed.

Example boolean_interface (c : seq G) (u v : G) :
  seq_cyclic_consecutiveb c u v -> seq_cyclic_consecutive c v u.
Proof. by move/seq_cyclic_consecutiveP/seq_cyclic_consecutive_sym. Qed.

Example rotation_invariance (n : nat) (c : seq G) (u v : G) :
  seq_cyclic_consecutiveb (rot n c) u v = seq_cyclic_consecutiveb c u v.
Proof. exact: seq_cyclic_consecutiveb_rot. Qed.

Example reversal_invariance (c : seq G) (u v : G) :
  seq_cyclic_consecutive (rev c) u v <-> seq_cyclic_consecutive c u v.
Proof. exact: seq_cyclic_consecutive_rev. Qed.

Example open_adjacency_is_cyclic (s : seq G) (u v : G) :
  seq_consecutive s u v -> seq_cyclic_consecutive s u v.
Proof. exact: seq_consecutive_cyclic. Qed.

(** On a graph cycle, cyclically consecutive vertices are adjacent. *)
Example cycle_neighbours_are_adjacent (c : seq G) (u v : G) :
  cycle (--) c -> seq_cyclic_consecutive c u v -> u -- v.
Proof. by move=> cyc /(seq_cyclic_consecutive_cycle cyc); rewrite (sg_sym v) orbb. Qed.

End PublicClient.

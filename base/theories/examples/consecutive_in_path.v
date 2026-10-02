(** Downstream use of the public consecutive-entry API, without corpus imports:
    the empty and one-vertex sequences, an adjacent pair in both orders, a
    repeated adjacent vertex, a non-adjacent pair, reversal, the edges of a graph
    path and of a packaged path, and an induced-path style use in which
    consecutive entries are the only adjacent pairs. *)
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PublicClient.
Variable G : sgraph.

Example empty_sequence_has_no_consecutive_pair (u v : G) : ~ seq_consecutive [::] u v.
Proof. exact: seq_consecutive_nil. Qed.

Example one_vertex_has_no_consecutive_pair (x u v : G) : ~ seq_consecutive [:: x] u v.
Proof. exact: seq_consecutive_seq1. Qed.

Example adjacent_pair_both_orders (x y : G) (s : seq G) :
  seq_consecutive [:: x, y & s] x y /\ seq_consecutive [:: x, y & s] y x.
Proof. by split; apply/seq_consecutive_cons2; [constructor 1 | constructor 2]. Qed.

(** No distinct-endpoint premise: a repeated adjacent vertex is consecutive to
    itself. *)
Example repeated_vertex_is_self_consecutive (x : G) : seq_consecutive [:: x; x] x x.
Proof. exact: seq_consecutive_repeat. Qed.

Example consecutive_entries_occur (s : seq G) (u v : G) :
  seq_consecutive s u v -> u \in s /\ v \in s.
Proof. exact: seq_consecutive_mem. Qed.

Example reversed_sequence (s : seq G) (u v : G) :
  seq_consecutive (rev s) u v <-> seq_consecutive s u v.
Proof. exact: seq_consecutive_rev. Qed.

Example consecutive_on_a_path_are_adjacent (x : G) (s : seq G) (u v : G) :
  path (--) x s -> seq_consecutive (x :: s) u v -> u -- v.
Proof. by apply: seq_consecutive_path_sym; exact: sg_sym. Qed.

Example consecutive_on_a_packaged_path_are_adjacent (x y : G) (p : Path x y) (u v : G) :
  seq_consecutive (nodes p) u v -> u -- v.
Proof. by move/seq_consecutive_nodes; rewrite (sg_sym v) orbb. Qed.

(** An induced-path style condition: on [[:: x; y; z]] with an edge between the
    ends, the ends would have to be consecutive, which they are not. *)
Example ends_of_three_are_not_consecutive (x y z : G) :
  x != y -> y != z -> x != z -> ~ seq_consecutive [:: x; y; z] x z.
Proof.
move=> xy yz xz /seq_consecutive_cons2[[_ /eqP]|[/eqP]|/seq_consecutive_pair[[/eqP]|[/eqP]]].
- by rewrite eq_sym (negbTE yz).
- by rewrite (negbTE xy).
- by rewrite (negbTE xy).
- by rewrite (negbTE xz).
Qed.

End PublicClient.

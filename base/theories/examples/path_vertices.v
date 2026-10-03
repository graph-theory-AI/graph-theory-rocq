(** Downstream use of the public vertex-sequence API, without corpus imports:
    the support of the empty sequence, a walk with a repeated vertex, and the
    head-plus-tail form [x :: s] of the library's packaged paths. *)
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PublicClient.
Variable G : sgraph.

Example empty_sequence_has_no_vertex : seq_vertices ([::] : seq G) = set0.
Proof. exact: seq_vertices_nil. Qed.

Example repeated_vertex_counts_once (u v : G) :
  seq_vertices [:: u; v; u] = [set u; v].
Proof.
by apply/setP => z; rewrite in_seq_vertices !inE; case: (z == u); case: (z == v).
Qed.

Example repeated_walk_has_two_vertices (u v : G) :
  u != v -> #|seq_vertices [:: u; v; u]| = 2.
Proof. by move=> uv; rewrite repeated_vertex_counts_once cards2 uv. Qed.

Example head_plus_tail_contains_head (x : G) (s : seq G) :
  x \in seq_vertices (x :: s).
Proof. exact: seq_vertices_head. Qed.

Example packaged_path_support (x y : G) (p : Path x y) :
  seq_vertices (x :: val p) = [set z in p].
Proof. exact: seq_vertices_val. Qed.

End PublicClient.

Example triangle_walk_has_two_vertices :
  #|seq_vertices [:: ord0; ord_max; ord0 : 'K_3]| = 2.
Proof. by rewrite card_seq_vertices. Qed.

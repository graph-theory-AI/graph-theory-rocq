(** Downstream use of the public internal-vertex API, without corpus imports:
    the empty sequence, a single edge, an endpoint value repeated inside the
    sequence, the head-plus-tail form, a packaged path, an endpoint that is never
    internal, and the own-endpoint variant [seq_inner]. *)
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PublicClient.
Variable G : sgraph.

Example empty_sequence_has_no_internal_vertex (x y : G) : seq_interior x y [::] = set0.
Proof. exact: seq_interior_nil. Qed.

Example single_edge_has_no_internal_vertex (x y : G) : seq_interior x y [:: x; y] = set0.
Proof. by rewrite seq_interior_head seq_interior_seq1 eqxx orbT. Qed.

Example repeated_endpoint_is_not_internal (x y : G) : seq_interior x y [:: x; x; y] = set0.
Proof. by rewrite !seq_interior_head seq_interior_seq1 eqxx orbT. Qed.

Example head_plus_tail_interior (x y : G) (s : seq G) :
  seq_interior x y (x :: s) = seq_interior x y s.
Proof. exact: seq_interior_head. Qed.

Example packaged_path_interior (x y : G) (p : Path x y) :
  seq_interior x y (x :: val p) = interior p.
Proof. exact: seq_interior_val. Qed.

Example endpoint_is_never_internal (x y : G) (s : seq G) : x \notin seq_interior x y s.
Proof. by rewrite in_seq_interior eqxx andbF. Qed.

Example internal_vertices_lie_on_the_sequence (x y z : G) (s : seq G) :
  z \in seq_interior x y s -> z \in s.
Proof. by rewrite in_seq_interior => /and3P[]. Qed.

Example singleton_has_no_inner_vertex (v : G) : seq_inner [:: v] = set0.
Proof. exact: seq_inner_seq1. Qed.

End PublicClient.

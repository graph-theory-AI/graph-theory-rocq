(** Downstream use of the public simple-walk API, without corpus imports: the
    empty sequence (a simple walk but not a path), a one-vertex walk, a two-vertex
    walk exactly at an edge, repeated vertices, the explicit nonempty bridge to
    [seq_simple_path], and the upstream [upath] form. *)
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PublicClient.
Variable G : sgraph.

(** The empty sequence is a simple walk, but not a simple path. *)
Example empty_walk_is_not_a_path :
  seq_simple_walk ([::] : seq G) /\ ~ seq_simple_path ([::] : seq G).
Proof. by split; [exact: seq_simple_walk_nil | exact: seq_simple_path_nil]. Qed.

Example one_vertex_walk (x : G) : seq_simple_walk [:: x].
Proof. exact: seq_simple_walk_seq1. Qed.

Example two_vertex_walk_at_an_edge (x y : G) : seq_simple_walk [:: x; y] = x -- y.
Proof.
rewrite seq_simple_walk_pair; case xy: (x -- y); rewrite ?andbF ?andbT //.
by apply: contraTneq xy => ->; rewrite sg_irrefl.
Qed.

Example repeated_vertices_are_excluded (x y : G) : ~~ seq_simple_walk [:: x; y; x].
Proof. by apply: seq_simple_walk_repeat; rewrite /= !inE eqxx orbT. Qed.

(** A nonempty simple walk is a simple path, and conversely. *)
Example nonempty_walks_are_paths (s : seq G) :
  s != [::] -> seq_simple_walk s -> seq_simple_path s.
Proof. by move=> ne w; apply/seq_simple_path_walk. Qed.

Example upstream_upath (x : G) (q : seq G) :
  seq_simple_walk (x :: q) = upath x (last x q) q.
Proof. exact: seq_simple_walk_upath. Qed.

End PublicClient.

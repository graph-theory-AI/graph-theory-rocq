(** Downstream use of the public simple-path API, without corpus imports: the empty
    sequence, a one-vertex path, a two-vertex path exactly at an edge, repeated
    vertices, reversal in a simple graph, the upstream [upath] bridge, packaged
    paths, set-to-set paths, maps that are injective and keep adjacency, an
    accepted chorded path of the triangle and a rejected non-edge of the 4-cycle. *)
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PublicClient.
Variable G : sgraph.

Example empty_sequence_is_no_path : ~ seq_simple_path ([::] : seq G).
Proof. exact: seq_simple_path_nil. Qed.

Example one_vertex_is_a_path (x : G) : seq_simple_path [:: x].
Proof. exact: seq_simple_path_seq1. Qed.

Example two_vertices_form_a_path_exactly_at_an_edge (x y : G) :
  seq_simple_path [:: x; y] <-> x -- y.
Proof.
rewrite seq_simple_path_pair; split=> [[_ //]|xy]; split=> //.
by apply: contraTneq xy => ->; rewrite sg_irrefl.
Qed.

Example repeated_vertices_are_excluded (x y : G) : ~ seq_simple_path [:: x; y; x].
Proof. by apply: seq_simple_path_repeat; rewrite /= !inE eqxx orbT. Qed.

Example reversal (p : seq G) : seq_simple_path p -> seq_simple_path (rev p).
Proof. exact/seq_simple_path_rev/sg_sym. Qed.

Example upstream_upath (x : G) (q : seq G) :
  seq_simple_path (x :: q) <-> upath x (last x q) q.
Proof. exact: seq_simple_path_upath. Qed.

Example packaged_path (x y : G) (p : Path x y) : irred p -> seq_simple_path (nodes p).
Proof. exact: seq_simple_path_nodes. Qed.

Example set_paths_are_simple_paths (X Y : {set G}) (p : seq G) :
  seq_set_path X Y p -> seq_simple_path p.
Proof. exact: seq_set_path_simple. Qed.

Example map_of_a_path (H : sgraph) (f : G -> H) (p : seq G) :
  injective f -> {homo f : x y / x -- y} -> seq_simple_path p -> seq_simple_path (map f p).
Proof. exact: seq_simple_path_map. Qed.

End PublicClient.

(** Chords are allowed: the triangle's vertices in order form a path. *)
Example chorded_triangle_path :
  seq_simple_path ([:: @Ordinal 3 0 isT; @Ordinal 3 1 isT; @Ordinal 3 2 isT] : seq 'K_3).
Proof. by split. Qed.

(** A non-edge is not a path: opposite vertices of the 4-cycle. *)
Example nonedge_of_the_four_cycle :
  ~ seq_simple_path ([:: @Ordinal 4 0 isT; @Ordinal 4 2 isT] : seq (cycle_graph 4)).
Proof. by case/seq_simple_path_pair. Qed.

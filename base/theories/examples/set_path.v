(** Downstream use of the public set-to-set path API, without corpus imports: the
    empty sequence, a one-vertex path exactly in the intersection of the endpoint
    sets, empty endpoint sets, repeated vertices, an edge of the triangle as a
    two-vertex path, reversal in a simple graph, the upstream [upath] bridge, and
    the vertex list of an irredundant packaged path. *)
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PublicClient.
Variable G : sgraph.

Example empty_sequence_is_no_path (X Y : {set G}) : ~ seq_set_path X Y [::].
Proof. exact: seq_set_path_nil. Qed.

(** No disjointness or distinct-endpoint premise: a one-vertex path lies in both sets. *)
Example one_vertex_path (X Y : {set G}) (x : G) :
  x \in X -> x \in Y -> seq_set_path X Y [:: x].
Proof. by move=> xX xY; apply/seq_set_path_seq1; rewrite inE xX xY. Qed.

Example no_path_from_an_empty_set (Y : {set G}) (p : seq G) : ~ seq_set_path set0 Y p.
Proof. exact: seq_set_path_set0l. Qed.

Example repeated_vertices_are_excluded (X Y : {set G}) (x : G) : ~ seq_set_path X Y [:: x; x].
Proof. by apply: seq_set_path_repeat; rewrite /= inE eqxx. Qed.

Example reversal (X Y : {set G}) (p : seq G) :
  seq_set_path X Y p -> seq_set_path Y X (rev p).
Proof. exact/seq_set_path_rev/sg_sym. Qed.

Example upstream_upath (X Y : {set G}) (x : G) (q : seq G) :
  seq_set_path X Y (x :: q) -> upath x (last x q) q.
Proof. by case/seq_set_path_upath. Qed.

Example packaged_path (x y : G) (p : Path x y) :
  irred p -> seq_set_path [set x] [set y] (nodes p).
Proof. by move=> ip; apply: seq_set_path_nodes; rewrite ?inE. Qed.

Example consecutive_vertices_are_adjacent (X Y : {set G}) (p : seq G) (u v : G) :
  seq_set_path X Y p -> seq_consecutive p u v -> u -- v.
Proof. by move=> pp /(seq_set_path_consecutive pp); rewrite (sg_sym v) orbb. Qed.

End PublicClient.

(** An edge of the triangle is a two-vertex path between its endpoints. *)
Example triangle_edge_is_a_path :
  seq_set_path [set ord0 : 'K_3] [set ord_max : 'K_3] [:: ord0; ord_max].
Proof. by apply/seq_set_path_cons; rewrite /= !inE !eqxx. Qed.

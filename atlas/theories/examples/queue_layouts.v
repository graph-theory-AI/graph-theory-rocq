(** Public-only clients of [Atlas.foundations.queue_layouts].  They import only GTBase and that
    foundation (no conjecture or migration module).  Ordering by an injective key: sorting the
    enumeration of ['I_n] by [val] puts the vertices in their own order, a one-vertex type is
    sorted trivially and the empty type gives the empty sequence; injectivity is needed, since a
    constant key leaves two distinct vertices at different positions with equal keys.  Edges:
    every member of [E(G)] is its two named ends, read in either order, and the two ends must be
    distinct, since an edge is never the set of one repeated end. *)
From GTBase Require Import base.
From Atlas.foundations Require Import queue_layouts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Sorting by an injective key *)

Example sort_by_val (n : nat) (a b : 'I_n) :
  let s := sort (fun x y : 'I_n => val x <= val y) (enum 'I_n) in
  (index a s < index b s) = (a < b).
Proof. exact: sort_index_lt val_inj. Qed.

Example sort_index_singleton (key : 'I_1 -> nat) :
  let s := sort (fun x y => key x <= key y) (enum 'I_1) in
  (index ord0 s < index ord0 s) = (key ord0 < key ord0).
Proof. by apply: sort_index_lt => x y _; rewrite (ord1 x) (ord1 y). Qed.

Example sort_empty (key : 'I_0 -> nat) :
  size (sort (fun x y => key x <= key y) (enum 'I_0)) = 0.
Proof. by rewrite size_sort -cardE card_ord. Qed.

Example sort_index_needs_injective :
  let key := fun _ : 'I_2 => 0 in
  let s := sort (fun x y => key x <= key y) (enum 'I_2) in
  exists a b : 'I_2, (index a s < index b s) != (key a < key b).
Proof.
cbv zeta; set s := sort _ _.
have ms (x : 'I_2) : x \in s by rewrite mem_sort mem_enum.
have ne : index (@ord0 1) s != index (@ord_max 1) s.
  apply/eqP => e; have := nth_index (@ord0 1) (ms (@ord_max 1)).
  by rewrite -e (nth_index _ (ms _)) => /(congr1 val).
case: (ltnP (index (@ord0 1) s) (index (@ord_max 1) s)) => [lt|le].
- by exists ord0, ord_max; rewrite lt.
- have gt : index (@ord_max 1) s < index (@ord0 1) s by rewrite ltn_neqAle eq_sym ne le.
  by exists ord_max, ord0; rewrite gt.
Qed.

(** ** The ends of an edge of [E(G)] *)

Example edge_ends_total (G : sgraph) (e : {set G}) (a d : G) :
  e \in E(G) -> a \in e -> d \in e -> a != d -> e = [set a; d] /\ a -- d.
Proof. exact: x158_edge_ends. Qed.

Example edge_ends_reversed (G : sgraph) (x y : G) :
  x -- y -> [set x; y] = [set y; x] /\ y -- x.
Proof.
move=> xy; apply: x158_edge_ends; first by rewrite in_edges.
- by rewrite !inE eqxx orbT.
- by rewrite !inE eqxx.
- by rewrite eq_sym (sg_edgeNeq xy).
Qed.

Example edge_ends_need_distinct (G : sgraph) (x y : G) :
  x -- y -> [set x; y] != [set x; x].
Proof.
move=> xy; apply/eqP => /setP /(_ y).
by rewrite !inE eqxx orbT eq_sym (sg_edgeNeq xy).
Qed.

(** * GTBase.examples.induced_paths — public-only client of [GTBase.induced_paths] (B22)

    Exercises the induced-path views through the public API alone: no conjecture module is imported
    (the concrete carriers are the complete graphs and B21's ordinal path graph).  Corners: the empty
    and singleton sequences, a repeated entry, a three-vertex path accepted in P_3 but the same order
    rejected in the triangle K_3, reversal exchanging the endpoints, the X67 length guard, exact orders
    0 and 1, and the conditional index bridge (membership is needed). *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph.
From GTBase Require Import base path_graphs induced_paths.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Empty, singleton and repeated sequences *)

(** The empty sequence is an induced path for the empty-allowed view only. *)
Lemma empty_sequence_allowed (G : sgraph) : induced_path ([::] : seq G).
Proof. exact: induced_path_nil. Qed.

Lemma empty_sequence_not_nonempty (G : sgraph) : ~ nonempty_induced_path ([::] : seq G).
Proof. exact: not_nonempty_induced_path_nil. Qed.

Lemma empty_sequence_joins_nothing (G : sgraph) (a b : G) : ~ induced_path_between a b [::].
Proof. exact: not_induced_path_between_nil. Qed.

(** A single vertex is a (nonempty) induced path, and it joins a to b exactly when both are it. *)
Lemma singleton_is_a_path (G : sgraph) (x : G) : nonempty_induced_path [:: x].
Proof. exact: nonempty_induced_path_seq1. Qed.

Lemma singleton_endpoints (G : sgraph) (a b x : G) :
  induced_path_between a b [:: x] <-> x = a /\ x = b.
Proof. exact: induced_path_between_seq1. Qed.

(** A repeated entry is rejected. *)
Lemma repeated_entry_rejected (G : sgraph) (x : G) (p : seq G) : ~ induced_path (x :: x :: p).
Proof. exact: not_induced_path_repeat. Qed.

(** ** A path versus a triangle *)

Section ThreeVertices.
Definition p3 : ordinal_path 3 := ord0.
Definition q3 : ordinal_path 3 := @Ordinal 3 1 isT.
Definition r3 : ordinal_path 3 := ord_max.

Lemma q3E : val q3 = 1.
Proof. by []. Qed.

(** In P_3 the sequence 0, 1, 2 is an induced path from 0 to 2. *)
Lemma three_vertex_path_accepted : induced_path_between p3 r3 [:: p3; q3; r3].
Proof.
have uq : uniq [:: p3; q3; r3] by vm_compute.
have pth : path (--) p3 [:: q3; r3] by vm_compute.
do ?split=> //.
move=> u v; rewrite !inE => /or3P[/eqP-> | /eqP-> | /eqP->] /or3P[/eqP-> | /eqP-> | /eqP->] uv ne;
  vm_compute in uv; vm_compute in ne; try done.
- by left; vm_compute.
- by right; vm_compute.
- by left; vm_compute.
- by right; vm_compute.
Qed.

(** In the triangle the same order has the chord 0 -- 2: not induced. *)
Lemma triangle_order_rejected : ~ induced_path [:: ord0 : 'K_3; @Ordinal 3 1 isT; ord_max].
Proof.
move/induced_path_chordless => /(_ ord0 ord_max).
have m1 : (ord0 : 'K_3) \in [:: ord0; @Ordinal 3 1 isT; ord_max] by vm_compute.
have m2 : (ord_max : 'K_3) \in [:: ord0; @Ordinal 3 1 isT; ord_max] by vm_compute.
have adj : (ord0 : 'K_3) -- ord_max by vm_compute.
have ne : (ord0 : 'K_3) != ord_max by vm_compute.
by move=> /(_ m1 m2 adj ne) [] h; vm_compute in h.
Qed.

End ThreeVertices.

(** ** Reversal exchanges the endpoints *)

Lemma reversal_swaps_endpoints (G : sgraph) (a b : G) (p : seq G) :
  induced_path_between a b p -> induced_path_between b a (rev p).
Proof. exact: induced_path_between_rev. Qed.

Lemma reversal_keeps_inducedness (G : sgraph) (p : seq G) : induced_path (rev p) <-> induced_path p.
Proof. exact: induced_path_rev. Qed.

(** ** The X67 length guard *)

(** The single edge of K_2 is an induced path between its ends but has only two vertices. *)
Lemma edge_is_a_path : induced_path_between (ord0 : 'K_2) ord_max [:: ord0; ord_max].
Proof.
have uq : uniq [:: ord0 : 'K_2; ord_max] by vm_compute.
have pth : path (--) (ord0 : 'K_2) [:: ord_max] by vm_compute.
do ?split=> //.
move=> u v; rewrite !inE => /orP[/eqP-> | /eqP->] /orP[/eqP-> | /eqP->] uv ne; vm_compute in uv; vm_compute in ne; try done.
- by left; vm_compute.
- by right; vm_compute.
Qed.

Lemma edge_too_short_for_x67 : ~ long_induced_path_between (ord0 : 'K_2) ord_max [:: ord0; ord_max].
Proof. by move/long_induced_path_between_size. Qed.

Lemma long_view_is_the_guarded_view (G : sgraph) (a b : G) (p : seq G) :
  long_induced_path_between a b p <-> induced_path_between a b p /\ 3 <= size p.
Proof. exact: long_induced_path_betweenP. Qed.

(** ** Exact orders *)

Lemma no_induced_path_of_order_zero (G : sgraph) : ~ has_induced_path_of_order G 0.
Proof. exact: has_induced_path_of_order0. Qed.

Lemma order_one_iff_a_vertex (G : sgraph) : has_induced_path_of_order G 1 <-> 0 < #|G|.
Proof. exact: has_induced_path_of_order1. Qed.

Lemma order_one_in_the_empty_graph : ~ has_induced_path_of_order 'K_0 1.
Proof. by move/has_induced_path_of_order1; rewrite card_ord. Qed.

(** ** The index bridge is conditional *)

(** For members of a duplicate-free list, consecutiveness is the index relation... *)
Lemma index_bridge_for_members (G : sgraph) (p : seq G) (u v : G) :
  uniq p -> u \in p -> v \in p ->
  seq_consecutive p u v <-> (index u p).+1 = index v p \/ (index v p).+1 = index u p.
Proof. exact: seq_consecutive_index. Qed.

(** ... but the index relation alone says nothing for a non-member: [index b [:: a] = 1] for every
    [b] other than [a], although [b] is not consecutive to anything in [[:: a]]. *)
Lemma index_bridge_needs_membership (G : sgraph) (a b : G) :
  a != b -> (index a [:: a]).+1 = index b [:: a] /\ ~ seq_consecutive [:: a] a b.
Proof. by move=> ab; split; [exact: index_relation_non_member | exact: seq_consecutive_seq1]. Qed.

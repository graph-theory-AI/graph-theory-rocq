(** Public-only client of the supplied-partition API of [Hypergraph.foundations.hypergraph]
    ([hg_partite_uniform part E]: every member of [E] meets each class of the supplied map [part]
    in exactly one vertex).  No conjecture module is imported.  Positive: the empty family at every
    rank, the identity-partitioned full edge, rank 0 with the empty family and the singleton empty
    edge, an isolated vertex, subfamilies and vertex deletion.  Consequences: member cardinality
    and D1 uniformity, and, under a member premise only, an onto map and [k <= #|T|].  Negative:
    uniformity does not give partiteness for a constant map, and without a member the map need not
    be onto. *)
From GTBase Require Import base hypergraph_uniformity.
From Hypergraph.foundations Require Import hypergraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Positive instances *)

Example empty_family_every_rank (T : finType) (k : nat) (part : T -> 'I_k) :
  hg_partite_uniform part (set0 : {set {set T}}).
Proof. exact: hg_partite_uniform0. Qed.

Example identity_full_edge_rank3 : hg_partite_uniform (fun v : 'I_3 => v) [set [set: 'I_3]].
Proof. exact: hg_partite_uniform_ord. Qed.

(** Rank 0: the carrier is empty; the empty family and the singleton empty edge both pass. *)
Example rank0_empty_carrier (T : finType) (part : T -> 'I_0) : #|T| = 0.
Proof. exact: hg_partite_rank0_card part. Qed.

Example rank0_empty_family (T : finType) (part : T -> 'I_0) :
  hg_partite_uniform part (set0 : {set {set T}}).
Proof. exact: hg_partite_uniform_rank0. Qed.

Example rank0_empty_edge (T : finType) (part : T -> 'I_0) :
  hg_partite_uniform part [set (set0 : {set T})].
Proof. exact: hg_partite_uniform_rank0. Qed.

(** One edge {0, 1} on 'I_3 with classes 0 -> 0, 1 -> 1, 2 -> 0: vertex 2 is isolated and the
    classes are unbalanced, which the predicate allows. *)
Definition isolated_part (v : 'I_3) : 'I_2 := if v == 1 :> nat then ord_max else ord0.

Example isolated_vertex_allowed :
  hg_partite_uniform isolated_part
    [set [set (@Ordinal 3 0 isT); (@Ordinal 3 1 isT)]].
Proof.
move=> e; rewrite inE => /eqP-> j.
case: j => -[|[|//]] j2.
- have -> : [set v in [set (@Ordinal 3 0 isT); (@Ordinal 3 1 isT)] |
              isolated_part v == Ordinal j2] = [set (@Ordinal 3 0 isT)].
    by apply/setP => -[[|[|[|//]]] ?]; rewrite !inE /isolated_part //=; apply/eqP/val_inj.
  by rewrite cards1.
- have -> : [set v in [set (@Ordinal 3 0 isT); (@Ordinal 3 1 isT)] |
              isolated_part v == Ordinal j2] = [set (@Ordinal 3 1 isT)].
    by apply/setP => -[[|[|[|//]]] ?]; rewrite !inE /isolated_part //=; apply/eqP/val_inj.
  by rewrite cards1.
Qed.

(** Closure: subfamilies, and vertex deletion keeping the whole edges that avoid [X]. *)
Example partite_subfamily (T : finType) (k : nat) (part : T -> 'I_k) (E F : {set {set T}}) :
  F \subset E -> hg_partite_uniform part E -> hg_partite_uniform part F.
Proof. exact: hg_partite_uniformS. Qed.

Example partite_delete (T : finType) (k : nat) (part : T -> 'I_k) (E : {set {set T}})
    (X : {set T}) :
  hg_partite_uniform part E -> hg_partite_uniform part [set e in E | [disjoint e & X]].
Proof. exact: hg_partite_uniform_delete. Qed.

(** ** Consequences *)

(** Every member has exactly [k] vertices, so the family is [k]-uniform in D1's sense (no
    [0 < k] premise). *)
Example partite_uniform_family (T : finType) (k : nat) (part : T -> 'I_k) (E : {set {set T}}) :
  hg_partite_uniform part E -> uniform_family E k.
Proof. exact: hg_partite_uniform_uniform. Qed.

(** With a member edge, [part] is onto and [k <= #|T|]. *)
Example member_onto_rank (T : finType) (k : nat) (part : T -> 'I_k) (E : {set {set T}})
    (e : {set T}) :
  hg_partite_uniform part E -> e \in E -> (forall j, exists v, part v = j) /\ k <= #|T|.
Proof.
move=> pE eE; split; first exact: hg_partite_uniform_onto pE eE.
exact: hg_partite_uniform_rank_le pE eE.
Qed.

(** ** Negative instances *)

(** The full edge of 'I_2 is 2-uniform, but with the constant map class 1 is never met. *)
Example uniform_not_partite :
  uniform_family [set [set: 'I_2]] 2 /\
  ~ hg_partite_uniform (fun _ : 'I_2 => (ord0 : 'I_2)) [set [set: 'I_2]].
Proof.
split.
  by move=> e; rewrite inE => /eqP->; rewrite cardsT card_ord.
move=> /(_ _ (set11 _) ord_max).
have -> : [set v in [set: 'I_2] | (ord0 : 'I_2) == ord_max] = set0.
  by apply/setP => v; rewrite !inE.
by rewrite cards0.
Qed.

(** Without a member, the empty family on the empty carrier is 1-partite, yet the map into
    ['I_1] is not onto and [1 <= #|T|] fails: the member premise above is needed. *)
Example no_member_no_rank_bound :
  hg_partite_uniform (fun v : 'I_0 => (ord0 : 'I_1)) set0 /\ ~ (1 <= #|'I_0|).
Proof. by split; [exact: hg_partite_uniform0 | rewrite card_ord]. Qed.

Print Assumptions isolated_vertex_allowed.
Print Assumptions partite_uniform_family.
Print Assumptions uniform_not_partite.
Print Assumptions no_member_no_rank_bound.

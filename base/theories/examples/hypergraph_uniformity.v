(** Public-only clients of [GTBase.hypergraph_uniformity] (no conjecture or migration import).
    Set families: the empty family at every rank, [{set0}] exactly at rank 0, a singleton
    k-set, a mixed-size family rejected, subfamily closure, a rank fixed only by a member and
    bounded by the vertex count only with a member.  Indexed incidence: an empty index type,
    duplicate labels and the image-family bridge; uniformity says nothing about injectivity of
    the incidence map (the [simple_hg] condition of the U5 row). *)
From mathcomp Require Import all_boot.
From GTBase Require Import hypergraph_uniformity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Example empty_family_every_rank (T : finType) (k : nat) :
  uniform_family (set0 : {set {set T}}) k.
Proof. exact: uniform_family0. Qed.

Example set0_member_rank0 (T : finType) : uniform_family [set (set0 : {set T})] 0.
Proof. exact/uniform_family_set0. Qed.

Example set0_member_not_rank1 (T : finType) : ~ uniform_family [set (set0 : {set T})] 1.
Proof. by move/uniform_family_set0. Qed.

Example singleton_kset (T : finType) (e : {set T}) : uniform_family [set e] #|e|.
Proof. exact: uniform_family1. Qed.

Example mixed_sizes_rejected :
  ~ uniform_family [set [set (@Ordinal 2 0 isT)]; [set: 'I_2]] 1.
Proof.
by move=> /(_ [set: 'I_2]); rewrite !inE eqxx orbT cardsT card_ord => /(_ isT).
Qed.

Example subfamily_closed (T : finType) (E F : {set {set T}}) (k : nat) :
  F \subset E -> uniform_family E k -> uniform_family F k.
Proof. exact: uniform_familyS. Qed.

Example rank_fixed_by_member (T : finType) (E : {set {set T}}) (e : {set T}) (k l : nat) :
  e \in E -> uniform_family E k -> uniform_family E l -> k = l.
Proof. exact: uniform_family_rank. Qed.

(** Without a member the rank is not determined. *)
Example empty_family_two_ranks (T : finType) :
  uniform_family (set0 : {set {set T}}) 0 /\ uniform_family (set0 : {set {set T}}) 1.
Proof. by split; exact: uniform_family0. Qed.

Example rank_bounded_by_member (T : finType) (E : {set {set T}}) (e : {set T}) (k : nat) :
  e \in E -> uniform_family E k -> k <= #|T|.
Proof. exact: uniform_family_rank_le. Qed.

(** Without a member nothing bounds the rank, even over the empty vertex type. *)
Example rank_unbounded_without_member :
  uniform_family (set0 : {set {set 'I_0}}) 5 /\ ~ (5 <= #|'I_0|).
Proof. by split; [exact: uniform_family0 | rewrite card_ord]. Qed.

Example empty_index_type (T : finType) (inc : 'I_0 -> {set T}) (k : nat) :
  uniform_incidence inc k.
Proof. by case. Qed.

(** Two labels with the same incidence set: uniform, not injective. *)
Definition twin_labels (i : 'I_2) : {set 'I_2} := [set: 'I_2].

Example duplicate_labels_uniform_not_injective :
  uniform_incidence twin_labels 2 /\ ~ injective twin_labels.
Proof.
split; first by move=> i; rewrite /twin_labels cardsT card_ord.
by move=> /(_ (@Ordinal 2 0 isT) (@Ordinal 2 1 isT) erefl) /(congr1 val).
Qed.

Example duplicate_labels_image :
  uniform_family [set twin_labels i | i in [set: 'I_2]] 2.
Proof. by apply/uniform_incidence_imageE => i; rewrite /twin_labels cardsT card_ord. Qed.

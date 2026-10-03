(** Public-only client of [Hypergraph.foundations.hypergraph_copies] ([hg_mono_copy E col]: one
    colour and one injection of the whole pattern carrier send every member of [E] to a host set of
    that colour).  No conjecture module is imported.  Covered: the empty family, an empty pattern
    carrier, an empty host, a family containing the empty edge, a larger pattern than host without
    edges, a constant colouring with an explicit injection, subfamilies, a real non-monochromatic
    colouring, palette relabelling, the bool/['I_2] bridge on a supplied colouring, the colour-class
    bridge with [hg_containsb], and the impossible colouring into the empty palette ['I_0]. *)
From GTBase Require Import base.
From Hypergraph.foundations Require Import hypergraph hypergraph_copies.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Empty family, empty pattern, empty host *)

(** With no members, the supplied colouring gives the colour: a copy exists iff an injection does. *)
Example empty_family (T U : finType) (C : Type) (col : {set U} -> C) :
  hg_mono_copy (set0 : {set {set T}}) col <-> exists f : T -> U, injective f.
Proof. exact: hg_mono_copy0. Qed.

(** An empty pattern carrier embeds in every host. *)
Example empty_pattern (U : finType) (C : Type) (col : {set U} -> C) :
  hg_mono_copy (set0 : {set {set 'I_0}}) col.
Proof.
apply/hg_mono_copy0; have f : 'I_0 -> U by case=> m; rewrite ltn0.
by exists f => -[m p]; exfalso; move: p; rewrite ltn0.
Qed.

(** A nonempty pattern carrier has no copy in the empty host, even without members. *)
Example empty_host (C : Type) (col : {set 'I_0} -> C) : ~ hg_mono_copy (set0 : {set {set 'I_1}}) col.
Proof. by move=> /hg_mono_copy_card; rewrite !card_ord. Qed.

(** A family containing the empty edge: its image is the host's empty set, coloured [col set0]. *)
Example empty_edge_member (U : finType) (C : Type) (col : {set U} -> C) (f : 'I_1 -> U) :
  injective f -> hg_mono_copy [set (set0 : {set 'I_1})] col.
Proof.
by move=> fi; exists (col set0), f; split=> // e; rewrite inE => /eqP->; rewrite imset0.
Qed.

(** A larger carrier never embeds in a smaller host, even with no members. *)
Example larger_pattern (C : Type) (col : {set 'I_2} -> C) : ~ hg_mono_copy (set0 : {set {set 'I_3}}) col.
Proof. by move=> /hg_mono_copy_card; rewrite !card_ord. Qed.

(** ** Positive cases and closure *)

(** A constant colouring with the explicit injection [widen_ord]. *)
Example constant_colour (E : {set {set 'I_2}}) :
  hg_mono_copy E (fun _ : {set 'I_3} => true).
Proof.
apply: (@hg_mono_copy_const _ _ _ E true (widen_ord (isT : 2 <= 3))).
by move=> x y /(congr1 val) /= xy; apply: val_inj.
Qed.

Example subfamily (T U : finType) (C : Type) (E F : {set {set T}}) (col : {set U} -> C) :
  F \subset E -> hg_mono_copy E col -> hg_mono_copy F col.
Proof. exact: hg_mono_copyS. Qed.

(** ** A real negative case *)

(** Two singleton members on two pattern vertices, host ['I_2], colour "is the set {0}": every
    injection sends the members to {0} and {1}, which get different colours. *)
Example not_monochromatic :
  ~ hg_mono_copy [set [set (ord0 : 'I_2)]; [set ord_max]] (fun s : {set 'I_2} => s == [set ord0]).
Proof.
move=> [c [f [fi H]]].
have h0 := H [set ord0] (set21 _ _); have h1 := H [set ord_max] (set22 _ _).
move: h0 h1; rewrite /= !imset_set1 !(inj_eq set1_inj) => <-.
have : f ord0 != f ord_max by rewrite (inj_eq fi).
by case: (f ord0) => -[|[|//]] ?; case: (f ord_max) => -[|[|//]] ?.
Qed.

(** ** Palettes *)

Example relabel (T U : finType) (C D : Type) (g : C -> D) (E : {set {set T}}) (col : {set U} -> C) :
  hg_mono_copy E col -> hg_mono_copy E (fun s => g (col s)).
Proof. exact: hg_mono_copy_map. Qed.

(** The bool / ['I_2] bridge keeps the supplied colouring, in both directions. *)
Definition bool_to_I2 (b : bool) : 'I_2 := @Ordinal 2 b (leq_b1 b).
Definition I2_to_bool (i : 'I_2) : bool := (i : nat) == 1.

Lemma bool_to_I2K : cancel bool_to_I2 I2_to_bool.
Proof. by case. Qed.

Lemma I2_to_boolK : cancel I2_to_bool bool_to_I2.
Proof. by move=> i; apply/val_inj; case: i => -[|[|m]]. Qed.

Example bool_I2_bridge (T U : finType) (E : {set {set T}}) (col : {set U} -> bool) :
  hg_mono_copy E col <-> hg_mono_copy E (fun s => bool_to_I2 (col s)).
Proof. by split; [exact: hg_mono_copy_map | exact: hg_mono_copy_mapK bool_to_I2K]. Qed.

Example I2_bool_bridge (T U : finType) (E : {set {set T}}) (col : {set U} -> 'I_2) :
  hg_mono_copy E col <-> hg_mono_copy E (fun s => I2_to_bool (col s)).
Proof. by split; [exact: hg_mono_copy_map | exact: hg_mono_copy_mapK I2_to_boolK]. Qed.

(** The colour-class bridge with the existing containment. *)
Example colour_class (T U : finType) (E : {set {set T}}) (col : {set U} -> bool) :
  hg_mono_copy E col <-> exists c, hg_containsb E [set e | col e == c].
Proof. exact: hg_mono_copyP. Qed.

(** The empty palette: a colouring of all host subsets into ['I_0] is impossible, since [set0]
    exists.  So any statement quantified over such colourings is vacuously true. *)
Example no_empty_palette_colouring (U : finType) (col : {set U} -> 'I_0) : False.
Proof. by case: (col set0). Qed.

Print Assumptions not_monochromatic.
Print Assumptions bool_I2_bridge.
Print Assumptions colour_class.

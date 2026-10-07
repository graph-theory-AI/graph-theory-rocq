(** Public-only client of [Hypergraph.foundations.hypergraph_forcing] ([hg_forces_mono E U C]: every
    colouring of the subsets of the host [U] by the palette [C] has a monochromatic copy of [E]).  No
    conjecture module is imported.  Covered: elimination, subfamilies, the empty palette (vacuous
    forcing, even into the empty host), the singleton palette (forcing iff an injection), the carrier
    obstruction for an inhabited palette, empty pattern cases, and the bool / ['I_2] transport through
    actual inverse palette maps. *)
From GTBase Require Import base.
From Hypergraph.foundations Require Import hypergraph hypergraph_copies hypergraph_forcing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Elimination and closure *)

Example forcing_gives_copy (T U : finType) (C : Type) (E : {set {set T}}) (col : {set U} -> C) :
  hg_forces_mono E U C -> hg_mono_copy E col.
Proof. exact: hg_forces_monoE. Qed.

Example forcing_subfamily (T U : finType) (C : Type) (E F : {set {set T}}) :
  F \subset E -> hg_forces_mono E U C -> hg_forces_mono F U C.
Proof. exact: hg_forces_monoS. Qed.

(** ** Palettes *)

(** The empty palette ['I_0]: no colouring of the host subsets exists, so every pattern is forced,
    even into the empty host. *)
Example empty_palette_forces (T U : finType) (E : {set {set T}}) : hg_forces_mono E U 'I_0.
Proof. by apply: hg_forces_mono_empty_palette => -[]. Qed.

Example empty_palette_empty_host : hg_forces_mono [set [set: 'I_3]] 'I_0 'I_0.
Proof. by apply: hg_forces_mono_empty_palette => -[]. Qed.

(** A singleton palette forces exactly when the whole pattern carrier injects into the host. *)
Example singleton_palette (T U : finType) (E : {set {set T}}) :
  hg_forces_mono E U 'I_1 <-> exists f : T -> U, injective f.
Proof. by apply: hg_forces_mono_singleton ord0 _ => c; exact: ord1. Qed.

(** With an inhabited palette, a pattern with more vertices than the host is never forced, even
    without members. *)
Example inhabited_palette_obstruction : ~ hg_forces_mono (set0 : {set {set 'I_3}}) 'I_2 bool.
Proof. by move=> /(hg_forces_mono_card true); rewrite !card_ord. Qed.

(** ** Empty patterns *)

(** The empty carrier is forced in every host for every palette: the colour of [set0] works. *)
Example empty_pattern_forced (U : finType) (C : Type) : hg_forces_mono (set0 : {set {set 'I_0}}) U C.
Proof.
move=> col; apply/hg_mono_copy0; have f : 'I_0 -> U by case=> m; rewrite ltn0.
by exists f => -[m p]; exfalso; move: p; rewrite ltn0.
Qed.

(** ** bool / ['I_2] transport through actual inverse maps *)

Definition bool_to_I2 (b : bool) : 'I_2 := @Ordinal 2 b (leq_b1 b).
Definition I2_to_bool (i : 'I_2) : bool := (i : nat) == 1.

Lemma bool_to_I2K : cancel bool_to_I2 I2_to_bool.
Proof. by case. Qed.

Lemma I2_to_boolK : cancel I2_to_bool bool_to_I2.
Proof. by move=> i; apply/val_inj; case: i => -[|[|m]]. Qed.

Example bool_I2_forcing (T U : finType) (E : {set {set T}}) :
  hg_forces_mono E U bool <-> hg_forces_mono E U 'I_2.
Proof.
split; first exact: hg_forces_mono_transport I2_to_boolK.
exact: hg_forces_mono_transport bool_to_I2K.
Qed.

Print Assumptions empty_palette_empty_host.
Print Assumptions singleton_palette.
Print Assumptions bool_I2_forcing.

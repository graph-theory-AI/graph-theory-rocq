(** Public-only client of [Hypergraph.foundations.hypergraph_ramsey] ([hg_ramsey_number E C R]: [R] is
    the least host size forcing a monochromatic copy of [E] under the palette [C], attained and minimal).
    No conjecture module is imported.  Covered: attainment, minimality and uniqueness; the empty palette
    (minimum 0); the empty carrier and the empty family with a colour (minimum [#|T|], the whole carrier
    must inject); the singleton empty edge; a Boolean example; and the separation of forcing alone, or
    minimality alone, from the attained minimum. *)
From GTBase Require Import base.
From Hypergraph.foundations Require Import hypergraph_copies hypergraph_forcing hypergraph_ramsey.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Attainment, minimality, uniqueness *)

Example ramsey_attained (T : finType) (E : {set {set T}}) (C : Type) (R : nat) :
  hg_ramsey_number E C R -> hg_forces_mono E 'I_R C.
Proof. exact: hg_ramsey_number_forces. Qed.

Example ramsey_minimal (T : finType) (E : {set {set T}}) (C : Type) (R N : nat) :
  hg_ramsey_number E C R -> hg_forces_mono E 'I_N C -> R <= N.
Proof. exact: hg_ramsey_number_min. Qed.

Example ramsey_unique (T : finType) (E : {set {set T}}) (C : Type) (R1 R2 : nat) :
  hg_ramsey_number E C R1 -> hg_ramsey_number E C R2 -> R1 = R2.
Proof. exact: hg_ramsey_number_uniq. Qed.

(** ** The empty palette: minimum 0 for every pattern *)

Example empty_palette_ramsey (T : finType) (E : {set {set T}}) (R : nat) :
  hg_ramsey_number E 'I_0 R <-> R = 0.
Proof. by apply: hg_ramsey_number_empty_palette => -[m]; rewrite ltn0. Qed.

(** ** The empty family with a colour: the whole carrier must inject *)

Example empty_carrier_ramsey (C : Type) (c0 : C) (R : nat) :
  hg_ramsey_number (set0 : {set {set 'I_0}}) C R <-> R = 0.
Proof. by have := @hg_ramsey_number_set0 'I_0 C c0 R; rewrite card_ord. Qed.

Example bool_empty_pattern_ramsey (R : nat) : hg_ramsey_number (set0 : {set {set 'I_2}}) bool R <-> R = 2.
Proof. by have := @hg_ramsey_number_set0 'I_2 bool true R; rewrite card_ord. Qed.

(** ** The singleton empty edge behaves like the empty family once a colour exists *)

Example empty_edge_forcing (T : finType) (C : Type) (c0 : C) (N : nat) :
  hg_forces_mono [set (set0 : {set T})] 'I_N C <-> #|T| <= N.
Proof.
split=> [/(hg_forces_mono_card c0)|TN col]; first by rewrite card_ord.
exists (col set0), (fun x => widen_ord TN (enum_rank x)); split.
  by move=> x y /(congr1 val) /= /val_inj /enum_rank_inj.
by move=> e; rewrite inE => /eqP->; rewrite imset0.
Qed.

Example empty_edge_ramsey (T : finType) (C : Type) (c0 : C) (R : nat) :
  hg_ramsey_number [set (set0 : {set T})] C R <-> R = #|T|.
Proof.
split=> [[F m]|->].
  have TR : #|T| <= R := (@empty_edge_forcing T C c0 R).1 F.
  have RT : R <= #|T| := m _ ((@empty_edge_forcing T C c0 #|T|).2 (leqnn _)).
  by apply/eqP; rewrite eqn_leq RT TR.
split; first exact: (@empty_edge_forcing T C c0 #|T|).2 (leqnn _).
by move=> N FN; exact: (@empty_edge_forcing T C c0 N).1 FN.
Qed.

(** ** Forcing alone, or minimality alone, is not the attained minimum *)

Example forcing_not_minimum :
  hg_forces_mono (set0 : {set {set 'I_1}}) 'I_5 bool /\ ~ hg_ramsey_number (set0 : {set {set 'I_1}}) bool 5.
Proof.
split; first by apply/(hg_forces_mono_set0 'I_1 true); rewrite card_ord.
by move=> /(hg_ramsey_number_set0 'I_1 true); rewrite card_ord.
Qed.

Example minimality_not_minimum :
  (forall N, hg_forces_mono (set0 : {set {set 'I_1}}) 'I_N bool -> 0 <= N) /\
  ~ hg_ramsey_number (set0 : {set {set 'I_1}}) bool 0.
Proof.
split=> // /(hg_ramsey_number_set0 'I_1 true).
by rewrite card_ord.
Qed.

Print Assumptions empty_palette_ramsey.
Print Assumptions bool_empty_pattern_ramsey.
Print Assumptions empty_edge_ramsey.
Print Assumptions forcing_not_minimum.

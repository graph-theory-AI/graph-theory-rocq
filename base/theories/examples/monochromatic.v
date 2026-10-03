(** Public-only client of the monochromatic subset API. No graph, conjecture
    or migration imports; colours may live in an infinite equality type. *)
From GTBase Require Import monochromatic.
From mathcomp Require Import all_boot.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Example empty_subset (T : finType) (C : eqType) (col : T -> C) :
  monochromatic_on col set0.
Proof. exact: monochromatic_on_set0. Qed.

Example singleton_with_natural_palette :
  monochromatic_on (fun x : bool => if x then 0 else 100) [set true].
Proof. exact: monochromatic_on_set1. Qed.

Example constant_colours (T : finType) (C : eqType) (c : C) (S : {set T}) :
  monochromatic_on (fun _ : T => c) S.
Proof. exact: monochromatic_on_const. Qed.

Example two_distinct_colours_fail :
  ~~ monochromatic_on (fun x : bool => x) [set true; false].
Proof. by rewrite monochromatic_on_pair. Qed.

Example empty_domain_empty_palette :
  monochromatic_on (fun x : 'I_0 => x) [set: 'I_0].
Proof.
apply/monochromatic_onP=> x y xS yS.
by move: (ltn_ord x); rewrite ltn0.
Qed.

Example restriction (T : finType) (C : eqType) (col : T -> C) (A B : {set T}) :
  A \subset B -> monochromatic_on col B -> monochromatic_on col A.
Proof. exact: monochromatic_on_sub. Qed.

Example outside_colours_do_not_matter
    (T : finType) (C : eqType) (c d : T -> C) (S : {set T}) :
  {in S, c =1 d} -> monochromatic_on c S = monochromatic_on d S.
Proof. exact: monochromatic_on_ext. Qed.

Example injective_palette_change
    (T : finType) (C D : eqType) (c : T -> C) (f : C -> D) (S : {set T}) :
  injective f -> monochromatic_on (f \o c) S = monochromatic_on c S.
Proof. exact: monochromatic_on_relabel. Qed.

Example explicit_pairwise_contract
    (T : finType) (C : eqType) (c : T -> C) (S : {set T}) :
  monochromatic_on c S -> forall x y, x \in S -> y \in S -> c x = c y.
Proof. exact/monochromatic_onP. Qed.

Example upstream_constant_is_the_definition
    (T : finType) (C : eqType) (c : T -> C) (S : {set T}) :
  monochromatic_on c S = constant [seq c x | x <- enum S].
Proof. by []. Qed.

Example differing_colours_witness_failure
    (T : finType) (C : eqType) (c : T -> C) (S : {set T}) :
  ~~ monochromatic_on c S -> exists x y : T, [/\ x \in S, y \in S & c x != c y].
Proof. exact/non_monochromatic_onP. Qed.

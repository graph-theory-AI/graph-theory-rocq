(** * Digraph.ckpath_shapes -- the finite Cheng--Keevash shape tables

    These lemmas isolate the Presburger-arithmetic end of the CK kernel for
    minimum out-degrees four, five, and six.  The variable [r] is the
    internal out-degree of the average-bound witness in the CK set [S]. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Stdlib Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma ckpath_shape4 (L s r a : nat) :
  Peano.le 7 L -> Peano.lt L 8 ->
  Peano.le 1 a -> Peano.le (Nat.add a 4) L -> Peano.le s 4 ->
  Peano.le 4 (Nat.add s (Nat.sub a 2)) ->
  Peano.le (Nat.sub 8 L) r ->
  Peano.le (Nat.add r r) (Nat.sub s 1) ->
  Peano.le (Nat.sub (Nat.add s 4) r) (Nat.sub (S L) a) ->
  [/\ L = 7, s = 4, r = 1 & a = 1].
Proof.
intros. split; lia.
Qed.

Lemma ckpath_shape5 (L s r a : nat) :
  Peano.le 8 L -> Peano.lt L 10 ->
  Peano.le 1 a -> Peano.le (Nat.add a 5) L -> Peano.le s 5 ->
  Peano.le 5 (Nat.add s (Nat.sub a 2)) ->
  Peano.le (Nat.sub 10 L) r ->
  Peano.le (Nat.add r r) (Nat.sub s 1) ->
  Peano.le (Nat.sub (Nat.add s 5) r) (Nat.sub (S L) a) ->
  [\/
    [/\ L = 8, s = 5, r = 2 & a = 1],
    [/\ L = 9, s = 5, r = 1 & a = 1],
    [/\ L = 9, s = 5, r = 2 & a = 1]
  | [/\ L = 9, s = 5, r = 2 & a = 2]].
Proof.
intros.
have hcases :
  (L = 8 /\ s = 5 /\ r = 2 /\ a = 1) \/
  (L = 9 /\ s = 5 /\ r = 1 /\ a = 1) \/
  (L = 9 /\ s = 5 /\ r = 2 /\ a = 1) \/
  (L = 9 /\ s = 5 /\ r = 2 /\ a = 2) by lia.
case: hcases => [[-> [-> [-> ->]]] |
  [[-> [-> [-> ->]]] |
   [[-> [-> [-> ->]]] | [-> [-> [-> ->]]]]]].
- apply: Or41; by split.
- apply: Or42; by split.
- apply: Or43; by split.
- apply: Or44; by split.
Qed.

Lemma ckpath_shape6 (L s r a : nat) :
  Peano.le 10 L -> Peano.lt L 12 ->
  Peano.le 1 a -> Peano.le (Nat.add a 6) L -> Peano.le s 6 ->
  Peano.le 6 (Nat.add s (Nat.sub a 2)) ->
  Peano.le (Nat.sub 12 L) r ->
  Peano.le (Nat.add r r) (Nat.sub s 1) ->
  Peano.le (Nat.sub (Nat.add s 6) r) (Nat.sub (S L) a) ->
  [\/
    [/\ L = 10, s = 6, r = 2 & a = 1],
    [/\ L = 11, s = 5, r = 2 & a = 3],
    [/\ L = 11, s = 6, r = 1 & a = 1]
  | ([/\ L = 11, s = 6, r = 2 & a = 1] \/
     [/\ L = 11, s = 6, r = 2 & a = 2])].
Proof.
intros.
have hcases :
  (L = 10 /\ s = 6 /\ r = 2 /\ a = 1) \/
  (L = 11 /\ s = 5 /\ r = 2 /\ a = 3) \/
  (L = 11 /\ s = 6 /\ r = 1 /\ a = 1) \/
  (L = 11 /\ s = 6 /\ r = 2 /\ a = 1) \/
  (L = 11 /\ s = 6 /\ r = 2 /\ a = 2) by lia.
case: hcases => [[-> [-> [-> ->]]] |
  [[-> [-> [-> ->]]] |
   [[-> [-> [-> ->]]] |
    [[-> [-> [-> ->]]] | [-> [-> [-> ->]]]]]]].
- apply: Or41; by split.
- apply: Or42; by split.
- apply: Or43; by split.
- apply: Or44; left; by split.
- apply: Or44; right; by split.
Qed.

(** The eleven exact kernel shapes at out-degree seven.  The lower bound
    [12 <= L] is supplied by the already established out-degree-six case. *)
Definition ckpath_shape7_cases (L s r a : nat) : Prop :=
  (L = 12 /\ s = 7 /\ r = 2 /\ a = 1) \/
  (L = 12 /\ s = 7 /\ r = 3 /\ a = 1) \/
  (L = 12 /\ s = 7 /\ r = 3 /\ a = 2) \/
  (L = 13 /\ s = 5 /\ r = 2 /\ a = 4) \/
  (L = 13 /\ s = 6 /\ r = 2 /\ a = 3) \/
  (L = 13 /\ s = 7 /\ r = 1 /\ a = 1) \/
  (L = 13 /\ s = 7 /\ r = 2 /\ a = 1) \/
  (L = 13 /\ s = 7 /\ r = 2 /\ a = 2) \/
  (L = 13 /\ s = 7 /\ r = 3 /\ a = 1) \/
  (L = 13 /\ s = 7 /\ r = 3 /\ a = 2) \/
  (L = 13 /\ s = 7 /\ r = 3 /\ a = 3).

Lemma ckpath_shape7 (L s r a : nat) :
  Peano.le 12 L -> Peano.lt L 14 ->
  Peano.le 1 a -> Peano.le (Nat.add a 7) L -> Peano.le s 7 ->
  Peano.le 7 (Nat.add s (Nat.sub a 2)) ->
  Peano.le (Nat.sub 14 L) r ->
  Peano.le (Nat.add r r) (Nat.sub s 1) ->
  Peano.le (Nat.sub (Nat.add s 7) r) (Nat.sub (S L) a) ->
  ckpath_shape7_cases L s r a.
Proof.
intros.
unfold ckpath_shape7_cases.
have hL : L = 12 \/ L = 13 by lia.
destruct hL as [hL | hL]; subst L.
- have hs : s = 7 by lia.
  have hc :
    (r = 2 /\ a = 1) \/ (r = 3 /\ a = 1) \/ (r = 3 /\ a = 2) by lia.
  destruct hc as [[hr ha] | [[hr ha] | [hr ha]]];
    subst s; subst r; subst a; tauto.
- have ha : a = 1 \/ a = 2 \/ a = 3 \/ a = 4 by lia.
  destruct ha as [ha | [ha | [ha | ha]]]; subst a.
  - have hs : s = 7 by lia.
    have hr : r = 1 \/ r = 2 \/ r = 3 by lia.
    destruct hr as [hr | [hr | hr]]; subst s; subst r; tauto.
  - have hs : s = 7 by lia.
    have hr : r = 2 \/ r = 3 by lia.
    destruct hr as [hr | hr]; subst s; subst r; tauto.
  - have hc : (s = 6 /\ r = 2) \/ (s = 7 /\ r = 3) by lia.
    destruct hc as [[hs hr] | [hs hr]]; subst s; subst r; tauto.
  - have hs : s = 5 by lia.
    have hr : r = 2 by lia.
    subst s; subst r; tauto.
Qed.

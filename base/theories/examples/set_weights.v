(** Downstream use of the upstream finite-set weight through the GTBase views, without corpus imports: the empty set
    and a singleton, zero weights (no positivity: a nonempty set may weigh 0), unit weights (the cardinality), the
    whole carrier (the total weight), the complement split, monotonicity, the bridge to the event weight of the
    finite-probability vocabulary with the zero test, and a concrete weighting of ['I_3]. *)
From GTBase Require Import base set_weights.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The empty set weighs 0 and a singleton its own weight, on every carrier and for every weighting. *)
Example weight_empty_singleton (T : finType) (w : T -> nat) (x : T) :
  weight_set w set0 = 0 /\ weight_set w [set x] = w x.
Proof. by rewrite weight_set0 weight_set1. Qed.

(** Zero weights are allowed: the nonempty whole carrier of ['I_2] weighs 0. *)
Example weight_zero_nonempty :
  weight_set (fun _ : 'I_2 => 0) [set: 'I_2] = 0 /\ [set: 'I_2] != set0.
Proof. by rewrite weight_set_const; split=> //; apply/set0Pn; exists ord0; rewrite inE. Qed.

(** Unit weights count the members. *)
Example weight_unit (T : finType) (S : {set T}) : weight_set (fun=> 1) S = #|S|.
Proof. by rewrite weight_set_const mul1n. Qed.

(** The whole carrier weighs the total, a set and its complement share it, and inclusion is monotone. *)
Example weight_total_split (T : finType) (w : T -> nat) (A B : {set T}) :
  [/\ weight_set w [set: T] = fg_total_weight w,
      weight_set w A + weight_set w (~: A) = fg_total_weight w &
      A \subset B -> weight_set w A <= weight_set w B].
Proof. by split; [exact: weight_setT | exact: weight_setC | exact: weight_set_subset]. Qed.

(** The finite-set coercion bridge to the event weight, and the zero test. *)
Example weight_event_zero (T : finType) (w : T -> nat) (S : {set T}) :
  weight_set w S = fg_event_weight w [in S] /\ (weight_set w S == 0) = [forall (x | x \in S), w x == 0].
Proof. by split; [exact: weight_set_event | exact: weight_set_eq0]. Qed.

(** A concrete weighting of ['I_3] (weights 1, 0, 2): the disjoint sets [{0}] and [{2}] add up to 3, the total weight
    is 3, and the nonempty set [{1}] weighs 0. *)
Definition w3 (i : 'I_3) : nat := nth 0 [:: 1; 0; 2] i.
Local Notation v i := (@Ordinal 3 i isT).

Example weight_concrete :
  [/\ weight_set w3 [set v 0; v 2] = weight_set w3 [set v 0] + weight_set w3 [set v 2],
      weight_set w3 [set v 0; v 2] = 3, fg_total_weight w3 = 3 & weight_set w3 [set v 1] = 0].
Proof.
have U : weight_set w3 [set v 0; v 2] = weight_set w3 [set v 0] + weight_set w3 [set v 2].
  by rewrite weight_setU // disjoints1 inE.
by split=> //; [rewrite U !weight_set1 | rewrite /fg_total_weight !big_ord_recl big_ord0 | rewrite weight_set1].
Qed.

Print Assumptions weight_empty_singleton.
Print Assumptions weight_zero_nonempty.
Print Assumptions weight_unit.
Print Assumptions weight_total_split.
Print Assumptions weight_event_zero.
Print Assumptions weight_concrete.

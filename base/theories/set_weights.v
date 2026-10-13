(** * GTBase.set_weights -- natural weights of finite sets

    The canonical weight of a finite set is upstream [weight_set w S := \sum_(v in S) w v]
    ([GraphTheory.core.dom], re-exported by [GTBase.base]), for any finite carrier [T], any natural
    weight function [w : T -> nat] and any supplied set [S : {set T}].  No weight primitive is added
    here; the lemmas below give it, without any positivity hypothesis, its basic finite-sum API:
    - [weight_set_event] / [weight_setT]: the finite-set coercion bridge to the event and total
      weights [fg_event_weight w [in S]] and [fg_total_weight w] of [GTBase.finite_graph];
    - [weight_set0] / [weight_set1]: the empty set weighs 0 and a singleton its vertex weight;
    - [weight_set_const]: a constant weight [c] gives [c * #|S|], so zero weights give 0 and unit
      weights the cardinality;
    - [weight_setU] / [weight_setC]: additivity on disjoint sets, and a set with its complement
      gives the total;
    - [weight_set_subset] / [weight_set_le_total]: monotonicity under inclusion;
    - [weight_set_eq0]: the weight is 0 exactly when every member weighs 0;
    - [eq_weight_set]: weights agreeing on [S] give the same weight.
    Zero weights and empty sets are allowed throughout (the empty carrier included).  Upstream's own
    [wset0], [minweight_minset] and [arg_minset] assume positive weights and are not needed here.  The
    finite-probability ratio predicates of [GTBase.finite_graph] keep their own positive-total-weight
    guards; nothing here adds or removes one.  Registry: meta/library_primitives/set-weight.json (A30). *)
From mathcomp Require Import all_boot.
From GraphTheory Require Import dom.
From GTBase Require Import finite_graph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SetWeights.
Variables (T : finType) (w : T -> nat).
Implicit Types (A B S : {set T}) (x : T).

(** The finite-set coercion bridge: a set weight is the event weight of its membership predicate. *)
Lemma weight_set_event S : weight_set w S = fg_event_weight w [in S].
Proof. by []. Qed.

(** The whole carrier weighs the total weight. *)
Lemma weight_setT : weight_set w [set: T] = fg_total_weight w.
Proof. by apply: eq_bigl => x; rewrite inE. Qed.

Lemma weight_set0 : weight_set w set0 = 0.
Proof. exact: big_set0. Qed.

Lemma weight_set1 x : weight_set w [set x] = w x.
Proof. exact: big_set1. Qed.

Lemma weight_setU A B :
  [disjoint A & B] -> weight_set w (A :|: B) = weight_set w A + weight_set w B.
Proof.
by move=> dis; rewrite /weight_set -bigU //; apply: eq_bigl => x; rewrite !inE.
Qed.

Lemma weight_setC A : weight_set w A + weight_set w (~: A) = fg_total_weight w.
Proof.
have dis : [disjoint A & ~: A] by rewrite disjoints_subset setCK.
by rewrite -weight_setU // setUCr weight_setT.
Qed.

Lemma weight_set_subset A B : A \subset B -> weight_set w A <= weight_set w B.
Proof. by move=> sAB; rewrite /weight_set [X in _ <= X](big_setID A) (setIidPr sAB) leq_addr. Qed.

Lemma weight_set_le_total A : weight_set w A <= fg_total_weight w.
Proof. by rewrite -weight_setT; apply: weight_set_subset; apply: subsetT. Qed.

Lemma weight_set_eq0 A : (weight_set w A == 0) = [forall (x | x \in A), w x == 0].
Proof. exact: sum_nat_eq0. Qed.

End SetWeights.

(** A constant weight [c] gives [c] times the cardinality: zero weights give 0, unit weights [#|S|]. *)
Lemma weight_set_const (T : finType) (c : nat) (S : {set T}) : weight_set (fun=> c) S = c * #|S|.
Proof. by rewrite /weight_set sum_nat_const mulnC. Qed.

Lemma eq_weight_set (T : finType) (w1 w2 : T -> nat) (S : {set T}) :
  {in S, w1 =1 w2} -> weight_set w1 S = weight_set w2 S.
Proof. by move=> eqw; apply: eq_bigr => x /eqw. Qed.

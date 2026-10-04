(** * GTBase.examples.walk_usage — public-only client of GTBase.walk_usage (B28)

    Compiles against public modules alone (no conjecture module).  Finite Boolean view: the empty sequence and a
    one-entry sequence use nothing, symmetry, a repeated adjacent value uses its loop pair, and the pair closing a
    cyclic reading is not used.  Alternating view, over an arbitrary [Type]: the empty tail uses nothing, the first
    step is forward at polarity [true] and backward at polarity [false], the second step is read with the flipped
    polarity, and the wrong orientation of a single forward step is not usage.  The two views differ on that step. *)

From mathcomp Require Import all_boot.
From GTBase Require Import base walks_paths walk_usage.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Finite view: empty and one-entry sequences. *)
Lemma example_finite_short (u v x : nat) :
  seq_consecutiveb [::] u v = false /\ seq_consecutiveb [:: x] u v = false.
Proof. by split; [exact: seq_consecutiveb_nil | exact: seq_consecutiveb_seq1]. Qed.

(** One step [0, 1]: both orders are used. *)
Lemma example_finite_symmetric : seq_consecutiveb [:: 0; 1] 0 1 /\ seq_consecutiveb [:: 0; 1] 1 0.
Proof. by []. Qed.

(** A repeated adjacent value uses its loop pair, with no edge premise. *)
Lemma example_finite_repeat : seq_consecutiveb [:: 2; 2] 2 2.
Proof. exact: seq_consecutiveb_repeat. Qed.

(** The pair closing the cyclic reading of [0, 1, 2] is not used. *)
Lemma example_finite_no_closing_pair : ~~ seq_consecutiveb [:: 0; 1; 2] 2 0.
Proof. by []. Qed.

(** Alternating view over any [Type]: the first step in both polarities, the empty tail. *)
Lemma example_alt_head (T : Type) (x y : T) :
  alt_uses true x [:: y] x y /\ alt_uses false x [:: y] y x /\ ~ alt_uses true x [::] x y.
Proof. by split; [exact: alt_uses_head_true | split; [exact: alt_uses_head_false | exact: alt_uses_nil]]. Qed.

(** The second step is read with the flipped polarity: backward after a forward first step. *)
Lemma example_alt_parity : alt_uses true 0 [:: 1; 2] 2 1 /\ ~ alt_uses true 0 [:: 1; 2] 1 2.
Proof.
split; first by apply: alt_uses_step; exact: alt_uses_head_false.
by move=> [[[_ [e _]] | [e _]] | [[[e _] | [_ [e _]]] | []]].
Qed.

(** The wrong orientation of a single forward step is not usage, although the finite view sees the pair. *)
Lemma example_wrong_orientation : ~ alt_uses true 0 [:: 1] 1 0 /\ seq_consecutiveb [:: 0; 1] 1 0.
Proof. by split=> //; case/alt_uses_true1. Qed.

Print Assumptions example_finite_short.
Print Assumptions example_finite_no_closing_pair.
Print Assumptions example_alt_head.
Print Assumptions example_alt_parity.
Print Assumptions example_wrong_orientation.

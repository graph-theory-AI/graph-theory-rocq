(** * GTBase.examples.natural_data_decoder — public-only client of GTBase.complexity's [data_nth_nat]

    Compiles against GTBase.base (which re-exports GTBase.complexity) alone, with no conjecture or migration module.
    A proper output list [enc_list [seq enc_nat n | n <- [:: 3; 1; 4]]] decodes position by position to [3], [1] and
    [4], and to [0] past its end; a scalar [Dnat 5] reads [5] at position [0] and [0] after; a non-natural entry reads
    [0] while the entries after it keep their positions; a malformed tail [Dnat 7] (in place of a list) is read as a
    scalar at the next position, and nothing after it; [Dnil] and [Dpair] read [0] everywhere.  The colouring adapters
    of the conjectures (an entry read modulo [k], or modulo [3]) are a separate layer over the decoder; read modulo [0],
    an entry keeps its value. *)

From mathcomp Require Import all_boot.
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition out314 : data := enc_list [seq enc_nat n | n <- [:: 3; 1; 4]].

(** A proper list of naturals: [nth 0] of the list, [0] past its end. *)
Example example_list_positions :
  [/\ data_nth_nat out314 0 = 3, data_nth_nat out314 1 = 1, data_nth_nat out314 2 = 4
    & data_nth_nat out314 3 = 0].
Proof. by []. Qed.

Lemma example_list_nth (i : nat) : data_nth_nat out314 i = nth 0 [:: 3; 1; 4] i.
Proof. exact: data_nth_nat_enc_list. Qed.

Lemma example_list_past_end (i : nat) : 3 <= i -> data_nth_nat out314 i = 0.
Proof. exact: (@data_nth_nat_enc_list_default [:: 3; 1; 4]). Qed.

(** A scalar answer is a one-entry list. *)
Example example_scalar : data_nth_nat (Dnat 5) 0 = 5 /\ data_nth_nat (Dnat 5) 1 = 0.
Proof. by []. Qed.

(** A non-natural entry reads 0; the entries after it keep their positions. *)
Example example_non_natural_entry :
  data_nth_nat (Dcons (Dpair (Dnat 1) Dnil) (Dcons (Dnat 8) Dnil)) 0 = 0 /\
  data_nth_nat (Dcons (Dpair (Dnat 1) Dnil) (Dcons (Dnat 8) Dnil)) 1 = 8.
Proof. by []. Qed.

(** A malformed tail: the scalar [Dnat 7] in place of the rest of the list is read at the next position. *)
Example example_malformed_tail :
  [/\ data_nth_nat (Dcons (Dnat 2) (Dnat 7)) 0 = 2, data_nth_nat (Dcons (Dnat 2) (Dnat 7)) 1 = 7
    & data_nth_nat (Dcons (Dnat 2) (Dnat 7)) 2 = 0].
Proof. by []. Qed.

(** [Dnil] and [Dpair] read 0 at every position, even when a pair holds naturals. *)
Lemma example_nil_pair (i : nat) : data_nth_nat Dnil i = 0 /\ data_nth_nat (Dpair (Dnat 4) (Dnat 4)) i = 0.
Proof. by split; [exact: data_nth_nat_Dnil | case: i]. Qed.

Example example_pair_is_not_a_list : data_nth_nat (Dpair (Dnat 4) Dnil) 0 != 4.
Proof. by []. Qed.

(** Position 0 is the natural value of the head entry (of the datum itself when it is no list cell). *)
Lemma example_head_value (e rest : data) : data_nth_nat (Dcons e rest) 0 = data_nat_value e.
Proof. exact: data_nth_nat0. Qed.

(** The adapters read an entry modulo [k]: modulo 3 here, and modulo 0 an entry keeps its value. *)
Example example_adapters : data_nth_nat out314 2 %% 3 = 1 /\ data_nth_nat out314 2 %% 0 = 4.
Proof. by []. Qed.

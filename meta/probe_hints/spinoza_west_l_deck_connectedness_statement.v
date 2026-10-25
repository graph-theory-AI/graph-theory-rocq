(** Witness hint (Any-lane guard, 2026-10-25): an axiom-free REFUTATION of
    [Reconstruction.conjectures.X21.spinoza_west_l_deck_connectedness_statement] as encoded
    before its [ell <= n] guard (corpus row studies:std_spinoza_west_connectedness_threshold_conjecture).

    The threshold hypothesis floor(n/2) + 1 <= ell does not bound ell by n.  Above the vertex
    count the ell-deck index type is empty, so [x21_same_l_deck] holds with the empty bijection.
    At n = 6, ell = 7 the complete graph K_6 (connected) and the edgeless graph on six vertices
    (not connected) refute the body.  With the guard [ell <= n] this file no longer compiles
    (hint-stale-FIX-OK). *)
From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph.
From GTBase Require Import base path_trees trees.
From Reconstruction.conjectures Require Import X21.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* Above the vertex count the ell-deck is empty, so any two graphs of that size share it. *)
Lemma deck_index_empty (G : sgraph) (ell : nat) :
  #|G| < ell -> x21_l_deck_index G ell -> False.
Proof.
move=> lt [S /eqP cS]; move: (max_card (mem S)); rewrite cS => le.
by move: (leq_ltn_trans le lt); rewrite ltnn.
Qed.

Lemma same_deck_above (G H : sgraph) (ell : nat) :
  #|G| < ell -> #|H| < ell -> x21_same_l_deck G H ell.
Proof.
move=> ltG ltH.
exists (fun S => False_rect _ (deck_index_empty ltG S)); split.
  exists (fun S => False_rect _ (deck_index_empty ltH S)) => S.
    by case: (deck_index_empty ltG S).
  by case: (deck_index_empty ltH S).
by move=> S; case: (deck_index_empty ltG S).
Qed.

(* A set closed under the edges separates its members from the other vertices. *)
Lemma not_connect_closed (G : sgraph) (a : pred G) (x y : G) :
  (forall u v : G, u -- v -> a u = a v) -> a x -> ~~ a y -> ~~ connect (--) x y.
Proof.
move=> cl ax nay; apply/negP => cxy.
have cla : closed (--) a by move=> u v /cl.
by move: (closed_connect cla cxy); rewrite !unfold_in ax (negbTE nay).
Qed.

(* Spinoza-West: K_6 is connected, the edgeless graph on six vertices is not. *)
Definition e6_rel : rel 'I_6 := fun _ _ => false.
Lemma e6_sym : symmetric e6_rel. Proof. by []. Qed.
Lemma e6_irrefl : irreflexive e6_rel. Proof. by []. Qed.
Definition E6 : sgraph := SGraph e6_sym e6_irrefl.

Lemma K6_connected : connected [set: 'K_6].
Proof.
apply: connectedTI => x y; case: (eqVneq x y) => [->|xy]; first exact: connect0.
by apply: connect1; rewrite /edge_rel /= xy.
Qed.

Lemma E6_not_connected : ~ connected [set: E6].
Proof.
move=> /connectedTE /(_ ord0 ord_max); apply/negP.
by apply: (@not_connect_closed E6 (fun v : 'I_6 => v == ord0)).
Qed.

Lemma refuted : ~ spinoza_west_l_deck_connectedness_statement.
Proof.
move=> /(_ 6 7 'K_6 E6 isT isT (card_ord 6) (card_ord 6)).
move=> /(_ (same_deck_above _ _)) h.
by apply: E6_not_connected; apply/h; rewrite ?card_ord //; exact: K6_connected.
Qed.

Print Assumptions refuted.

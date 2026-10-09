(** Downstream use of the directed disjoint union [digraph_sum] without conjecture imports: arcs through both
    injections, no arc across in either direction, a loop and an asymmetric arc kept as they are, and the number of
    vertices, with an empty summand. *)
From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph digraph_sum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PublicClient.
Variables D1 D2 : diGraphType.

(** Arcs inside each summand, through both injections; none across, in either direction. *)
Example digraph_sum_arcs (a b : D1) (c d : D2) :
  [/\ ((inl a : digraph_sum D1 D2) --> inl b) = (a --> b), ((inr c : digraph_sum D1 D2) --> inr d) = (c --> d),
      ((inl a : digraph_sum D1 D2) --> inr c) = false & ((inr c : digraph_sum D1 D2) --> inl a) = false].
Proof.
by split; [exact: digraph_sum_arc_inl | exact: digraph_sum_arc_inr | exact: digraph_sum_arc_inl_inr
          | exact: digraph_sum_arc_inr_inl].
Qed.

Example digraph_sum_vertices : #|{: digraph_sum D1 D2}| = #|D1| + #|D2|.
Proof. exact: card_digraph_sum. Qed.

End PublicClient.

(** Concrete summands: one vertex with a loop, one arc [false --> true] only, and no vertex at all. *)
Definition loop1 : Type := unit.
HB.instance Definition _ := Finite.on loop1.
HB.instance Definition _ := HasArc.Build loop1 (fun _ _ : unit => true).

Definition arrow2 : Type := bool.
HB.instance Definition _ := Finite.on arrow2.
HB.instance Definition _ := HasArc.Build arrow2 (fun u v : bool => ~~ u && v).

Definition empty0 : Type := 'I_0.
HB.instance Definition _ := Finite.on empty0.
HB.instance Definition _ := HasArc.Build empty0 (fun _ _ : 'I_0 => false).

(** The loop and the asymmetric arc are kept: no loopless or oriented condition. *)
Example digraph_sum_loop_asymmetry :
  [/\ ((inl tt : digraph_sum loop1 arrow2) --> inl tt),
      ((inr false : digraph_sum loop1 arrow2) --> inr true)
    & ~~ ((inr true : digraph_sum loop1 arrow2) --> inr false)].
Proof. by []. Qed.

(** An empty summand adds no vertex, on either side. *)
Example digraph_sum_empty :
  #|{: digraph_sum empty0 arrow2}| = 2 /\ #|{: digraph_sum arrow2 empty0}| = 2.
Proof. by rewrite !card_digraph_sum card_ord card_bool. Qed.

Print Assumptions digraph_sum_arcs.
Print Assumptions digraph_sum_vertices.
Print Assumptions digraph_sum_loop_asymmetry.
Print Assumptions digraph_sum_empty.

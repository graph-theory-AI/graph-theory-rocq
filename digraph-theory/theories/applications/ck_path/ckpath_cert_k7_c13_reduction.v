(** * Full-mask reductions for the k=7 C13 certificate families

    The C13 certificate generator substitutes every distinguished-set bit
    before emitting a DRAT trace.  The executable assignment below uses that
    same order: vertex zero first, then vertices one through [n - 1], including
    both the true and false mask positions.

    This module deliberately leaves [fixed_set_instance] and its graph theorem
    untouched.  The correspondence with its unit-clause suffix gives a small
    trusted bridge from the existing theorem to the reduced instances. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Stdlib Require Import List Bool Arith Lia.
From Digraph Require Import prelude digraph oriented dipath strong
  ckpath_odd_gateway ckpath_cnf ckpath_cnf_reduction ckpath_cert_base
  ckpath_cert_clause_tools ckpath_cert_k7_base ckpath_k7_orbits
  ckpath_cert_graph_k7_c13_semantics.
Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Executable full-mask specialization *)

Fixpoint fixed_set_assignment_from
    (n start : nat) (mask : list bool) : assignment :=
  match mask with
  | [] => []
  | b :: mask' =>
      (set_var n start, b) ::
        fixed_set_assignment_from n (S start) mask'
  end.

Definition fixed_set_assignment (n : nat) (mask : list bool) : assignment :=
  fixed_set_assignment_from n 0 mask.

Definition fixed_set_reduced_instance
    (base : cnf) (n : nat) (mask : list bool) : cnf :=
  reduce_cnf (fixed_set_assignment n mask) base.

(** The old unit suffix and the new partial assignment contain exactly the
    same literals in exactly the same order. *)
Lemma fixed_set_units_from_assignment n start mask :
  fixed_set_units_from n start mask =
  List.map (fun l : literal => [l])
    (fixed_set_assignment_from n start mask).
Proof.
revert start.
induction mask as [|b mask IH]; intros start; simpl.
- reflexivity.
- now rewrite IH.
Qed.

Lemma singleton_units_satisfied_extends rho (a : assignment) :
  satisfies_cnf rho (List.map (fun l : literal => [l]) a) ->
  extends rho a.
Proof.
move=> Hunits x b Hin.
have Hclause : eval_clause rho [(x, b)] = true.
  apply: (@eval_cnf_member rho
    (List.map (fun l : literal => [l]) a) [(x, b)] Hunits).
  apply: List.in_map.
  exact Hin.
change ((eval_literal rho (x, b) || false) = true) in Hclause.
rewrite orbF in Hclause.
exact: (proj1 (eval_literal_true_iff rho x b) Hclause).
Qed.

Lemma extends_singleton_units_satisfied rho (a : assignment) :
  extends rho a ->
  satisfies_cnf rho (List.map (fun l : literal => [l]) a).
Proof.
move=> Ha.
unfold satisfies_cnf, eval_cnf.
apply List.forallb_forall.
move=> unit Hunit.
apply List.in_map_iff in Hunit.
move: Hunit=> [l [<- Hin]].
case: l Hin=> x b Hin.
change ((eval_literal rho (x, b) || false) = true).
rewrite orbF.
apply: (proj2 (eval_literal_true_iff rho x b)).
exact: Ha x b Hin.
Qed.

Lemma fixed_set_assignment_from_bits_extends rho n start len bits :
  (forall i,
      (start <= i < start + len)%coq_nat ->
      rho (set_var n i) = bits i) ->
  extends rho
    (fixed_set_assignment_from n start
      (List.map bits (List.seq start len))).
Proof.
move=> Hbits.
apply: singleton_units_satisfied_extends.
rewrite <- fixed_set_units_from_assignment.
exact: fixed_set_units_from_bits_satisfied Hbits.
Qed.

Lemma fixed_set_assignment_extends_iff_units rho n mask :
  extends rho (fixed_set_assignment n mask) <->
  satisfies_cnf rho (fixed_set_units n mask).
Proof.
rewrite /fixed_set_assignment /fixed_set_units
  fixed_set_units_from_assignment.
split.
- exact: extends_singleton_units_satisfied.
- exact: singleton_units_satisfied_extends.
Qed.

Lemma fixed_set_reduced_instance_satisfied rho base n mask :
  extends rho (fixed_set_assignment n mask) ->
  satisfies_cnf rho base ->
  satisfies_cnf rho (fixed_set_reduced_instance base n mask).
Proof.
move=> Hextends Hbase.
rewrite /fixed_set_reduced_instance.
exact: (@reduce_cnf_sound rho (fixed_set_assignment n mask) base
  Hextends Hbase).
Qed.

(** Any witness for the preserved fixed-unit formulation is automatically a
    witness for the generator's fully specialized formulation. *)
Lemma fixed_set_instance_reduced_satisfied rho base n mask :
  satisfies_cnf rho (fixed_set_instance base n mask) ->
  satisfies_cnf rho (fixed_set_reduced_instance base n mask).
Proof.
rewrite /fixed_set_instance satisfies_cnf_app.
move=> [Hbase Hunits].
exact: (@fixed_set_reduced_instance_satisfied rho base n mask
  (proj2 (fixed_set_assignment_extends_iff_units rho n mask) Hunits)
  Hbase).
Qed.

(** ** C13 graph interfaces *)

Section C13ReducedGraphBridge.
Variable D : orientedDigraph.
Variables (c : list D) (S : {set D}).

Hypothesis Hreg : forall v : D, outdeg v = 7.
Hypothesis Hstr : strongb D.
Hypothesis Hell : ell D < 14.
Hypothesis Hcycle : dicycle c.
Hypothesis Hcsize : size c = 13.
Hypothesis HScard : #|S| = 7.
Hypothesis HSsub : S \subset odd_cycle_set c.
Hypothesis HSclosed :
  forall u v, u \in S -> u --> v -> v \in odd_cycle_set c.
Hypothesis Horder : 15 <= #|D|.

Local Notation A := (odd_active_set c).

(** One of the 22, 55, or 99 orbit-reduced formulas is realized, according
    as the active-set size is 3, 4, or 5. *)
Theorem ckpath_k7_c13_graph_reduced_instance_satisfied :
  exists m mask rho,
    [ /\ m = 3 \/ m = 4 \/ m = 5,
        #|A| = m,
        List.In mask (orbit_representatives 13 m)
      & satisfies_cnf rho
          (fixed_set_reduced_instance (c13_k7_cover_base m) 13 mask) ].
Proof.
have [m [mask [rho [Hm Hcard Hrep Hfixed]]]] :=
  @ckpath_k7_c13_graph_fixed_instance_satisfied
    D c S Hreg Hstr Hell Hcycle Hcsize HScard HSsub HSclosed Horder.
have Hreduced : satisfies_cnf rho
    (fixed_set_reduced_instance (c13_k7_cover_base m) 13 mask).
  exact: fixed_set_instance_reduced_satisfied Hfixed.
exists m, mask, rho.
by split.
Qed.

End C13ReducedGraphBridge.

(** * Equality case for the CK seven-outregular C12 low endpoints

    This small continuation module isolates the Hamilton-order equality
    case from the counting infrastructure in [ckpath_k7_c12_low_hand].
    Keeping the large constructive splice in a separate opaque unit bounds
    peak memory during physical compilation. *)

From HB Require Import structures.
From mathcomp Require Import all_boot zify.
From Stdlib Require Import Lia.
From Digraph Require Import
  prelude digraph oriented dipath ckpath_cycle_tools ckpath_even_gateway
  ckpath_kernel_prefix_adapters ckpath_k7_c12_low_hand
  ckpath_k7_c12_low_arc_hamilton.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section C12LowGe3.
Variable D : orientedDigraph.
Variables (c : seq D) (S : {set D}) (v0 v1 : D).

Hypothesis Hreg : forall v : D, outdeg v = 7.
Hypothesis Hell : ell D = 13.
Hypothesis Hprefix : ckpath_prefix2_data c S v0 v1.
Hypothesis Hcycle : dicycle c.
Hypothesis Hcsize : size c = 12.
Hypothesis HScard : #|S| = 7.

Local Notation C := (ckpath_cycle_set c).
Local Notation R := (ckpath_outside c).
Local Notation Q := (C :\: S).
Local Notation Low := (c12_k7_low_endpoints c).
Local Notation B := (ckpath_successor_set c S).

(** The equality case supplies one of the forbidden two-chord Hamilton
    orderings explicitly.  If [q --> r] is the arc between the two low
    vertices, then [r = next q].  Starting the ordinary cycle order at
    [next p], for [p in S] different from [prev q], delete [q] at its old
    position and append it after [p]. *)
Lemma c12_k7_low_exact_two_hamilton (Hcard : #|Low| = 2) :
  exists q, q \in Low /\ c12_k7_hamilton_from c B q.
Proof.
have LowSub := c12_k7_low_subset_complement Hreg Hprefix.
have LowN0 : Low != set0 by rewrite -card_gt0 Hcard.
move/set0Pn: LowN0 => [q qLow].
have restcard : #|Low :\ q| = 1.
  have h := cardsD1 q Low.
  move: h; rewrite qLow Hcard /= add1n => h.
  have hp := congr1 predn h.
  move: hp; rewrite /= => hp.
  exact: esym hp.
have restN0 : Low :\ q != set0 by rewrite -card_gt0 restcard.
move/set0Pn: restN0 => [r rRest].
have rDq : r != q.
  by move: rRest; rewrite !inE => /andP[].
have rLow : r \in Low.
  move: rRest; rewrite inE => /andP[_ rLow].
  exact rLow.
have qDr : q != r.
  apply/negP=> /eqP qr; subst r.
  by move: rDq; rewrite eqxx.
have qC : q \in C.
  by move: qLow; rewrite (c12_k7_low_endpointP c Hreg) => /andP[].
have rC : r \in C.
  by move: rLow; rewrite (c12_k7_low_endpointP c Hreg) => /andP[].
have /orP[aqr|arq] :=
  c12_k7_low_cycle_total Hreg Hprefix Hcycle Hcsize HScard
    Hcard qC rC qDr.
- exists q; split=> //.
  exact: (@c12_k7_low_arc_hamilton D c S v0 v1 Hreg Hell Hprefix
    Hcycle Hcsize HScard Hcard q r qLow rLow qDr aqr).
- exists r; split=> //.
  exact: (@c12_k7_low_arc_hamilton D c S v0 v1 Hreg Hell Hprefix
    Hcycle Hcsize HScard Hcard r q rLow qLow rDq arq).
Qed.

(** The aggregate degree deficit therefore forces at least three low cycle
    endpoints.  This is the hand strengthening used to expose a compact
    marker-cardinality constraint to the finite checker. *)
Theorem c12_k7_low_card_ge3 : 3 <= #|Low|.
Proof.
rewrite leqNgt; apply/negP=> hsmall.
have hge2 := c12_k7_low_card_ge2 Hreg Hprefix Hcycle Hcsize HScard.
have hle2 : #|Low| <= 2 by move: hsmall; rewrite ltnS.
have Hcard : #|Low| = 2.
  apply/eqP.
  by rewrite eqn_leq hle2 hge2.
have [q [qLow hham]] := c12_k7_low_exact_two_hamilton Hcard.
exact: (@c12_k7_low_no_hamilton D c S v0 v1 Hell Hprefix q qLow hham).
Qed.

End C12LowGe3.

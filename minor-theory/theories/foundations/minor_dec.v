(** * Minor.foundations.minor_dec -- decidability of [minor], and monotonicity of clique minors

    Two reusable facts about the library's [minor G H] ("G contains H as a minor"):

    - [minorP : reflect (minor G H) (minorb G H)].  On finite simple graphs [minor] is
      DECIDABLE: by [minorRE] / [minor_of_rmap] it is equivalent to the existence of a
      [minor_rmap], i.e. of a function [H -> {set G}], and each of the four clauses of
      [minor_rmap] is a Boolean condition ([connectedb] / [neighbor] are already Boolean).
      The consequence actually used by the implication edges is [minorNN] : a double
      negation of [minor G H] can be eliminated, which is what turns a corpus argument of
      the shape "if G had no [K_(h+1)] minor then ..." into a Rocq proof without any
      classical axiom.

    - [minor_K_le] : [minor G 'K_n] and [m <= n] give [minor G 'K_m] -- monotonicity of
      complete-graph minors in the order, via [minor_of_clique] on [[set: 'K_n]] and
      [minor_trans].  [minor_K1] is the [n = 1] base case for a nonempty graph. *)

From GTBase Require Export base.
From GraphTheory Require Import minor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Decidability of [minor] *********************************************)

Section MinorDec.
Variables (G H : sgraph).

(** Boolean form of [minor_rmap] (minor.v), on a [{ffun ...}] carrier. *)
Definition minor_rmapb (phi : {ffun H -> {set G}}) : bool :=
  [&& [forall x : H, phi x != set0],
      [forall x : H, connectedb (phi x)],
      [forall x : H, forall y : H, (x != y) ==> [disjoint phi x & phi y]] &
      [forall x : H, forall y : H, (x -- y) ==> neighbor (phi x) (phi y)]].

Definition minorb : bool := [exists phi : {ffun H -> {set G}}, minor_rmapb phi].

Lemma minorP : reflect (minor G H) minorb.
Proof.
apply: (iffP idP) => [/existsP[phi]|].
- case/and4P => /forallP p1 /forallP p2 /forallP p3 /forallP p4.
  apply: (@minor_of_rmap _ _ (fun x : H => phi x)); split.
  + exact: p1.
  + by move=> x; apply/connectedP; exact: p2.
  + by move=> x y xy; move: (p3 x) => /forallP/(_ y)/implyP; apply.
  + by move=> x y xy; move: (p4 x) => /forallP/(_ y)/implyP; apply.
- case/minorRE => phi [q1 q2 q3 q4]; apply/existsP; exists (finfun phi).
  apply/and4P; split.
  + by apply/forallP => x; rewrite ffunE; exact: q1.
  + by apply/forallP => x; rewrite ffunE; apply/connectedP; exact: q2.
  + apply/forallP => x; apply/forallP => y; apply/implyP => xy.
    by rewrite !ffunE; exact: q3.
  + apply/forallP => x; apply/forallP => y; apply/implyP => xy.
    by rewrite !ffunE; exact: q4.
Qed.

(** Double-negation elimination for [minor] -- the constructive content of
    decidability, and the only form the implication edges need. *)
Lemma minorNN : ~ ~ minor G H -> minor G H.
Proof.
move=> nn; have [m|/negP h] := boolP minorb; first exact/minorP.
by exfalso; apply: nn => /minorP mb; exact: h mb.
Qed.

End MinorDec.

(** ** Monotonicity of complete-graph minors *******************************)

Lemma minor_K_le (G : sgraph) (m n : nat) : m <= n -> minor G 'K_n -> minor G 'K_m.
Proof.
move=> mn h; apply: minor_trans h _.
apply: (@minor_of_clique _ [set: 'K_n] m); last exact: Kn_clique.
by rewrite cardsT card_ord.
Qed.

Lemma minor_K1 (G : sgraph) : 0 < #|G| -> minor G 'K_1.
Proof.
move=> /card_gt0P[x _].
by apply: (@minor_of_clique _ [set x] 1); [rewrite cards1 | exact: clique1].
Qed.

Print Assumptions minorP.
Print Assumptions minorNN.
Print Assumptions minor_K_le.
Print Assumptions minor_K1.

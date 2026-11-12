(** * Topological.conjectures.grounding_X305 -- grounding certificates for wave X305 (2026-11-12)

    Qed-closed, axiom-free certificates for the one row of [X305.v] (the Earth-Moon sub-bracket chi_EM <= 11):
    hyp_inhabited and not_trivially_true, and the equivalence of U13's union form of biplanarity with the record's
    partition form.  X305 declares no helper, so no helper_sanity.
    - hyp: K_4 is biplanar (both layers are K_4 itself, which has too few vertices for a K_5 or a K_(3,3) minor), so
      the hypothesis is inhabited, and the statement bounds the chromatic number of K_4 by 11.
    - ntt: ~ V /\ (V -> S), with V = "every graph has chromatic number at most 11" (the biplanarity dropped):
      V -> S by weakening, and ~ V at K_12, whose chromatic number is 12.
    - g305_union_partition: U13's union of two Wagner-planar layers is the record's partition into two disjoint
      Wagner-planar layers.
    They validate the statement; they do not prove it. *)

From GTBase Require Import base.
From GraphTheory Require Import minor.
From Topological.conjectures Require Import U13 X305.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The record's partition form of biplanarity: two disjoint Wagner-planar layers. *)
Definition g305_partition_biplanar (G : sgraph) : Prop :=
  exists (e1 e2 : rel G)
         (s1 : symmetric e1) (i1 : irreflexive e1)
         (s2 : symmetric e2) (i2 : irreflexive e2),
    [/\ wagner_planar (SGraph s1 i1), wagner_planar (SGraph s2 i2),
        forall x y : G, (x -- y) = e1 x y || e2 x y
      & forall x y : G, ~~ (e1 x y && e2 x y)].

(** A layer with fewer edges on the same vertices stays Wagner-planar (a minor of a subgraph is a minor). *)
Lemma g305_wagner_sub (V : finType) (e e' : rel V)
    (s : symmetric e) (i : irreflexive e) (s' : symmetric e') (i' : irreflexive e') :
  subrel e' e -> wagner_planar (SGraph s i) -> wagner_planar (SGraph s' i').
Proof.
move=> sub [n5 n33].
have m : minor (SGraph s i) (SGraph s' i').
  by apply: sub_minor; exists id => // x y /sub.
by split=> h; [apply: n5 | apply: n33]; exact: minor_trans m h.
Qed.

Lemma g305_union_partition (G : sgraph) :
  union_of_two_planar wagner_planar G <-> g305_partition_biplanar G.
Proof.
split.
- move=> [e1 [e2 [s1 [i1 [s2 [i2 [p1 p2 adj]]]]]]].
  pose e2' := fun x y : G => e2 x y && ~~ e1 x y.
  have s2' : symmetric e2' by move=> x y; rewrite /e2' s2 s1.
  have i2' : irreflexive e2' by move=> x; rewrite /e2' i2.
  exists e1, e2', s1, i1, s2', i2'; split => //.
  + by apply: g305_wagner_sub p2 => x y /andP [].
  + by move=> x y; rewrite adj /e2'; case: (e1 x y); case: (e2 x y).
  + by move=> x y; rewrite /e2'; case: (e1 x y); rewrite ?andbF.
- move=> [e1 [e2 [s1 [i1 [s2 [i2 [p1 p2 adj _]]]]]]].
  by exists e1, e2, s1, i1, s2, i2; split.
Qed.

(** K_4 is biplanar: both layers are K_4 itself, which has too few vertices for a K_5 or a K_(3,3) minor. *)
Lemma g305_K4_biplanar : union_of_two_planar wagner_planar 'K_4.
Proof.
exists (@sedge 'K_4), (@sedge 'K_4), (@sg_sym 'K_4), (@sg_irrefl 'K_4), (@sg_sym 'K_4), (@sg_irrefl 'K_4).
have wp : wagner_planar (SGraph (@sg_sym 'K_4) (@sg_irrefl 'K_4)).
  by split=> /minor_card; rewrite ?card_sum !card_ord.
by split=> // x y; rewrite orbb.
Qed.

(** K_12 needs 12 colours. *)
Lemma g305_K12_chi : χ([set: 'K_12]) = 12.
Proof. by rewrite chi_clique ?cardsT ?card_ord. Qed.

(* ** hyp_inhabited *)
Definition g305_hyp_claim : Prop :=
  union_of_two_planar wagner_planar 'K_4 /\
  (earth_moon_biplanar_chi_le_11_statement -> χ([set: 'K_4]) <= 11).

Theorem g305_hyp_inhabited : g305_hyp_claim.
Proof. by split=> [|S]; [exact: g305_K4_biplanar | exact: S _ g305_K4_biplanar]. Qed.

(* ** not_trivially_true *)
(** The bound without biplanarity: every graph has chromatic number at most 11. *)
Definition g305_all_chi_le_11 : Prop := forall G : sgraph, χ([set: G]) <= 11.

Definition g305_ntt_claim : Prop :=
  ~ g305_all_chi_le_11 /\ (g305_all_chi_le_11 -> earth_moon_biplanar_chi_le_11_statement).

Theorem g305_not_trivially_true : g305_ntt_claim.
Proof.
split=> [/(_ 'K_12)|V G _]; last exact: V.
by rewrite g305_K12_chi.
Qed.

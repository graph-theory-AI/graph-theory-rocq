(** * Minor.conjectures.grounding_X297 -- grounding lemmas for wave X297.

    Qed-closed, axiom-free certificates for the row of [X297.v] (hyp_inhabited, not_trivially_true; X297 declares
    no helper, so no helper_sanity).  The hyp witness is the class of edgeless graphs: its shallow minors and
    their subgraphs have no edge, so it satisfies both sides (f1 = 0, f6 = 1).  The ntt variant drops the
    hypothesis of each direction of the equivalence, i.e. asks every class to satisfy both sides; it fails for the
    class of all graphs, whose member K_n is its own subgraph (a shallow minor at depth 0) with independence number
    at most 1, so f6(0) would bound every n.  They validate the statement; they do not prove it (the converse is
    the paper's open Problem 8). *)

From GraphTheory Require Import minor.
From GTBase Require Import base common.
From Minor.foundations Require Import shallow_minors.
From Minor.conjectures Require Import X297.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* The two sides of the row for a class C, as printed in X297.v. *)
Definition g297_expansion (C : sgraph -> Prop) : Prop :=
  exists f1 : nat -> nat, forall (r : nat) (G H : sgraph),
    C G -> internal_shallow_minor G H r -> 2 * #|E(H)| <= f1 r * #|H|.

Definition g297_hall (C : sgraph -> Prop) : Prop :=
  exists f6 : nat -> nat, forall (r : nat) (G H K : sgraph),
    C G -> internal_shallow_minor G H r -> has_subgraph H K -> #|K| <= f6 r * α([set: K]).

(* The class of edgeless graphs. *)
Definition g297_edgeless (G : sgraph) : Prop := forall x y : G, ~~ (x -- y).

(* A shallow minor of an edgeless graph is edgeless: a pattern edge needs a host edge between two branch sets. *)
Lemma g297_edgeless_shallow (G H : sgraph) (r : nat) :
  g297_edgeless G -> internal_shallow_minor G H r -> g297_edgeless H.
Proof.
move=> eG [B [ctr [[_ _ _ hE] _ _]]] x y; apply/negP => /hE /existsP [u /andP [_ /existsP [v /andP [_ uv]]]].
by move: (eG u v); rewrite uv.
Qed.

(* A subgraph of an edgeless graph is edgeless. *)
Lemma g297_edgeless_sub (H K : sgraph) : g297_edgeless H -> has_subgraph H K -> g297_edgeless K.
Proof.
move=> eH /has_subgraphP [f [_ hf]] x y; apply/negP => /hf fxy.
by move: (eH (f x) (f y)); rewrite fxy.
Qed.

Lemma g297_edgeless_E (H : sgraph) : g297_edgeless H -> #|E(H)| = 0.
Proof.
move=> eH; apply/eqP; rewrite cards_eq0; apply/eqP/setP => e; rewrite inE.
apply/negP => /imset2P [x y _]; rewrite inE => /andP [_ xy] _.
by move: (eH x y); rewrite xy.
Qed.

(* An edgeless graph is independent as a whole. *)
Lemma g297_edgeless_alpha (K : sgraph) : g297_edgeless K -> #|K| <= α([set: K]).
Proof.
move=> eK; rewrite -cardsT; apply: stabset_bound; rewrite inE subxx /=.
by apply/stableP => u v _ _; exact: eK.
Qed.

(* hyp: the edgeless class satisfies both sides.  The claim names the row (gate_contracts: a claim mentions every
   reference): the statement at the edgeless class gives its equivalence, whose two sides both hold there. *)
Definition g297_bsh_hyp_claim : Prop :=
  [/\ g297_expansion g297_edgeless, g297_hall g297_edgeless
    & (bounded_expansion_shallow_minor_hall_ratio_statement ->
       (g297_expansion g297_edgeless <-> g297_hall g297_edgeless))].

Theorem g297_bsh_hyp_inhabited : g297_bsh_hyp_claim.
Proof.
split.
- exists (fun _ => 0) => r G H eG sm.
  by rewrite (g297_edgeless_E (g297_edgeless_shallow eG sm)).
- exists (fun _ => 1) => r G H K eG sm sub; rewrite mul1n.
  exact: g297_edgeless_alpha (g297_edgeless_sub (g297_edgeless_shallow eG sm) sub).
- by move=> S; exact: S g297_edgeless.
Qed.

(* The complete graph K_n has independence number at most 1. *)
Lemma g297_alpha_K (n : nat) : α([set: 'K_n]) <= 1.
Proof.
case: alphaP => S; rewrite !inE => /andP [/andP [_ st] _].
apply/card_le1_eqP => x y xS yS; apply/eqP; apply: contraT => xy.
move/stableP: st => /(_ x y xS yS).
by rewrite (Kn_clique (in_setT x) (in_setT y)) // eq_sym.
Qed.

(* ntt: every class satisfying both sides, i.e. the row without the hypothesis of either direction. *)
Definition g297_bsh_both : Prop := forall C : sgraph -> Prop, g297_expansion C /\ g297_hall C.

Definition g297_bsh_ntt_claim : Prop :=
  ~ g297_bsh_both /\ (g297_bsh_both -> bounded_expansion_shallow_minor_hall_ratio_statement).

Theorem g297_bsh_not_trivially_true : g297_bsh_ntt_claim.
Proof.
split.
- move=> /(_ (fun _ => True)) [_ [f6 h]].
  pose K := 'K_(f6 0).+1.
  have sm : internal_shallow_minor K K 0 by apply/internal_shallow_minor0E; exact: has_subgraph_refl.
  have := h 0 K K K I sm (has_subgraph_refl K).
  rewrite card_ord => le; have := leq_trans le (leq_mul (leqnn (f6 0)) (g297_alpha_K _)).
  by rewrite muln1 ltnn.
- by move=> V C; split=> _; [exact: (V C).2 | exact: (V C).1].
Qed.

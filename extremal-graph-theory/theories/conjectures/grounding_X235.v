(** * Extremal.conjectures.grounding_X235 -- grounding certificates of wave X235.

    For the row arxiv:2103.15175#00: hyp_inhabited (the guards hold at s = 2, k = 1, and the
    statement then yields lists on K_3 forcing a colour class of chromatic number greater than 2) and
    not_trivially_true (the contract form of meta/EXPANSION_PLAN.md 4.4: with BOTH guards dropped the
    row fails at s = k = 0, since 0 ^ 0 = 1 and K_1 already forces with the empty lists, and that
    unguarded variant implies the row; extras: K_3 is forced and K_2 is not at s = 2, k = 1, so the
    reading R_l = s^k is false).  Either guard alone is not load-bearing (Notes of X235.v).
    helper_sanity covers the four local definitions of X235.v, each with a positive and a negative
    instance on K_2 or K_3.  Small instances: the constant 1-lists [:: 0] on K_2 and K_3, lists
    differing between the two orientations of the edge of K_2, constant colourings. *)

From GTBase Require Import base.
From Extremal.conjectures Require Import X235.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Instances *)

(** A constant colour graph is complete, or edgeless off its colour. *)
Lemma g235_const_edge (V : finType) (c d : nat) (x y : lr_color_graph (fun _ _ : V => c) d) :
  (x -- y) = (x != y) && (c == d).
Proof. by rewrite /edge_rel /= /fg_srel orbb. Qed.

(** 1-lists on K_3 force a colour class of chromatic number 3 > 2. *)
Lemma g235_forces_2_1_3 : lr_nat_graph_forces 2 1 3.
Proof.
exists (fun _ _ => [:: 0]); split; first by split=> // x y _.
move=> phi [sym adm]; exists 0.
have cl : clique [set: lr_color_graph phi 0].
  move=> x y _ _ xy; rewrite /edge_rel /= /fg_srel xy /=.
  by have := adm x y xy; rewrite inE => ->.
by rewrite (chi_clique cl) cardsT card_ord.
Qed.

(** On K_2 the colour graph of the forced colour has chromatic number at most 2. *)
Lemma g235_not_forces_2_1_2 : ~ lr_nat_graph_forces 2 1 2.
Proof.
case=> L [[sym valid] force].
pose o1 : 'I_2 := Ordinal (isT : 1 < 2).
have e (z : 'I_2) : z = ord0 \/ z = o1.
  by case: z => [[|[|z]] hz] //; [left|right]; apply: val_inj.
have [_ s01] := valid ord0 o1 isT.
pose a := head 0 (L ord0 o1).
have a01 : a \in L ord0 o1.
  by rewrite /a; case: (L ord0 o1) s01 => // b l _; exact: mem_head.
have a10 : a \in L o1 ord0 by rewrite sym.
have adm : lr_nat_admissible L (fun _ _ => a).
  split=> // x y xy.
  by case: (e x) xy => ->; case: (e y) => ->.
have [c hc] := force _ adm.
have := leq_chi [set: lr_color_graph (fun _ _ : 'I_2 => a) c].
by rewrite cardsT card_ord leqNgt hc.
Qed.

(** With the empty lists, K_1 forces a colour class of chromatic number 1 > 0. *)
Lemma g235_forces_0_0_1 : lr_nat_graph_forces 0 0 1.
Proof.
exists (fun _ _ => [::]); split; first by split=> // x y _.
move=> phi _; exists 0.
have cl : clique [set: lr_color_graph phi 0].
  by move=> x y _ _; rewrite (ord1 x) (ord1 y) eqxx.
by rewrite (chi_clique cl) cardsT card_ord.
Qed.

(** Lists that differ between the two orientations of the edge of K_2. *)
Definition g235_skew_lists (x y : 'I_2) : seq nat := if x == ord0 then [:: 0] else [:: 1].

(** ** helper_sanity *)

Definition g235_helpers_claim : Prop :=
  [/\ lr_nat_valid_lists 1 (fun _ _ : 'I_2 => [:: 0]) /\ ~ lr_nat_valid_lists 1 g235_skew_lists,
      lr_nat_admissible (fun _ _ : 'I_2 => [:: 0]) (fun _ _ => 0) /\
        ~ lr_nat_admissible (fun _ _ : 'I_2 => [:: 0]) (fun _ _ => 1),
      (forall x y : lr_color_graph (fun _ _ : 'I_3 => 0) 0, (x -- y) = (x != y)) /\
        (forall x y : lr_color_graph (fun _ _ : 'I_3 => 0) 1, ~~ (x -- y))
    & lr_nat_graph_forces 2 1 3 /\ ~ lr_nat_graph_forces 2 1 2].

Theorem g235_helpers_sanity : g235_helpers_claim.
Proof.
split.
- split; first by split=> // x y _.
  case=> sym _; have := sym ord0 (Ordinal (isT : 1 < 2)) 0.
  by rewrite /g235_skew_lists.
- split; first by split=> // x y _.
  by case=> _ /(_ ord0 (Ordinal (isT : 1 < 2)) isT).
- by split=> x y; rewrite g235_const_edge ?andbT ?andbF.
- by split; [exact: g235_forces_2_1_3 | exact: g235_not_forces_2_1_2].
Qed.

(** ** Row arxiv:2103.15175#00 *)

Definition g235_hyp_claim : Prop :=
  [/\ 2 <= 2, 0 < 1 &
      (list_ramsey_chromatic_resolution_statement -> lr_nat_graph_forces 2 1 (2 ^ 1).+1)].

Theorem g235_hyp_inhabited : g235_hyp_claim.
Proof. by split=> // h; have [] := h 2 1 (leqnn 2) isT. Qed.

(** The row with both guards dropped: false at s = k = 0 (0 ^ 0 = 1, and K_1 forces). *)
Definition g235_unguarded : Prop :=
  forall s k : nat,
    lr_nat_graph_forces s k (s ^ k).+1 /\
    forall n, lr_nat_graph_forces s k n -> (s ^ k).+1 <= n.

(** An extra: the reading R = s^k (without the + 1) is false at s = 2, k = 1. *)
Definition g235_exact_sk : Prop :=
  forall s k : nat, 2 <= s -> 0 < k ->
    lr_nat_graph_forces s k (s ^ k) /\ forall n, lr_nat_graph_forces s k n -> s ^ k <= n.

Definition g235_ntt_claim : Prop :=
  [/\ ~ g235_unguarded, g235_unguarded -> list_ramsey_chromatic_resolution_statement,
      lr_nat_graph_forces 2 1 3, ~ lr_nat_graph_forces 2 1 2 & ~ g235_exact_sk].

Theorem g235_not_trivially_true : g235_ntt_claim.
Proof.
split.
- move=> h; have [_ low] := h 0 0.
  by have := low 1 g235_forces_0_0_1.
- by move=> h s k _ _; exact: h s k.
- exact: g235_forces_2_1_3.
- exact: g235_not_forces_2_1_2.
- by move=> h; have [f _] := h 2 1 (leqnn 2) isT; exact: g235_not_forces_2_1_2 f.
Qed.

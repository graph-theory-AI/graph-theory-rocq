(** * Reconstruction.examples.decks — public-only client of Reconstruction.foundations.decks

    Imports GTBase.base and Reconstruction.foundations.decks only, no conjecture or migration module.
    - Positive: every graph has the same deck and the same edge deck as itself, and a card of the triangle has two
      vertices.
    - Negative, vertex decks: [K_2] and the edgeless graph [E2] on two vertices have the same deck (each card is a
      single vertex) but are not isomorphic, so the Reconstruction Conjecture needs its order guard (at least 3).
    - Negative, edge decks: [K_1] and [E2] are both edgeless, so they have the same (empty) edge deck, yet they have
      different orders and are not isomorphic, so edge reconstruction needs a positive edge-count guard (the
      Edge Reconstruction Conjecture's is 4). *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph bij.
From GTBase Require Import base.
From Reconstruction Require Import foundations.decks.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The edgeless graph on two vertices. *)
Definition e2_rel : rel 'I_2 := fun _ _ => false.
Lemma e2_sym : symmetric e2_rel. Proof. by []. Qed.
Lemma e2_irrefl : irreflexive e2_rel. Proof. by []. Qed.
Definition E2 : sgraph := SGraph e2_sym e2_irrefl.

(** ** Positive *)

Example example_same_deck_self : same_deck 'K_3 'K_3 /\ same_edge_deck 'K_3 'K_3.
Proof. by split; [exact: same_deck_refl | exact: same_edge_deck_refl]. Qed.

Example example_triangle_card (v : 'K_3) : #|vdel_card v| = 2.
Proof. by rewrite card_vdel_card card_ord. Qed.

(** ** Negative: the vertex-order guard *)

(** Two distinct vertices of ['I_2] both different from [v] coincide. *)
Lemma I2_other (v x y : 'I_2) : x != v -> y != v -> x = y.
Proof.
by case: v x y => [[|[|//]] ?] [[|[|//]] ?] [[|[|//]] ?] //= _ _; apply: val_inj.
Qed.

Lemma example_K2_E2_same_deck : same_deck 'K_2 E2.
Proof.
exists (id : 'K_2 -> E2); split; first by exists id.
move=> v; constructor.
pose phi (x : vdel_card v) : vdel_card (v : E2) := Sub (val x : E2) (valP x).
pose psi (x : vdel_card (v : E2)) : vdel_card v := Sub (val x : 'K_2) (valP x).
apply: (@Diso' _ _ phi psi); [by move=> x; apply: val_inj | by move=> x; apply: val_inj |].
move=> x y; rewrite /edge_rel /= /e2_rel.
have xv : (val x : 'I_2) != v by have := valP x; rewrite inE.
have yv : (val y : 'I_2) != v by have := valP y; rewrite inE.
by rewrite (I2_other xv yv) !sg_irrefl.
Qed.

Lemma example_K2_E2_not_iso : ~ inhabited ('K_2 ≃ E2).
Proof.
case=> h; have := edge_diso h (ord0 : 'K_2) (ord_max : 'K_2).
by rewrite /edge_rel /= /e2_rel.
Qed.

(** ** Negative: the edge-count guard *)

Lemma E_K1 : E('K_1) = set0.
Proof. by apply/setP => e; rewrite inE; apply/edgesP => -[x [y [_ xy]]]; rewrite (ord1 x) (ord1 y) sg_irrefl in xy. Qed.

Lemma E_E2 : E(E2) = set0.
Proof. by apply/setP => e; rewrite inE; apply/edgesP => -[x [y [_ xy]]]. Qed.

Lemma example_K1_E2_same_edge_deck : same_edge_deck 'K_1 E2.
Proof. exact: edgeless_same_edge_deck E_K1 E_E2. Qed.

Lemma example_K1_E2_not_iso : ~ inhabited ('K_1 ≃ E2).
Proof. by case=> h; have := card_bij (diso_v h); rewrite !card_ord. Qed.

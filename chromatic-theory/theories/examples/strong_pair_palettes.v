(** * Chromatic.examples.strong_pair_palettes — public-only client of Chromatic.foundations.strong_pair_palettes (D13)

    Compiles against GTBase.base and the public module alone (no conjecture or migration module).  The empty host
    ['K_0] has every palette, zero included; the nonempty edgeless host ['K_1] has none at 0 (the map is total) and
    one at 1; the single edge of ['K_2] needs exactly one colour (its only pair is never distinct from itself); and in
    ['K_3] the edges [{0, 1}] and [{1, 2}] are distinct and near, so one colour is not enough. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph.
From GTBase Require Import base.
From Chromatic Require Import foundations.strong_pair_palettes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation k2 i := (@Ordinal 2 i isT) (only parsing).
Local Notation k3 i := (@Ordinal 3 i isT) (only parsing).

Lemma K2_vertex (x : 'K_2) : x = k2 0 \/ x = k2 1.
Proof. by case: x => -[|[|//]] Hx; [left | right]; apply: val_inj. Qed.

(** The empty host: every palette, zero included. *)
Lemma example_K0 : strong_pair_colourable 'K_0 0 /\ strong_pair_colourable 'K_0 6.
Proof. by split; apply: strong_pair_colourable_card0; rewrite card_ord. Qed.

(** A nonempty edgeless host: no map into the empty palette, one colour suffices. *)
Lemma example_K1 : ~ strong_pair_colourable 'K_1 0 /\ strong_pair_colourable 'K_1 1.
Proof.
split; first by move/strong_pair_colourable0; rewrite card_ord.
by apply: strong_pair_colourable_edgeless => // x y; rewrite (ord1 x) (ord1 y) sg_irrefl.
Qed.

(** A genuine edge: one colour, not zero. *)
Lemma example_K2 : strong_pair_colourable 'K_2 1 /\ ~ strong_pair_colourable 'K_2 0.
Proof.
split; last by move/strong_pair_colourable0; rewrite card_ord.
exists (fun _ _ => ord0); split=> // x y u v.
by case: (K2_vertex x) => ->; case: (K2_vertex y) => ->; case: (K2_vertex u) => ->; case: (K2_vertex v) => ->.
Qed.

(** Near distinct edges: [{0, 1}] and [{1, 2}] of ['K_3] need two colours. *)
Lemma example_K3_near : ~ strong_pair_colourable 'K_3 1.
Proof. by move/(@strong_pair_colourable_two 'K_3 1 (k3 0) (k3 1) (k3 1) (k3 2)) => /(_ isT isT isT isT). Qed.

Print Assumptions example_K0.
Print Assumptions example_K1.
Print Assumptions example_K2.
Print Assumptions example_K3_near.

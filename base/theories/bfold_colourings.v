(** * GTBase.bfold_colourings -- (a:b)-fold vertex colourings over a supplied palette

    [bfold_colouring b f] (with [G] and the palette size [a] implicit, read off [f : G -> {set 'I_a}]): the supplied
    map [f] gives every vertex [v] a [b]-element set [f v] of colours from the palette ['I_a], and adjacent vertices
    receive disjoint sets.  The palette size and the map are supplied data: unused colours are allowed and no quotient
    by palette permutations is taken.  Degenerate cases, all without any guard:
    - [b = 0]: the constant empty map is a 0-fold colouring of every graph over every palette ([bfold_colouring0]);
    - an empty vertex type: every map is an (a:b)-colouring ([bfold_colouring_empty]);
    - a vertex forces [b <= a] ([bfold_colouring_le]) and an edge forces [2 * b <= a] ([bfold_colouring_edge]).
    A ratio [a / b] is not part of this contract.  The fractional-chromatic notions built on it keep their own
    [0 < b] guards and stay distinct: Chromatic X130's existential cross-multiplied bound and Extremal D2chr's
    attained rational minimum.  This focused module has no conjecture imports and no base re-export.
    Registry: meta/library_primitives/bfold-colouring.json. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition bfold_colouring (G : sgraph) (a b : nat) (f : G -> {set 'I_a}) : Prop :=
  (forall v : G, #|f v| = b) /\ (forall x y : G, x -- y -> [disjoint f x & f y]).

(** The finite (boolean) form. *)
Lemma bfold_colouringP (G : sgraph) (a b : nat) (f : G -> {set 'I_a}) :
  reflect (bfold_colouring b f)
          ([forall v, #|f v| == b] && [forall x, forall y, (x -- y) ==> [disjoint f x & f y]]).
Proof.
apply: (iffP andP) => [[/forallP c /forallP d]|[c d]]; split.
- by move=> v; apply/eqP.
- by move=> x y; move: (d x) => /forallP /(_ y) /implyP.
- by apply/forallP => v; apply/eqP.
- by apply/forallP => x; apply/forallP => y; apply/implyP; exact: d.
Qed.

(** [b = 0]: the constant empty map. *)
Lemma bfold_colouring0 (G : sgraph) (a : nat) : bfold_colouring 0 (fun _ : G => (set0 : {set 'I_a})).
Proof. by split=> [v|x y _]; [rewrite cards0 | rewrite -setI_eq0 setI0]. Qed.

(** An empty vertex type: every map. *)
Lemma bfold_colouring_empty (G : sgraph) (a b : nat) (f : G -> {set 'I_a}) :
  #|G| = 0 -> bfold_colouring b f.
Proof. by move=> G0; split=> [v|v]; case: (fintype0 v G0). Qed.

(** A vertex forces [b <= a]. *)
Lemma bfold_colouring_le (G : sgraph) (a b : nat) (f : G -> {set 'I_a}) (v : G) :
  bfold_colouring b f -> b <= a.
Proof. by case=> /(_ v) <- _; have := max_card (f v); rewrite card_ord. Qed.

(** An edge forces [2 * b <= a]. *)
Lemma bfold_colouring_edge (G : sgraph) (a b : nat) (f : G -> {set 'I_a}) (x y : G) :
  bfold_colouring b f -> x -- y -> 2 * b <= a.
Proof.
case=> card disj xy; have := max_card (f x :|: f y); rewrite card_ord.
by rewrite cardsU (disjoint_setI0 (disj x y xy)) cards0 subn0 !card addnn -mul2n.
Qed.

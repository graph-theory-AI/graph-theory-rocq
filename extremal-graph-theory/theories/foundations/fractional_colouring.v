(** * Extremal.foundations.fractional_colouring — the attained fractional chromatic number

    Family [fractional-chromatic] (meta/library_primitives/fractional-chromatic.json).
    [is_fractional_chromatic G r] says that [r] is the fractional chromatic number chi_f(G) as an ATTAINED
    RATIONAL MINIMUM over (a:b)-colourings with a POSITIVE denominator [b]:
    - attainment: some (a:b)-colouring with [0 < b] has [r = a/b];
    - minimality: [r <= a/b] for every (a:b)-colouring with [0 < b].
    An (a:b)-colouring is [GTBase.bfold_colourings.bfold_colouring b f] for a supplied [f : G -> {set 'I_a}]:
    every vertex gets a b-element subset of the palette ['I_a] and adjacent vertices get disjoint subsets.  The
    b-fold contract itself allows [b = 0]; the positive denominator belongs to this relation, in both clauses.

    Degenerate cases: there is no guard on [G].  On the empty graph the (0:1)-colouring is attained and every
    a/b is non-negative, so chi_f = 0 ([is_fractional_chromatic_empty]); rows that need a non-empty graph keep
    their own guard.  The value is unique ([is_fractional_chromatic_unique]).  Its EXISTENCE for every finite
    graph is the LP attainment theorem [Atlas.foundations.fractional.frac_chromatic_exists] (through
    [Extremal.foundations.lp_rational.lp_max_fin]); it is not assumed here.

    Distinct notions, not defined here: the existential cross-multiplied natural bound
    [Chromatic.conjectures.X130.x130_frac_chi_le] (its own [0 < b], vacuous for [q = 0]); the circular
    chromatic number [Extremal.foundations.circular_colouring.is_circular_chromatic] (the same attained-minimum
    shape over (p,q)-colourings of an abstract adjacency); the colouring-mixing threshold of D2chr (an infimum
    without attainment).  The body is that of [Extremal.conjectures.D2chr.is_fractional_chromatic], whose name
    is a transparent alias of this one since the fractional-chromatic library migration. *)

From GTBase Require Import base bfold_colourings.
From mathcomp Require Import all_algebra.
Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Definition is_fractional_chromatic (G : sgraph) (r : rat) : Prop :=
  (exists a b : nat, (0 < b)%N /\ (exists f, @bfold_colouring G a b f) /\ r = a%:Q / b%:Q) /\
  (forall a b : nat, (0 < b)%N -> (exists f, @bfold_colouring G a b f) -> r <= a%:Q / b%:Q).

(** ** The two clauses *)

Lemma is_fractional_chromatic_attained (G : sgraph) (r : rat) :
  is_fractional_chromatic G r ->
  exists a b : nat, [/\ (0 < b)%N, exists f : G -> {set 'I_a}, bfold_colouring b f & r = a%:Q / b%:Q].
Proof. by case=> -[a [b [b0 [hf ->]]]] _; exists a, b. Qed.

Lemma is_fractional_chromatic_le (G : sgraph) (r : rat) (a b : nat) (f : G -> {set 'I_a}) :
  is_fractional_chromatic G r -> (0 < b)%N -> bfold_colouring b f -> r <= a%:Q / b%:Q.
Proof. by case=> _ H b0 hf; apply: H b0 _; exists f. Qed.

(** ** Uniqueness, sign, the empty graph *)

Lemma is_fractional_chromatic_unique (G : sgraph) (r1 r2 : rat) :
  is_fractional_chromatic G r1 -> is_fractional_chromatic G r2 -> r1 = r2.
Proof.
move=> h1 h2; apply: order.Order.POrderTheory.le_anti; apply/andP; split.
- by have [a [b [b0 [f hf] ->]]] := is_fractional_chromatic_attained h2; exact: is_fractional_chromatic_le h1 b0 hf.
- by have [a [b [b0 [f hf] ->]]] := is_fractional_chromatic_attained h1; exact: is_fractional_chromatic_le h2 b0 hf.
Qed.

Lemma is_fractional_chromatic_ge0 (G : sgraph) (r : rat) : is_fractional_chromatic G r -> 0 <= r.
Proof. by case/is_fractional_chromatic_attained => a [b [_ _ ->]]; rewrite divr_ge0 // ler0z. Qed.

(** The empty graph has fractional chromatic number 0: the (0:1)-colouring is attained (every map is a
    colouring of an empty vertex type) and every ratio a/b is non-negative. *)
Lemma is_fractional_chromatic_empty (G : sgraph) : #|G| = 0%N -> is_fractional_chromatic G 0.
Proof.
move=> G0; split.
  exists 0%N, 1%N; split=> //; split; last by rewrite mul0r.
  by exists (fun _ => set0); exact: bfold_colouring_empty.
by move=> a b _ _; rewrite divr_ge0 // ler0z.
Qed.

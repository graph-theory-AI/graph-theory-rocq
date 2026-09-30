(** * Chromatic.foundations.poly_forms -- the two normal forms of "polynomially chi-bounded"

    The chi-boundedness corpus rows encode "the class F is polynomially
    chi-bounded" in TWO ways:

      [x3_polynomially_chi_bounded F]  (X3.v, used by X65.v and X66.v)
        -- some coefficient list [p : seq nat] bounds [chi(G)] by the HORNER
           evaluation [x3_poly_eval p (omega(G))];

      [poly_chi_bounded F]             (chi_bounding.v, used by X218.v)
        -- some [c], [d] bound [chi(G)] by the NORMAL FORM [c * omega(G) ^ d].

    Over the naturals the two are EQUIVALENT, and this file proves both
    directions once and for all:

      [x3_poly_chi_boundedW] : list form  ==> normal form   (uses F4,
        [chi_bounding.horner_nat_dom], plus the [omega(G) = 0] corner: a graph
        with clique number zero has no vertex, hence chromatic number zero);
      [poly_chi_bounded_x3W] : normal form ==> list form    (the coefficient
        list of [c * t ^ d] is [d] zeros followed by [c]).

    Every wave-X218/X65/X66 edge that crosses the two encodings goes through
    these two lemmas. *)

From GTBase Require Export base.
From Chromatic.foundations Require Import chi_bounding.
From Chromatic.conjectures Require Import X3.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** X3's Horner [Fixpoint] is the [foldr] of [chi_bounding.horner_nat]. *)
Lemma x3_poly_evalE (p : seq nat) (x : nat) : x3_poly_eval p x = horner_nat p x.
Proof. by elim: p => //= a p ->. Qed.

(** F4 in the form used by the edges: Horner domination for [x3_poly_eval]. *)
Lemma x3_poly_eval_dom (p : seq nat) (t : nat) :
  1 <= t -> x3_poly_eval p t <= (\sum_(i <- p) i) * t ^ (size p).-1.
Proof. by rewrite x3_poly_evalE; exact: horner_nat_dom. Qed.

(** A graph with clique number zero has no vertices, hence chromatic number
    zero: this is what covers the [t = 0] corner of the domination bound. *)
Lemma chi_eq0_omega0 (G : sgraph) : ω([set: G]) = 0 -> χ([set: G]) = 0.
Proof. by move/eqP; rewrite omega_eq0 => /eqP ->; exact: chi0. Qed.

(** The coefficient list of the monomial [c * t ^ d]: [d] zeros, then [c]. *)
Lemma x3_poly_eval_monomial (c d t : nat) :
  x3_poly_eval (nseq d 0 ++ [:: c]) t = c * t ^ d.
Proof.
elim: d => [|d IH] /=; first by rewrite muln0 addn0 expn0 muln1.
by rewrite IH expnS mulnCA.
Qed.

(** ** The two conversions ************************************************)

(** List form ==> normal form.  [c] is the sum of the coefficients and [d] the
    degree; for [omega(G) >= 1] this is F4, and for [omega(G) = 0] the graph is
    empty so both sides are trivially ordered. *)
Lemma x3_poly_chi_boundedW (F : sgraph -> Prop) :
  x3_polynomially_chi_bounded F -> poly_chi_bounded F.
Proof.
case=> p Hp; exists (\sum_(i <- p) i), (size p).-1 => G FG.
case: (posnP (ω([set: G]))) => [w0|wpos]; first by rewrite (chi_eq0_omega0 w0).
by apply: leq_trans (Hp G FG) _; exact: x3_poly_eval_dom.
Qed.

(** Normal form ==> list form. *)
Lemma poly_chi_bounded_x3W (F : sgraph -> Prop) :
  poly_chi_bounded F -> x3_polynomially_chi_bounded F.
Proof.
case=> c [d] H; exists (nseq d 0 ++ [:: c]) => G FG.
by rewrite x3_poly_eval_monomial; exact: H.
Qed.

(** The two encodings of "polynomially chi-bounded" agree. *)
Lemma poly_chi_bounded_x3E (F : sgraph -> Prop) :
  x3_polynomially_chi_bounded F <-> poly_chi_bounded F.
Proof. by split; [exact: x3_poly_chi_boundedW | exact: poly_chi_bounded_x3W]. Qed.

Print Assumptions x3_poly_eval_dom.
Print Assumptions x3_poly_chi_boundedW.
Print Assumptions poly_chi_bounded_x3W.
Print Assumptions poly_chi_bounded_x3E.

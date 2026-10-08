(** * Chromatic.foundations.poly_forms -- the two normal forms of "polynomially chi-bounded"

    The chi-boundedness corpus rows encode "the class F is polynomially
    chi-bounded" in TWO ways:

      [poly_list_chi_bounded F]        (chi_bounding.v; X3's [x3_polynomially_chi_bounded],
                                        used by X65.v and X66.v, and X124's [x124_poly_chi_bounded]
                                        are aliases of it since the A32 library migration)
        -- some coefficient list [p : seq nat] bounds [chi(G)] by the HORNER
           evaluation [GTBase.poly_nat.horner_nat p (omega(G))];

      [poly_chi_bounded F]             (chi_bounding.v, used by X218.v)
        -- some [c], [d] bound [chi(G)] by the NORMAL FORM [c * omega(G) ^ d].

    Over the naturals the two are EQUIVALENT, and this file proves both
    directions once and for all:

      [x3_poly_chi_boundedW] : list form  ==> normal form   (uses F4,
        [GTBase.poly_nat.horner_nat_dom], plus the [omega(G) = 0] corner: a graph
        with clique number zero has no vertex, hence chromatic number zero);
      [poly_chi_bounded_x3W] : normal form ==> list form    (the coefficient
        list of [c * t ^ d] is [d] zeros followed by [c]).

    Every wave-X218/X65/X66 edge that crosses the two encodings goes through
    these two lemmas.  This foundation imports no conjecture file: since the A32
    library migration its lemmas keep their names and are stated over the owners'
    constants, to which X3's names are aliases, so each complete type is
    convertible to the former X3-stated one. *)

From GTBase Require Export base.
From Chromatic.foundations Require Import chi_bounding.
From GTBase Require poly_nat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** X3's Horner evaluation is [chi_bounding.horner_nat]: since the A31 library migration both are aliases of
    [GTBase.poly_nat.horner_nat] (this statement is X3's [x3_poly_eval p x = horner_nat p x] up to that alias). *)
Lemma x3_poly_evalE (p : seq nat) (x : nat) : GTBase.poly_nat.horner_nat p x = horner_nat p x.
Proof. by []. Qed.

(** F4 in the form used by the edges: Horner domination. *)
Lemma x3_poly_eval_dom (p : seq nat) (t : nat) :
  1 <= t -> GTBase.poly_nat.horner_nat p t <= (\sum_(i <- p) i) * t ^ (size p).-1.
Proof. exact: GTBase.poly_nat.horner_nat_dom. Qed.

(** A graph with clique number zero has no vertices, hence chromatic number
    zero: this is what covers the [t = 0] corner of the domination bound. *)
Lemma chi_eq0_omega0 (G : sgraph) : ω([set: G]) = 0 -> χ([set: G]) = 0.
Proof. by move/eqP; rewrite omega_eq0 => /eqP ->; exact: chi0. Qed.

(** The coefficient list of the monomial [c * t ^ d]: [d] zeros, then [c]. *)
Lemma x3_poly_eval_monomial (c d t : nat) :
  GTBase.poly_nat.horner_nat (nseq d 0 ++ [:: c]) t = c * t ^ d.
Proof. exact: GTBase.poly_nat.horner_nat_monomial. Qed.

(** ** The two conversions ************************************************)

(** List form ==> normal form.  [c] is the sum of the coefficients and [d] the
    degree; for [omega(G) >= 1] this is F4, and for [omega(G) = 0] the graph is
    empty so both sides are trivially ordered. *)
Lemma x3_poly_chi_boundedW (F : sgraph -> Prop) :
  poly_list_chi_bounded F -> poly_chi_bounded F.
Proof.
case=> p Hp; exists (\sum_(i <- p) i), (size p).-1 => G FG.
case: (posnP (ω([set: G]))) => [w0|wpos]; first by rewrite (chi_eq0_omega0 w0).
by apply: leq_trans (Hp G FG) _; exact: x3_poly_eval_dom.
Qed.

(** Normal form ==> list form. *)
Lemma poly_chi_bounded_x3W (F : sgraph -> Prop) :
  poly_chi_bounded F -> poly_list_chi_bounded F.
Proof.
case=> c [d] H; exists (nseq d 0 ++ [:: c]) => G FG.
by rewrite x3_poly_eval_monomial; exact: H.
Qed.

(** The two encodings of "polynomially chi-bounded" agree. *)
Lemma poly_chi_bounded_x3E (F : sgraph -> Prop) :
  poly_list_chi_bounded F <-> poly_chi_bounded F.
Proof. by split; [exact: x3_poly_chi_boundedW | exact: poly_chi_bounded_x3W]. Qed.

Print Assumptions x3_poly_eval_dom.
Print Assumptions x3_poly_chi_boundedW.
Print Assumptions poly_chi_bounded_x3W.
Print Assumptions poly_chi_bounded_x3E.

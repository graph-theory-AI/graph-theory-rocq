(** * Chromatic.conjectures.implications_X65 -- a Rocq-only EDGE between X3 and X65 (polynomial Gyarfas-Sumner).

    X3 (arxiv:2110.00278#00, [polynomial_gyarfas_sumner_statement]) states the polynomial Gyarfas-Sumner
    conjecture with the bound omega ^ c: for every forest H there is c > 0 such that every H-free graph has
    chi <= omega ^ c.  X65 (arxiv:2202.05557#00, [forest_free_polynomial_chi_bound_statement]) allows any
    polynomial in omega ([x3_polynomially_chi_bounded], a list of natural coefficients evaluated by
    [GTBase.poly_nat.horner_nat]); its Notes call it formally weaker.  The theorem below records the Rocq-only
    equivalence (no corpus relation): the two rows state one conjecture.
    Forward: X3's c gives the list nseq c 0 ++ [:: 1], whose value is omega ^ c.  Backward: from X65's list p,
    with s the sum of its coefficients and d = (size p).-1, the exponent (s + d).+1 serves: omega = 0 means no
    vertex (chi = 0); omega = 1 means no edge, since an edge is a clique on two vertices, so a constant colouring
    is proper (chi <= 1); omega >= 2 gives p(omega) <= s * omega ^ d <= omega ^ (s + d).+1, as s < 2 ^ s.
    Axiom-free: only [Qed]-closed results, and no helper of its own. *)

From GTBase Require Import base colourings.
From GTBase Require poly_nat.
From Chromatic.conjectures Require Import U8 X3 X65.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Polynomial Gyarfas-Sumner: the bound omega ^ c (X3) <=> any polynomial in omega (X65) *)

(*@EDGE from=polynomial_gyarfas_sumner_statement to=forest_free_polynomial_chi_bound_statement kind=equiv status=verified proof=polynomial_gyarfas_sumner_equiv_forest_free_polynomial_chi_bound note="Rocq-only edge (no corpus relation), routed by Lancelot's (729), (731): the polynomial Gyarfas-Sumner conjecture as arxiv:2110.00278#00 (X3: for every forest H some c > 0 with chi <= omega^c on H-free graphs) and as arxiv:2202.05557#00 (X65: any polynomial in omega, which X65's Notes call formally weaker). Forward: the coefficient list nseq c 0 ++ [:: 1] has value omega^c. Backward: from X65's list p (s its coefficient sum, d its size less one), the exponent (s + d).+1: omega = 0 gives no vertex, omega = 1 no edge (chi <= 1), omega >= 2 gives p(omega) <= s * omega^d <= omega^(s + d).+1. Both rows are partial." *)
Theorem polynomial_gyarfas_sumner_equiv_forest_free_polynomial_chi_bound :
  polynomial_gyarfas_sumner_statement <-> forest_free_polynomial_chi_bound_statement.
Proof.
split=> [h H fH | h H fH].
- have [c [_ hc]] := h H fH.
  exists (nseq c 0 ++ [:: 1]) => G HG.
  by rewrite GTBase.poly_nat.horner_nat_monomial mul1n; exact: hc.
- have [p hp] := h H fH.
  set s := \sum_(i <- p) i; set d := (size p).-1.
  exists (s + d).+1; split=> // G HG.
  have hG := hp G HG; set w := ω([set: G]) in hG *.
  case: (ltngtP w 1) => [w0|w2|w1].
  + have : w == 0 by rewrite -leqn0 -ltnS.
    by rewrite /w omega_eq0 => /eqP ->; rewrite chi0.
  + apply: (leq_trans hG); apply: (leq_trans (GTBase.poly_nat.horner_nat_dom p (ltnW w2))).
    rewrite -/s -/d expnS expnD; apply: leq_trans (leq_pmull _ (ltnW w2)).
    by rewrite leq_mul2r (ltnW (ltn_expl s w2)) orbT.
  + rewrite w1 exp1n.
    have noedge (x y : G) : x -- y -> false.
      move=> xy; have := @clique_bound G [set x; y] [set: G].
      rewrite inE subsetT andTb => /(_ (introT (cliqueP _) (clique2 xy))).
      by rewrite cards2 (sg_edgeNeq xy) -/w w1.
    have pc : proper_colouring (fun _ : G => tt).
      by apply/proper_colouringP => x y /noedge.
    by apply: leq_trans (proper_colouring_chi pc) _; rewrite card_unit.
Qed.

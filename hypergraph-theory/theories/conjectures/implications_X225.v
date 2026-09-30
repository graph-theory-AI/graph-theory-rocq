(** * Hypergraph.conjectures.implications_X225 -- implication edges for wave X225

    Wave X225 has four nodes, in two corpus-related pairs:

      arxiv:2206.13635#00  [kt_minor_free_hypergraph_chromatic_three_halves_statement]
      arxiv:2206.13635#01  [k3_minor_free_hypergraph_three_colourable_statement]
      arxiv:2401.00359#01  [kpartite_hypergraph_turan_exponent_dmax_statement]
      arxiv:2401.00359#02  [latin_square_hypergraph_turan_exponent_statement]

    The corpus records one confirmed [implies] relation inside each pair:

      e049  #00 ==> #01  "Pure restriction: setting t = 3 in h(t) = ceil(3(t-1)/2) gives
            h(3) = 3, i.e. every K_3-minor-free hypergraph is 3-colorable, which is verbatim
            the target problem."  -- VERIFIED here.
      e145  2401.00359#01 ==> #02  "For a d x d Latin square, d_1(H_L), d_2(H_L) = Theta(d),
            so d_max(H_L) = Theta(d) and 6.2 gives ex(n,H_L) <= n^{3-Omega(1/d)}.  The
            matching lower bound is unconditional from the paper's proven Theorem 1.4."
            -- CANDIDATE: the reduction consumes the paper's PROVEN Theorem 1.4 (the
            Omega(n^{k-C_k/d_1(H)}) lower bound) and the computation d_max(H_L) = Theta(d),
            neither of which is formalised; Conjecture 6.2 alone yields only the upper half
            of Conjecture 6.4.  See the annotation below.

    [Print Assumptions] on the proved theorem is clean; the file contains no [Axiom] /
    [Parameter] / [Admitted]. *)

From GTBase Require Import base.
From Hypergraph.foundations Require Import hypergraph.
From Hypergraph.conjectures Require Import X225.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** e049.  Conjecture 2 at [t = 3] is Problem 1: [ceil_div (3 * 2) 2] computes to 3, and the
    universal half of the conjecture is exactly the target statement. *)
Theorem kt_minor_free_hypergraph_chromatic_three_halves_implies_k3_minor_free_hypergraph_three_colourable :
  kt_minor_free_hypergraph_chromatic_three_halves_statement ->
  k3_minor_free_hypergraph_three_colourable_statement.
Proof.
move=> H T E lp nm.
have [up _] := H 3 isT.
by have := up T E lp nm.
Qed.

(*@EDGE from=kt_minor_free_hypergraph_chromatic_three_halves_statement to=k3_minor_free_hypergraph_three_colourable_statement kind=implies status=verified proved=true proof=kt_minor_free_hypergraph_chromatic_three_halves_implies_k3_minor_free_hypergraph_three_colourable cite="gc:e049" note="Instantiate t := 3: ceil_div (3 * 3.-1) 2 = 3, so the universal half of Conjecture 2 at t = 3 IS Problem 1. Pure restriction, no external input." *)

(*@EDGE from=kpartite_hypergraph_turan_exponent_dmax_statement to=latin_square_hypergraph_turan_exponent_statement kind=implies status=candidate proved=false cite="gc:e145" note="Does NOT close from the two committed statements. Conjecture 6.2 gives only the UPPER half of Conjecture 6.4 (ex(n,H_L)^dmax * n^ck <= K n^{3 dmax}), and only after the unformalised computation d_max(H_L) = Theta(d) that converts the H_L-dependent exponent into the absolute constant b; the LOWER half of 6.4 comes from the paper's PROVEN Theorem 1.4, which is not part of either statement. Formalising the edge needs those two external ingredients." *)

Print Assumptions kt_minor_free_hypergraph_chromatic_three_halves_implies_k3_minor_free_hypergraph_three_colourable.

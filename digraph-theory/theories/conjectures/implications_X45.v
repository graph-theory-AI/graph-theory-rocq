(** * Digraph.conjectures.implications_X45 — wave X45 implication edges

      - e038 : arxiv:1608.03040#00 ==> arxiv:1608.03040#02
               (majority 3-colouring ==> the beta-version row: some beta < 1
               works on every loopless digraph).

    VERIFIED: take beta = 1/2.  [majority_col col] of conjectures/colouring_variants.v is
    [forall v, 2 * #|same_col_outnb col v| <= outdeg v] over ALL digraphs, and the X45 body
    (re-encoded 2026-10-25) asks for p < q with
    [forall v, q * x45_same_colour_outneighbours col v <= p * outdeg v] on loopless digraphs,
    where [x45_same_colour_outneighbours col v = #|[set w | (v --> w) && (col w == col v)]|]
    is the same cardinal.  So the edge is p = 1, q = 2, the [loopless] guard unused, a change
    of notation and the [reflect] step out of the boolean [forall]. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented.
From Digraph.conjectures Require Import colouring_variants X45.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The two local vocabularies agree on the nose. *)
Lemma x45_same_colour_outneighboursE (D : diGraphType) (col : D -> 'I_3) (v : D) :
  x45_same_colour_outneighbours col v = #|same_col_outnb col v|.
Proof. by []. Qed.

(*@EDGE from=majority_3col_statement to=majority_three_colouring_beta_statement kind=implies status=verified proof=majority_3col_implies_majority_three_colouring_beta cite="gc:e038" note="Take beta = 1/2 (p = 1, q = 2) and ignore the target's loopless guard: x45_same_colour_outneighbours col v is by conversion #|same_col_outnb col v|, so the boolean majority_col col of the source unfolds (via forallP) to the pointwise 2 * #same <= 1 * outdeg of the target." *)

Theorem majority_3col_implies_majority_three_colouring_beta :
  majority_3col_statement -> majority_three_colouring_beta_statement.
Proof.
move=> H; exists 1, 2; split => // D _; have [col Hcol] := H D; exists col => v.
by rewrite mul1n x45_same_colour_outneighboursE; exact: (forallP Hcol v).
Qed.

(** ** Print Assumptions audit *)

Print Assumptions majority_3col_implies_majority_three_colouring_beta.

(** * Digraph.conjectures.implications_X45 — wave X45 implication edges

      - e038 : arxiv:1608.03040#00 ==> arxiv:1608.03040#02
               (majority 3-colouring ==> the beta-version row, whose body
               encodes beta = 1/2).

    VERIFIED: the two bodies are the SAME condition written with two local
    vocabularies — [majority_col col] of conjectures/colouring_variants.v is
    [forall v, 2 * #|same_col_outnb col v| <= outdeg v] and the X45 body is
    [forall v, 2 * x45_same_colour_outneighbours col v <= outdeg v] with
    [x45_same_colour_outneighbours col v = #|[set w | (v --> w) && (col w == col v)]|],
    i.e. the same cardinal.  So the edge is a change of notation plus the
    [reflect] step out of the boolean [forall]. *)

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

(*@EDGE from=majority_3col_statement to=majority_three_colouring_beta_statement kind=implies status=verified proof=majority_3col_implies_majority_three_colouring_beta cite="gc:e038" note="Same condition, two vocabularies: x45_same_colour_outneighbours col v is by conversion #|same_col_outnb col v|, so the boolean majority_col col of the source unfolds (via forallP) to the pointwise 2 * #same <= outdeg of the target; the X45 body already encodes beta = 1/2, so no parameter monotonicity step is needed." *)

Theorem majority_3col_implies_majority_three_colouring_beta :
  majority_3col_statement -> majority_three_colouring_beta_statement.
Proof.
move=> H D; have [col Hcol] := H D; exists col => v.
by rewrite x45_same_colour_outneighboursE; exact: (forallP Hcol v).
Qed.

(** ** Print Assumptions audit *)

Print Assumptions majority_3col_implies_majority_three_colouring_beta.

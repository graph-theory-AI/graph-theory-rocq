(** * GTMisc.conjectures.implications_X227 -- wave X227 corpus-relation edges

    The confirmed corpus relations (meta/corpus_relations.json) whose two endpoints are
    both formalized in this package.

    - e061 (arxiv:1812.09752#00 implies arxiv:2107.05995#00) is a genuine
      conjunction-to-conjunct edge and is proved below: part (ii) of Problem 1.4 IS the
      degeneracy-bound belief.  It is deliberately recorded as a weak consistency signal
      only: a projection out of an [and3] is trivial by construction, and the value of
      proving it is that the two rows really do share ONE hat-game vocabulary
      ([x227_hat_guessing_le], [k_degenerate]) rather than two incompatible encodings.
    - e149 (arxiv:2208.06858#01 implies arxiv:2208.06858#00) and e152
      (arxiv:2208.06858#03 implies arxiv:2208.06858#04) join rows whose SOURCE endpoint is
      a BLOCKED placeholder, so no relative theorem is stated: the placeholder bodies do
      not encode the rows' quantities (see the Notes in X227.v).  Both are recorded as
      candidates with proved=false.
    - e150 (arxiv:2208.06858#00 equivalent_to arxiv:2208.06858#02) and e151
      (arxiv:2208.06858#03 implies arxiv:2208.06858#02) have their other endpoint in
      homomorphism-theory (wave X227:homomorphism-theory), so they are not annotated here;
      they belong to the package that owns the Kneser-power statement.

    The file is axiom-free: no Axiom/Parameter/Admitted, and no [Theorem ... Qed] asserting
    an unproven edge. *)

From GTBase Require Import base.
From GTMisc.conjectures Require Import X227.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*@EDGE from=hat_guessing_degree_degeneracy_bounds_statement to=hat_guessing_degeneracy_bounded_statement kind=implies status=verified proof=hat_guessing_degree_degeneracy_bounds_implies_hat_guessing_degeneracy_bounded cite="gc:e061" note="Conjunction-to-conjunct: part (ii) of Alon-Ben-Eliezer-Shangguan-Tamo Problem 1.4 is verbatim the Alon-Chizewer degeneracy-bound belief. Trivial by construction; recorded as a shared-vocabulary consistency check, not as evidence." *)
Theorem hat_guessing_degree_degeneracy_bounds_implies_hat_guessing_degeneracy_bounded :
  hat_guessing_degree_degeneracy_bounds_statement ->
  hat_guessing_degeneracy_bounded_statement.
Proof. by case=> _ [f2 H2] _; exists f2. Qed.

(*@EDGE from=levine_hat_monotone_success_vanishes_statement to=levine_hat_intersecting_success_vanishes_statement kind=implies status=candidate proved=false cite="gc:e149" note="Both endpoints are BLOCKED placeholders whose bodies keep only the recorded properties of the success sequence (probability, non-increasing) and carry the winning-set class as an inert label, so the corpus argument (intersecting families are among the balanced monotone ones, hence p_monotone >= p_intersecting) is NOT represented. No relative theorem is stated: a proof here would be an artefact of the placeholders, not of the conjectures." *)

(*@EDGE from=independent_set_correlated_gap_statement to=independent_set_binomial_gap_statement kind=implies status=candidate proved=false cite="gc:e152" note="The source endpoint is a BLOCKED placeholder: the correlated-distribution quantity alpha*(G) is not expressible in GTBase, and the placeholder body IS the binomial special case, i.e. the target. The edge is real in the literature (the binomial distribution is the independent member of the positively-correlated class) but is not machine-witnessed here; stating it would prove nothing." *)

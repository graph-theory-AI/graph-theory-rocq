(** * Digraph.conjectures.grounding_X51 — guard grounding for the X51 row

    GROUNDING for the 2026-10-25 looplessness guard of row arxiv:1608.03040#06
    ([majority_choosable_universal_constant_statement], Open Problem 7).

    THE GUARD IS NOT VACUOUS: [x51_hyps_nonvacuous] — for every list size c, the
    directed triangle [C3] (a tournament, hence loopless) with the full palette
    ['I_c] at every vertex is non-empty and meets both hypotheses of the guarded
    body.  The guard's teeth (a looped vertex refutes the unguarded body for every
    c) are in meta/probe_hints/majority_choosable_universal_constant_statement.v,
    outside the package, so that this file carries no refutation of a committed
    row.

    Every lemma is closed by [Qed] and axiom-free. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented tournament X51.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma x51_hyps_nonvacuous (c : nat) :
  exists (D : diGraphType) (L : D -> {set 'I_c}),
    [/\ irreflexive (@arc D), (0 < #|D|)%N & forall v : D, (c <= #|L v|)%N].
Proof.
exists (C3 : diGraphType), (fun _ => setT); split.
- exact: C3_irrefl.
- by rewrite card_C3.
- by move=> v; rewrite cardsT card_ord.
Qed.

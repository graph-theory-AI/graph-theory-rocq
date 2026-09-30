(** * Chromatic.conjectures.X183 -- v2 d-degenerate list-flexibility row *)

From GTBase Require Export base.
From Chromatic.conjectures Require Import X132.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X183 statements *****************************************************)

(** Corpus row: arxiv:1612.08698#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1612.08698__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1612.08698__00.json
    English statement: (Dvorak, Norin and Postle 2018, Problem 1, arXiv:1612.08698)
      For every d there is a positive rational p/q with p <= q such that every d-degenerate finite
      simple graph is weighted p/q-flexible for lists of size d+1: for every list assignment with
      lists of size at least d+1 and every weighted request there is a proper list colouring
      satisfying at least the fraction p/q of the total request weight.
    Definitions: [weighted_epsilon_flexible G k p q] - the weighted flexibility predicate just
      described, cross-multiplied over the naturals (GTBase base/theories/list_flexibility.v);
      [k_degenerate G d] - every nonempty vertex subset contains a vertex of degree at most d inside
      it (GTBase base/theories/base.v).
    Notes: KNOWN UNFAITHFUL ENCODING, corpus leg blocked. The faithfulness audit of 2026-07-17,
      meta/BLOCKED_RETARGETING_AUDIT.md and the row's verification_note, found a fatal mis-
      quantification of the list size: base's [weighted_epsilon_flexible] requires lists of size AT
      LEAST d+1 while summing the request weight over ALL colours of each list, and weighted
      flexibility is not monotone in the list size, so the Rocq statement is provably FALSE rather
      than the open problem, which is about lists of size EXACTLY d+1. The source also offers the
      weaker unweighted variant, which is not the one encoded. The body is left untouched here, WP4
      changes comments only. *)
Definition degenerate_list_flexibility_d_plus_one_statement : Prop :=
  forall d : nat,
    exists p q : nat,
      [/\ 0 < p, p <= q &
        forall G : sgraph,
          k_degenerate G d ->
          weighted_epsilon_flexible G d.+1 p q].

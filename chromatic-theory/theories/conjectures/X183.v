(** * Chromatic.conjectures.X183 -- v2 d-degenerate list-flexibility row *)

From GTBase Require Export base.
From Chromatic.conjectures Require Import X132.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X183 vocabulary ***********************************************)

(** Weighted p/q-flexibility for lists of size EXACTLY [k]: for every list assignment whose lists
    all have [k] colours and every weighted request (a nonnegative integer weight for each vertex
    and colour), some proper list colouring satisfies at least the fraction p/q of the total
    request weight over the listed colours.  The base predicate [weighted_epsilon_flexible] asks
    for lists of size AT LEAST [k]; with arbitrarily long lists no fixed fraction can be
    satisfied, so the source's problem needs the exact size. *)
Definition x183_weighted_flexible_exact (G : sgraph) (k p q : nat) : Prop :=
  forall (C : finType) (L : G -> {set C}) (w : G -> C -> nat),
    (forall v : G, #|L v| = k) ->
    exists f : G -> C,
      proper_list_colouring L f /\
      p * weighted_request_total L w <= q * weighted_request_satisfied w f.

(** ** X183 statements *****************************************************)

(** Corpus row: arxiv:1612.08698#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1612.08698__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1612.08698__00.json
    English statement: (Dvorak, Norin and Postle 2018, Problem 1, arXiv:1612.08698)
      For every d there is a positive rational p/q with p <= q such that every d-degenerate finite
      simple graph is weighted p/q-flexible for lists of size d+1: for every list assignment with
      lists of size exactly d+1 and every weighted request there is a proper list colouring
      satisfying at least the fraction p/q of the total request weight.
    Definitions: [x183_weighted_flexible_exact G k p q] - the weighted flexibility predicate just
      described, for lists of size exactly k, cross-multiplied over the naturals (this file);
      [proper_list_colouring], [weighted_request_total], [weighted_request_satisfied] (GTBase
      base/theories/list_flexibility.v); [k_degenerate G d] - every nonempty vertex subset contains
      a vertex of degree at most d inside it (GTBase base/theories/base.v).
    Notes: RE-ENCODED 2026-10-25 (coordination/PROGRAMME.md, A1). Until then the body used base's
      [weighted_epsilon_flexible G d.+1 p q], whose lists have size AT LEAST d+1 while the request
      weight sums over all colours of each list: a vertex with a list of q+1 colours, each requested
      with weight 1, then defeats every p/q, so that body was false (faithfulness audit of
      2026-07-17, meta/BLOCKED_RETARGETING_AUDIT.md; kernel-checked in
      meta/probe_hints/degenerate_list_flexibility_d_plus_one_statement.v). The source's lists
      have size exactly d+1. Natural weights and a rational epsilon = p/q lose nothing: the
      condition is invariant under scaling the weights, the rational requests are dense among the
      real ones for each of the finitely many colourings, and a real epsilon can be lowered to a
      rational one; p <= q is harmless since at most the whole weight is satisfied. The source
      also asks the weaker unweighted question ("or at least epsilon-flexible"); the weighted one
      is encoded. *)
Definition degenerate_list_flexibility_d_plus_one_statement : Prop :=
  forall d : nat,
    exists p q : nat,
      [/\ 0 < p, p <= q &
        forall G : sgraph,
          k_degenerate G d ->
          x183_weighted_flexible_exact G d.+1 p q].

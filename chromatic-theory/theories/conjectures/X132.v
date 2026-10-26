(** * Chromatic.conjectures.X132 -- v2 planar list-flexibility row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X132 vocabulary ***********************************************)

(** Triangle-free: base's [triangle_free], equal for simple graphs to girth at least four
    ([girth_geq4_equiv_triangle_free]). *)
Definition x132_triangle_free (G : sgraph) : Prop := triangle_free G.

(** Weighted p/q-flexibility for lists of size EXACTLY [k] (the notion of X183's
    [x183_weighted_flexible_exact]): for every list assignment whose lists all have [k] colours and
    every weighted request (a nonnegative integer weight for each vertex and colour), some proper
    list colouring satisfies at least the fraction p/q of the total request weight over the listed
    colours.  The base predicate [weighted_epsilon_flexible] asks for lists of size AT LEAST [k];
    with arbitrarily long lists no fixed fraction can be satisfied, so the source's problem needs
    the exact size. *)
Definition x132_weighted_flexible_exact (G : sgraph) (k p q : nat) : Prop :=
  forall (C : finType) (L : G -> {set C}) (w : G -> C -> nat),
    (forall v : G, #|L v| = k) ->
    exists f : G -> C,
      proper_list_colouring L f /\
      p * weighted_request_total L w <= q * weighted_request_satisfied w f.

(** ** X132 statements *****************************************************)

(** Corpus row: studies:std_dvo_k_norin_postle_flexibility_conjecture_planar
    Site: none
    Review: none
    English statement: (Dvorak, Norin and Postle, studies slice of the corpus)
      There is a positive rational p/q with p <= q such that every planar finite simple graph G is
      weighted p/q-flexible for lists of size exactly 5, and moreover for lists of size exactly 4
      when G is triangle-free, and for lists of size exactly 3 when G has girth at least 5.
    Definitions: [x132_weighted_flexible_exact G k p q] - for every finite palette, every assignment
      of lists of size exactly k and every natural-valued request weight, there is a proper list
      colouring satisfying at least the fraction p/q of the total request weight, cross-multiplied
      over the naturals (this file, over GTBase base/theories/list_flexibility.v); [x132_triangle_free G]
      - girth at least 4, which for simple graphs is triangle-freeness (this file); [wagner_planar],
      [girth_geq] (GTBase base.v).
    Notes: This row has no site or review page in the corpus, hence the literal "none" above. The
      corpus row is a QUESTION covering three cases; the Rocq body is its affirmative reading with
      the three cases as a conjunction under one uniform epsilon, represented as the rational p/q.
      The real epsilon of the source is replaced by a rational, which is no loss for a uniform lower
      bound on a fraction of weights. Source repair 2026-10-25 (coordination/PROGRAMME.md A2; record
      meta/STATEMENT_IMPROVEMENTS.md): the body used GTBase's [weighted_epsilon_flexible], lists of
      size AT LEAST k, while the total request weight sums over every listed colour, so the planar
      one-vertex graph with one list of q+5 colours, each requested with weight 1, refuted it
      (meta/probe_hints/dvorak_norin_postle_planar_list_flexibility_statement.v). The source's lists
      have the stated sizes exactly. The cited papers prove case (b) (arXiv:1902.02971, Theorem 2) and
      case (c) for girth at least 6 (arXiv:1902.04069); the conjunction remains open. *)
Definition dvorak_norin_postle_planar_list_flexibility_statement : Prop :=
  exists p q : nat,
    [/\ 0 < p, p <= q &
      forall G : sgraph,
        wagner_planar G ->
        x132_weighted_flexible_exact G 5 p q /\
        (x132_triangle_free G -> x132_weighted_flexible_exact G 4 p q) /\
        (girth_geq G 5 -> x132_weighted_flexible_exact G 3 p q)].

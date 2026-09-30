(** * Chromatic.conjectures.X132 -- v2 planar list-flexibility row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X132 vocabulary ***********************************************)

(** Triangle-free, for simple graphs, is represented by girth at least four. *)
Definition x132_triangle_free (G : sgraph) : Prop := girth_geq G 4.

(** ** X132 statements *****************************************************)

(** Corpus row: studies:std_dvo_k_norin_postle_flexibility_conjecture_planar
    Site: none
    Review: none
    English statement: (Dvorak, Norin and Postle, studies slice of the corpus)
      There is a positive rational p/q with p <= q such that every planar finite simple graph G is
      weighted p/q-flexible for lists of size 5, and moreover for lists of size 4 when G is
      triangle-free, and for lists of size 3 when G has girth at least 5.
    Definitions: [weighted_epsilon_flexible G k p q] - for every finite palette, every assignment
      of lists of size at least k and every natural-valued request weight, there is a proper list
      colouring satisfying at least the fraction p/q of the total request weight, cross-multiplied
      over the naturals (GTBase base/theories/list_flexibility.v); [x132_triangle_free G] - girth at
      least 4, which for simple graphs is triangle-freeness (this file); [wagner_planar],
      [girth_geq] (GTBase base.v).
    Notes: This row has no site or review page in the corpus, hence the literal "none" above. The
      corpus row is a QUESTION covering three cases; the Rocq body is its affirmative reading with
      the three cases as a conjunction under one uniform epsilon, represented as the rational p/q.
      The real epsilon of the source is replaced by a rational, which is no loss for a uniform lower
      bound on a fraction of weights. *)
Definition dvorak_norin_postle_planar_list_flexibility_statement : Prop :=
  exists p q : nat,
    [/\ 0 < p, p <= q &
      forall G : sgraph,
        wagner_planar G ->
        weighted_epsilon_flexible G 5 p q /\
        (x132_triangle_free G -> weighted_epsilon_flexible G 4 p q) /\
        (girth_geq G 5 -> weighted_epsilon_flexible G 3 p q)].

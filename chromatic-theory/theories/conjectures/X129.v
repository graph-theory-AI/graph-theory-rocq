(** * Chromatic.conjectures.X129 -- v2 planar girth-5 square-colouring row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X129 vocabulary ************************************************)

(** Maximum degree Δ(G): the sgraph maximum degree [Delta] from base
    (Δ(G) = max over v of |N(v)|). *)
Definition x129_maxdeg (G : sgraph) : nat := Delta G.

(** ** X129 statements ******************************************************)

(** Corpus row: studies:std_dvo_k_kr_nejedl_krekovski_conjecture_square_of_p
    Site: none
    Review: none
    English statement: (Dvorak, Kral, Nejedly and Skrekovski, studies slice of the corpus)
      There is a threshold D0 such that every planar finite simple graph G of girth at least 5 whose
      maximum degree is at least D0 satisfies chi(G^2) <= Delta(G) + 2, where G^2 is the square of
      G, i.e. two distinct vertices are adjacent when they are at distance at most 2.
    Definitions: [x129_maxdeg G] - a local synonym for base's [Delta G] (this file); [graph_power
      G 2] - the square of G (GTBase base/theories/base.v); [wagner_planar G] - no K5 and no K3,3
      minor, which is planarity by Wagner's theorem (base.v); [girth_geq G 5] - every cycle has at
      least 5 vertices (base.v).
    Notes: This row has no site or review page in the corpus, hence the literal "none" above.
      Faithfulness points inherited from the previous comment: girth at least 5 uses [girth_geq],
      not base's [has_girth] which means girth EXACTLY 5 and would wrongly exclude planar graphs of
      larger girth; the threshold D0 is in the order there exists D0 for all G, i.e. uniform; and
      the hypotheses are jointly satisfiable for every D0, for instance by a large star, so the
      statement is not vacuous. *)
Definition dvorak_kral_nejedly_skrekovski_planar_girth5_square_statement : Prop :=
  exists D0 : nat,
    forall G : sgraph,
      wagner_planar G ->
      girth_geq G 5 ->
      (D0 <= x129_maxdeg G)%N ->
      (χ([set: graph_power G 2]) <= x129_maxdeg G + 2)%N.

(** * Extremal.conjectures.X310 -- v2 row: the fractional 8/3 conjecture of Cames van Batenburg et al. (a
      triangle-free subcubic graph with none of six graphs as a subgraph is fractionally 8/3-colourable) *)

From GTBase Require Import base common bfold_colourings.
From Extremal.conjectures Require Import X287.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X310 statement ********************************************************* *)

(** Corpus row: studies:std_cames_van_batenburg_et_al_conjecture_fractional
    Site: none
    Review: none
    English statement: (Cames van Batenburg et al.'s conjecture; studies slice of the corpus, records arXiv:2204.12683
      and arXiv:2501.00567)
      Every subcubic triangle-free graph avoiding F_14^(1), F_14^(2), F_11, F_22, F_19^(1), and F_19^(2) as subgraphs
      is fractionally 8/3-colorable.
    Definitions: [x287_bb_graph i] (X287.v) - the six graphs F_11, F_14^(1), F_14^(2), F_19^(1), F_19^(2), F_22 of
      arXiv:1911.12471's Figure 1, from wave X287; [has_subgraph G H] - G contains H as a (not necessarily induced)
      subgraph: an injective map from H to G sending edges to edges (GTBase common.v, host first); [triangle_free G] -
      no three pairwise adjacent vertices; [subcubic G] - every vertex has at most three neighbours (GTBase base.v);
      [bfold_colouring b f] - the supplied map f : G -> {set 'I_a} gives every vertex a b-element set of colours
      from the palette 'I_a and adjacent vertices disjoint sets, an (a:b)-fold colouring (GTBase bfold_colourings.v).
    Notes: encoded as stated.  "Fractionally 8/3-colorable" is the second of the equivalent conditions of
      arXiv:2204.12683v3 (aic-elevenfour.tex l.185-196): for some positive integers a and b with a/b <= 8/3, an
      assignment of b-element subsets of {1, ..., a} to the vertices, disjoint on every edge (l.191-193); here
      0 < b, a * 3 <= 8 * b (no division) and an (a:b)-fold colouring over 'I_a.  A vertex forces a >= b > 0, and a
      = 0 only for the empty graph, which is fractionally k-colourable for every k in both readings.  "Avoiding ...
      as subgraphs" is ordinary (not induced) containment; has_subgraph asks for an injective edge-preserving map, so
      it does not depend on how the six graphs' vertices are labelled.  Sources: the conjecture is Cames van
      Batenburg, Goedgebeur and Joret's, arXiv:1911.12471v2 (8 July 2020), Revision_IndependenceRatio8over3.tex
      l.2072-2076 ("containing none of ... as a subgraph.  Then, chi_f(G) <= 8/3"; l.2056-2063 define chi_f), restated
      word for word by Dvorak, Lidicky and Postle, arXiv:2204.12683v3 (last revised 28 March 2025), aic-elevenfour.tex
      l.246-250; l.244-245 there: it would imply the Heckman-Thomas conjecture (X270's row), the six graphs being
      non-planar (l.238).  The forbidden-subgraph hypothesis is needed: without it the statement fails at F_11, whose
      fractional chromatic number is 11/4 (l.260; [g310_not_trivially_true] in grounding_X310.v).  Status: pinned
      open; open in both deposited records (2204.12683v3 l.252: "the first step towards this conjecture", 11/4 when
      no component is F_14^(1) or F_14^(2), l.254-258); the third record, arXiv:2501.00567, is not read here, and a
      literature item follows if it changes the status (Lancelot's (789)). *)
Definition cames_van_batenburg_forbidden_subgraph_fractional_statement : Prop :=
  forall G : sgraph, triangle_free G -> subcubic G ->
    (forall i : 'I_6, ~ has_subgraph G (x287_bb_graph i)) ->
    exists (a b : nat) (f : G -> {set 'I_a}), [/\ 0 < b, bfold_colouring b f & a * 3 <= 8 * b].

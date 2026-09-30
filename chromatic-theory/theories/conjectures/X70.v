(** * Chromatic.conjectures.X70 -- v2 Scott-Seymour tournament row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X70 vocabulary ************************************************)

Definition x70_graph
    (V : finType) (E : rel V) (Esym : symmetric E) (Eirr : irreflexive E) :
    sgraph :=
  SGraph Esym Eirr.

Definition x70_tournament_rel (V : finType) (T : rel V) : Prop :=
  irreflexive T /\
  forall x y : V, x != y -> T x y = ~~ T y x.

(** ** X70 statements ******************************************************)

(** Corpus row: studies:std_scott_seymour_tournament_chi_boundedness_conject
    Site: none
    Review: none
    English statement: (Scott and Seymour, studies slice of the corpus)
      For every k there is a K such that whenever a tournament T and a simple graph G are given on
      the same finite vertex set and the chromatic number of G is at least K, some vertex v has the
      property that the subgraph of G induced on the out-neighbourhood of v in T has chromatic
      number at least k.
    Definitions: [x70_tournament_rel T] - T is irreflexive and, for distinct vertices, exactly one
      of T x y and T y x holds (this file); [x70_graph Esym Eirr] - packaging a symmetric
      irreflexive relation on a finType as an [sgraph] (this file); the out-neighbourhood of v is
      the vertex set [set u | T v u].
    Notes: This row has no site or review page in the corpus, hence the literal "none" above.
      Sharing the vertex set between the tournament and the graph is realised by quantifying over
      one finType V carrying both relations. The bound K depends on k only, as in the source. *)
Definition scott_seymour_tournament_outneighbourhood_chi_statement : Prop :=
  forall k : nat,
    exists K : nat,
      forall (V : finType) (T E : rel V)
             (Esym : symmetric E) (Eirr : irreflexive E),
        x70_tournament_rel T ->
        let G := x70_graph Esym Eirr in
        K <= χ([set: G]) ->
        exists v : G,
          k <= χ([set: induced [set u : G | T v u]]).

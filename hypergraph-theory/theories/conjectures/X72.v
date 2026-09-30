(** * Hypergraph.conjectures.X72 -- v2 Ryser cover-gap row *)

From GTBase Require Export base.
From Hypergraph.conjectures Require Import X6.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X72 vocabulary ************************************************)

Definition x72_intersecting (T : finType) (E : {set {set T}}) : Prop :=
  forall e f : {set T}, e \in E -> f \in E -> e :&: f != set0.

Definition x72_vertex_cover (T : finType) (E : {set {set T}}) (X : {set T})
  : Prop :=
  forall e : {set T}, e \in E -> ~~ [disjoint X & e].

Definition x72_transversal_number
    (T : finType) (E : {set {set T}}) (tau : nat) : Prop :=
  (exists X : {set T}, x72_vertex_cover E X /\ #|X| = tau) /\
  forall X : {set T}, x72_vertex_cover E X -> tau <= #|X|.

(** ** X72 statements ******************************************************)

(** Corpus row: studies:std_abu_khazneh_bar_t_pokrovskiy_szab_question_on_co
    Site: none
    Review: none
    English statement: (Abu-Khazneh, Barat, Pokrovskiy and Szabo, question on covers of
      intersecting r-partite hypergraphs)
      Is there a constant K such that for every r at least 1 there is an intersecting r-partite
      r-uniform hypergraph with at least one hyperedge whose cover number is at least r - K?
    Definitions: [x72_intersecting E] - any two hyperedges of E meet
      (hypergraph-theory/theories/conjectures/X72.v); [x72_vertex_cover E X] - the vertex set X
      meets every hyperedge (same file); [x72_transversal_number E tau] - tau is attained by
      some vertex cover and is a lower bound for the size of every vertex cover, i.e. tau is the
      cover number (same file); [x6_r_partite_uniform part E] - every hyperedge meets each of
      the r parts in exactly one vertex (hypergraph-theory/theories/conjectures/X6.v).
    Notes: the constant K is quantified before r, as in the source ("a constant K such that for
      every r").  The inequality tau >= r - K is stated without natural subtraction, as
      r <= tau + K.  The extra guard [E != set0] excludes the empty hypergraph, for which the
      intersecting condition is vacuous and tau = 0, which would make the statement trivially
      true with K = r.  [x72_vertex_cover] and [x72_transversal_number] duplicate the
      [hg_cover]/[is_cover_number] pair of U12.v (see meta/STATEMENT_IMPROVEMENTS.md). *)
Definition ryser_intersecting_partite_cover_gap_statement : Prop :=
  exists K : nat,
    forall r : nat,
      1 <= r ->
      exists (T : finType) (part : T -> 'I_r) (E : {set {set T}}) (tau : nat),
        [/\ E != set0,
            @x6_r_partite_uniform T r part E,
            x72_intersecting E,
            x72_transversal_number E tau
          & r <= tau + K].

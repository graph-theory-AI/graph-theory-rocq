(** * Digraph.conjectures.X123 -- v2 directed Gyarfas-Sumner (tournament + forest) row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented.
From Digraph.conjectures Require Import chi_bounded dichromatic heroes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X123 vocabulary ************************************************)

(** A transitive tournament: a tournament (irreflexive, semicomplete and
    asymmetric — [heroes.is_tournament]) whose arc relation is transitive, i.e.
    the strict order of a linear order (isomorphic to some [TT n]). *)
Definition x123_transitive_tournament (H : diGraphType) : Prop :=
  is_tournament H /\ transitive (arc : rel H).

(** The class forbidding BOTH [H] and [F] as induced subdigraphs, inside the
    oriented graphs — the pair {H,F} is the forbidden set (cf. [X71]'s
    single-forest [x71_oriented_forb_ind]). *)
Definition x123_forb_pair (H F D : diGraphType) : Prop :=
  chi_bounded.oriented_dg D /\ ind_free H D /\ ind_free F D.

(** ** X123 statements ******************************************************)

(** Corpus row: studies:std_directed_gy_rf_s_sumner_conjecture_aboulker_char
    Site: none
    Review: none
    English statement: (Aboulker, Charbit and Naserasr, directed Gyarfas-Sumner conjecture, tournament and forest case)
      For every transitive tournament H and every oriented forest F, the class of oriented
      graphs containing no induced copy of H and no induced copy of F has bounded dichromatic
      number: one constant dicolours every member.
    Definitions: [x123_transitive_tournament H] - a tournament (irreflexive, semicomplete,
      asymmetric) whose arc relation is transitive (this file); [x123_forb_pair H F D] - D is
      oriented and free of induced copies of both H and F (this file); [is_tournament] and
      [ind_free] (conjectures/heroes.v); [oriented_forest] and [oriented_dg]
      (conjectures/chi_bounded.v); [dichromatic_bounded C] - a single constant k dicolours every
      member of the class C (conjectures/dichromatic.v).
    Notes: chi-vec-finite of the source is the CONSTANT bound [dichromatic_bounded], not a
      function of the clique number; forbidding a transitive tournament bounds the directed
      clique number, which is what turns the function bound of
      [directed_gyarfas_sumner_oriented_forest_dichromatic_statement] (conjectures/X71.v) into a
      constant here. *)
Definition directed_gyarfas_sumner_tournament_forest_statement : Prop :=
  forall H F : diGraphType,
    x123_transitive_tournament H ->
    chi_bounded.oriented_dg F ->
    chi_bounded.oriented_forest F ->
    dichromatic_bounded (x123_forb_pair H F).

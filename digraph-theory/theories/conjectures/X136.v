(** * Digraph.conjectures.X136 -- v2 tournament Erdos-Hajnal row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph tournament.
From Digraph.conjectures Require Import heroes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Corpus row: studies:std_erd_s_hajnal_conjecture_for_tournaments
    Site: none
    Review: none
    English statement: (Erdos and Hajnal, Erdos-Hajnal conjecture for tournaments)
      For every tournament H there are positive naturals a and b such that every tournament G
      with no induced copy of H has a vertex set S inducing a transitive subtournament with #|G|
      ^ a <= #|S| ^ b, that is with at least |G| to the power a/b vertices.
    Definitions: [ind_free H G] - no induced copy of H (conjectures/heroes.v); [transb T] - the
      arc relation is transitive, i.e. the subtournament is transitive (core/tournament.v);
      [sub_tournament S] (core/tournament.v).
    Notes: The positive real exponent tau of the source is encoded as a positive rational a/b,
      cleared of division by raising both sides to integer powers. Any real exponent can be
      lowered to a rational one, so this is equivalent for the existence statement. *)
Definition erdos_hajnal_tournament_transitive_subtournament_statement : Prop :=
  forall H : tournament,
    exists a b : nat,
      [/\ 0 < a, 0 < b &
        forall G : tournament,
          ind_free (H : diGraphType) (G : diGraphType) ->
          exists S : {set G},
            #|G| ^ a <= #|S| ^ b /\
            transb (sub_tournament S)].


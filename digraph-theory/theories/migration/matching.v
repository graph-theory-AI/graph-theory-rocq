(** C24: the whole-graph matching representation of [Digraph.conjectures.path_fas], frozen
    at the fixed C23 pin a77d0b06239d7a78dd6cc0a209939ad935ac669b; the whole path_fas file is
    byte-identical at the C1 matching baseline 9e030727db115917ae077ac07a8fc6aa68661f73.
    - [Legacy.matching]: the raw local predicate on the ENTIRE graph (a forest whose vertices
      have at most one neighbour), not the new public alias; the live source now unfolds to
      [GTBase.matching_graphs.matching_graph G], the upstream [matching] of E(G).
    - [Legacy.has_matchingFAS]: the same witness F, its [is_FAS] (an arc set meeting every
      directed cycle) and the loop-guarded, orientation-erasing [farc_graph F].
    - [Legacy.matchingFAS_iff_dw1_statement]: the complete non-corpus Davot-Isenmann-Roy-
      Thiebaut iff with the exact [Delta_star] minimum and bound 1. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude interop_graph_theory digraph oriented dipath.
From Digraph Require Import tournament order.
From GTBase Require Import matching_graphs.
From Digraph.conjectures Require Import path_fas.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition matching (G : sgraph) : Prop :=
  is_forest [set: G] /\ (forall x : G, sdeg x <= 1).

Definition has_matchingFAS (T : tournament) : Prop :=
  exists F : {set T * T}, is_FAS F /\ Legacy.matching (farc_graph F).

Definition matchingFAS_iff_dw1_statement : Prop :=
  forall T : tournament, Legacy.has_matchingFAS T <-> (Delta_star T <= 1)%N.

End Legacy.

(** The raw conjunction is the public whole-graph view, by [matchingP]. *)
Lemma matching_compat (G : sgraph) : Legacy.matching G <-> matching G.
Proof. exact: iff_sym (matchingP G). Qed.

Lemma has_matchingFAS_compat (T : tournament) :
  Legacy.has_matchingFAS T <-> has_matchingFAS T.
Proof.
split=> -[F [fas m]]; exists F; split=> //.
- exact: (proj1 (matching_compat (farc_graph F)) m).
- exact: (proj2 (matching_compat (farc_graph F)) m).
Qed.

Lemma matchingFAS_iff_dw1_statement_compat :
  Legacy.matchingFAS_iff_dw1_statement <-> matchingFAS_iff_dw1_statement.
Proof.
split=> st T; split=> h.
- exact: (proj1 (st T) (proj2 (has_matchingFAS_compat T) h)).
- exact: (proj1 (has_matchingFAS_compat T) (proj2 (st T) h)).
- exact: (proj1 (st T) (proj1 (has_matchingFAS_compat T) h)).
- exact: (proj2 (has_matchingFAS_compat T) (proj2 (st T) h)).
Qed.

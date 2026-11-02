(** * Chromatic.conjectures.grounding_X279 -- grounding certificates for wave X279 (2026-11-02)

    For the one row, arxiv:2209.09107#00: hyp_inhabited (the three conditions of the body hold together at K_2,
    with the empty arc set, and the statement gives such an arc set there) and not_trivially_true (the body has no
    hypothesis to drop; it is false, by the triangle).  No local helper, so no helper_sanity.
    The row statement is kernel-equivalent to applications/alon_tarsi_triangle.v's [question_6_1_statement]
    ([g279_statement_iff]); [alon_tarsi_spanning_orientation_half_degree_disproved] is the theorem of the formal
    resolution 2209.09107__00 (meta/formal_resolutions.json), through that file's [question_6_1_disproved]. *)

From GTBase Require Import base.
From Chromatic.foundations Require Import alon_tarsi.
From Chromatic.applications Require Import alon_tarsi_triangle.
From Chromatic.conjectures Require Import X279.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The applications encoding and the disproof ************************************************ *)

(* N(v) is coq-graph-theory's open neighbourhood, the applications file's [set y | v -- y] *)
Lemma g279_neigh (G : sgraph) (v : G) : #|N(v)| = #|[set y : G | v -- y]|.
Proof. by []. Qed.

(* the row statement is the applications file's question_6_1_statement, stated with Prop connectives *)
Lemma g279_statement_iff :
  alon_tarsi_spanning_orientation_half_degree_statement <-> question_6_1_statement.
Proof.
split=> h G.
- have [A [h1 h2 h3]] := h G; exists A; split; last split.
  + apply/forallP=> x; apply/forallP=> y; apply/implyP=> xy.
    by have [e n] := h1 x y xy; rewrite e n.
  + exact: h2.
  + by apply/forallP=> x; rewrite -g279_neigh; exact: h3 x.
- have [A [h1 [h2 h3]]] := h G; exists A; split => //.
  + move=> x y xy; move/forallP/(_ x)/forallP/(_ y)/implyP/(_ xy): h1 => /andP [e n].
    by split.
  + by move=> v; rewrite g279_neigh; exact: (forallP h3 v).
Qed.

(** The formal resolution's theorem (record 2209.09107__00, direction disprove): the triangle. *)
Theorem alon_tarsi_spanning_orientation_half_degree_disproved :
  ~ alon_tarsi_spanning_orientation_half_degree_statement.
Proof. by move/g279_statement_iff; exact: question_6_1_disproved. Qed.

(** ** arxiv:2209.09107#00 ********************************************************************** *)

(** hyp_inhabited: the three conditions of the body hold together at K_2 with the empty arc set (no arc, the empty
    set Alon-Tarsi by [at_empty_alon_tarsi], and degree 1 <= 2 * 0 + 1: the unfloored bound is 0 there), and the
    statement gives such an arc set at K_2. *)
Definition g279_hyp_claim : Prop :=
  (exists A : {set 'K_2 * 'K_2},
     [/\ forall (x y : 'K_2), (x, y) \in A -> x -- y /\ (y, x) \notin A,
         at_alon_tarsi A &
         forall (v : 'K_2), #|N(v)| <= (2 * at_outdegree A v).+1]) /\
  (alon_tarsi_spanning_orientation_half_degree_statement ->
     exists A : {set 'K_2 * 'K_2},
       [/\ forall (x y : 'K_2), (x, y) \in A -> x -- y /\ (y, x) \notin A,
           at_alon_tarsi A &
           forall (v : 'K_2), #|N(v)| <= (2 * at_outdegree A v).+1]).

Theorem g279_hyp_inhabited : g279_hyp_claim.
Proof.
split; last by move=> S; exact: S 'K_2.
exists set0; split.
- by move=> x y; rewrite inE.
- exact: at_empty_alon_tarsi.
- move=> v.
  have -> : at_outdegree (set0 : {set 'K_2 * 'K_2}) v = 0.
    by rewrite /at_outdegree; apply/eqP; rewrite cards_eq0; apply/eqP/setP => w; rewrite !inE.
  rewrite muln0; apply: (leq_trans (subset_leq_card (_ : N(v) \subset [set~ v]))).
    by apply/subsetP => y; rewrite !inE; apply: contraTneq => ->; rewrite sg_irrefl.
  by rewrite cardsC1 card_ord.
Qed.

(** not_trivially_true: the body has no hypothesis to drop; it is false (the triangle), so it is not trivially
    true. *)
Definition g279_ntt_claim : Prop := ~ alon_tarsi_spanning_orientation_half_degree_statement.

Theorem g279_not_trivially_true : g279_ntt_claim.
Proof. exact: alon_tarsi_spanning_orientation_half_degree_disproved. Qed.

Print Assumptions alon_tarsi_spanning_orientation_half_degree_statement.
Print Assumptions g279_statement_iff.
Print Assumptions alon_tarsi_spanning_orientation_half_degree_disproved.
Print Assumptions g279_hyp_inhabited.
Print Assumptions g279_not_trivially_true.

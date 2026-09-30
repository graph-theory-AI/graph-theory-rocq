(** Question 6.1 in arXiv:2209.09107v2, exactly with its unfloored bound. *)
From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph.
From Chromatic.foundations Require Import alon_tarsi.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The chosen arc set orients a spanning subgraph: arcs follow edges of G,
    and an edge cannot be used in both directions. Isolated vertices remain. *)
Definition at_spanning_orientation (G : sgraph) (A : {set G * G}) :=
  [forall x, [forall y,
    ((x, y) \in A) ==> ((x -- y) && ((y, x) \notin A))]].

(** Exact integer form of outdegree >= (degree_G - 1)/2.
    Writing degree_G <= 2*outdegree+1 avoids truncated subtraction. *)
Definition at_degree_bound (G : sgraph) (A : {set G * G}) :=
  [forall x, #|[set y : G | x -- y]| <= (2 * at_outdegree A x).+1].

(** No corpus row: applications-local encoding of Question 6.1 of arXiv:2209.09107v2, stated
    here with its unfloored bound so that it can be REFUTED below by the triangle (see
    [question_6_1_disproved] in this file). The corpus does contain a row for this question,
    arxiv:2209.09107#00, but that row registers no formal_name and its statement leg is still
    todo, so the gate cannot link this definition to it; the row's page is
    https://graph-theory-ai.github.io/graph-conjectures/arxiv/2209.09107__00/ *)
Definition question_6_1_statement : Prop :=
  forall G : sgraph, exists A : {set G * G},
    at_spanning_orientation A /\ at_alon_tarsi A /\ at_degree_bound A.

Definition at_triangle_rel (x y : 'I_3) := x != y.
Lemma at_triangle_sym : symmetric at_triangle_rel.
Proof. by move=> x y; rewrite /at_triangle_rel eq_sym. Qed.
Lemma at_triangle_irrefl : irreflexive at_triangle_rel.
Proof. by move=> x; rewrite /at_triangle_rel eqxx. Qed.
Definition at_triangle : sgraph := SGraph at_triangle_sym at_triangle_irrefl.

Lemma at_triangle_degree (x : at_triangle) :
  #|[set y : at_triangle | x -- y]| = 2.
Proof.
have -> : [set y : at_triangle | x -- y] = [set~ x].
  by apply/setP=> y; rewrite !inE /= /at_triangle_rel eq_sym.
by rewrite cardsC1 card_ord.
Qed.

Definition at_v0 : at_triangle := ord0.
Definition at_v1 : at_triangle := @Ordinal 3 1 isT.
Definition at_v2 : at_triangle := @Ordinal 3 2 isT.
Lemma at_triangle_enum : enum at_triangle = [:: at_v0; at_v1; at_v2].
Proof.
apply: (inj_map val_inj).
by rewrite val_enum_ord.
Qed.
Lemma at_triangle_cases (x : at_triangle) :
  x = at_v0 \/ x = at_v1 \/ x = at_v2.
Proof.
have hx : x \in [:: at_v0; at_v1; at_v2] by rewrite -at_triangle_enum mem_enum.
move: hx; rewrite !inE=> /or3P[/eqP ->|/eqP ->|/eqP ->]; tauto.
Qed.
Lemma at_triangle_forall (P : pred at_triangle) :
  [forall x, P x] = [&& P at_v0, P at_v1 & P at_v2].
Proof.
apply/forallP/and3P=> [h|[h0 h1 h2] x]; first by repeat split; exact: h.
by case: (at_triangle_cases x)=> [->|[->|->]].
Qed.
Lemma at_triangle_card (P : pred at_triangle) :
  #|P| = P at_v0 + P at_v1 + P at_v2.
Proof.
rewrite cardE /enum_mem -enumT at_triangle_enum size_filter /=.
by rewrite addn0 addnA.
Qed.
Lemma at_triangle_set_card (P : pred at_triangle) :
  #|[set x | P x]| = P at_v0 + P at_v1 + P at_v2.
Proof. by rewrite cardsE at_triangle_card. Qed.
Lemma at_triangle_pair_enum :
  enum [the finType of (at_triangle * at_triangle)%type] =
  [:: (at_v0,at_v0); (at_v0,at_v1); (at_v0,at_v2);
      (at_v1,at_v0); (at_v1,at_v1); (at_v1,at_v2);
      (at_v2,at_v0); (at_v2,at_v1); (at_v2,at_v2)].
Proof.
rewrite enumT unlock.
change (@prod_enum at_triangle at_triangle =
  [:: (at_v0,at_v0); (at_v0,at_v1); (at_v0,at_v2);
      (at_v1,at_v0); (at_v1,at_v1); (at_v1,at_v2);
      (at_v2,at_v0); (at_v2,at_v1); (at_v2,at_v2)]).
by rewrite /prod_enum at_triangle_enum.
Qed.
Lemma at_triangle_arc_card (A : {set at_triangle * at_triangle}) :
  #|A| = ((at_v0,at_v0) \in A) + ((at_v0,at_v1) \in A) + ((at_v0,at_v2) \in A) +
         ((at_v1,at_v0) \in A) + ((at_v1,at_v1) \in A) + ((at_v1,at_v2) \in A) +
         ((at_v2,at_v0) \in A) + ((at_v2,at_v1) \in A) + ((at_v2,at_v2) \in A).
Proof.
rewrite cardE /enum_mem -enumT at_triangle_pair_enum size_filter /=.
by rewrite addn0 !addnA.
Qed.

Lemma at_triangle_balance (A : {set at_triangle * at_triangle}) :
  at_spanning_orientation A -> at_degree_bound A ->
  at_eulerian A /\ odd #|A|.
Proof.
rewrite /at_spanning_orientation /at_degree_bound /at_eulerian
  !at_triangle_forall !at_triangle_degree.
rewrite /at_outdegree /at_indegree !at_triangle_set_card at_triangle_arc_card /=.
case: ((at_v0,at_v0) \in A); first by [].
case: ((at_v1,at_v1) \in A); first by rewrite /= !andbF.
case: ((at_v2,at_v2) \in A); first by rewrite /= !andbF.
by case: ((at_v0,at_v1) \in A); case: ((at_v0,at_v2) \in A);
   case: ((at_v1,at_v0) \in A); case: ((at_v1,at_v2) \in A);
   case: ((at_v2,at_v0) \in A); case: ((at_v2,at_v1) \in A).
Qed.

Theorem question_6_1_disproved : ~ question_6_1_statement.
Proof.
move=> /(_ at_triangle) [A [ho [hAT hd]]].
have [he hodd] := at_triangle_balance ho hd.
by move: (at_odd_eulerian_not_alon_tarsi he hodd); rewrite hAT.
Qed.

Print Assumptions question_6_1_disproved.

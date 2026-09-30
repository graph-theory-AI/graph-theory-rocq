(** * Chromatic.conjectures.X192 -- v2 triangle-free additive approximation row *)

From GraphTheory Require Import minor.
From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X192 vocabulary ***********************************************)

Definition x192_proper_minor_closed_class (C : sgraph -> Prop) : Prop :=
  exists H : sgraph, forall G : sgraph, C G -> ~ minor G H.

Definition x192_triangle_free (G : sgraph) : Prop := girth_geq G 4.

Definition x192_additive_chromatic_output
    (alpha : nat) (G : sgraph) (out : data) : Prop :=
  χ([set: G]) <= data_nat_value out /\
  data_nat_value out <= χ([set: G]) + alpha.

Definition x192_polytime_additive_chromatic_approx
    (C : sgraph -> Prop) (alpha : nat) : Prop :=
  polytime_outputs_graph_on
    (fun G : sgraph => C G /\ x192_triangle_free G)
    (x192_additive_chromatic_output alpha).

(** ** X192 statements *****************************************************)

(** Corpus row: arxiv:1707.03888#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1707.03888__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1707.03888__00.json
    English statement: (Dvorak and Kawarabayashi 2017, open question, arXiv:1707.03888)
      There is a natural alpha such that for every proper minor-closed class of graphs there is a
      polynomial-time algorithm computing, for every triangle-free graph in the class, a number
      between chi(G) and chi(G) + alpha; that is, the chromatic number of triangle-free graphs in
      any proper minor-closed class can be approximated in polynomial time within a universal
      additive error.
    Definitions: [x192_proper_minor_closed_class C] - some graph H is a minor of no member of C
      (this file); [x192_triangle_free G] - girth at least 4 (this file);
      [x192_additive_chromatic_output alpha G out] - the decoded output lies between chi(G) and
      chi(G) + alpha (this file); [x192_polytime_additive_chromatic_approx C alpha] -
      [polytime_outputs_graph_on] for that specification on the triangle-free members of C (this
      file); [polytime_outputs_graph_on], [data_nat_value] (GTBase base/theories/complexity.v);
      [minor] (coq-graph-theory minor.v).
    Notes: The corpus row is a QUESTION; the Rocq body is its affirmative reading. The quantifier
      order matters and follows the source: the additive error alpha is uniform, chosen before the
      class. Minor-closedness itself is not asserted, only properness in the form of a forbidden
      minor, which is what the statement uses. The row was retargeted in 2026-07-16 from a blocked
      placeholder, see meta/BLOCKED_RETARGETING_FOUNDATIONS.md. *)
Definition triangle_free_minor_closed_chromatic_additive_approx_statement : Prop :=
  exists alpha : nat,
    forall C : sgraph -> Prop,
      x192_proper_minor_closed_class C ->
      x192_polytime_additive_chromatic_approx C alpha.

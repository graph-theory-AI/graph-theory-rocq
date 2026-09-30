(** * Minor.conjectures.implications_X5 — corpus-relation edges landing in X5

    Edges of [meta/corpus_relations.json] whose TARGET is an X5 row.  Axiom-free:
    only [Qed]-closed results live here.

    e045.  [min_degree_six_max_degree_eight_k6_minor_statement] ⟹
    [six_regular_has_k6_minor_statement].  Pure hypothesis-class containment: a
    6-regular graph has every degree equal to 6, hence minimum degree at least 6
    and maximum degree [Delta G = 6 <= 8], so it lies in the hypothesis class of
    the source row, whose conclusion is verbatim the target's. *)

From GTBase Require Import base.
From GraphTheory Require Import minor.
From Minor.conjectures Require Import X5.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** e045 *****************************************************************)

(** A [d]-regular nonempty graph has maximum degree exactly [d]. *)
Lemma Delta_regular (G : sgraph) (d : nat) :
  0 < #|G| -> regular G d -> Delta G = d.
Proof.
move=> G0 reg; have [x0 Hx0] := eq_bigmax (fun x : G => #|N(x)|) G0.
by rewrite /Delta Hx0 reg.
Qed.

Theorem min_degree_six_max_degree_eight_k6_minor_implies_six_regular_has_k6_minor :
  min_degree_six_max_degree_eight_k6_minor_statement ->
  six_regular_has_k6_minor_statement.
Proof.
move=> src G G0 reg; apply: src => // [v|].
- by rewrite reg.
- by rewrite (Delta_regular G0 reg).
Qed.

(*@EDGE from=min_degree_six_max_degree_eight_k6_minor_statement to=six_regular_has_k6_minor_statement kind=implies status=verified proved=true proof=min_degree_six_max_degree_eight_k6_minor_implies_six_regular_has_k6_minor cite="gc:e045" note="Hypothesis-class containment: a nonempty 6-regular graph has every degree equal to 6, hence minimum degree at least 6 and Delta G = 6 <= 8 (Delta_regular, proved here from eq_bigmax), so the source row applies verbatim and its conclusion is the target's." *)

Print Assumptions Delta_regular.
Print Assumptions min_degree_six_max_degree_eight_k6_minor_implies_six_regular_has_k6_minor.

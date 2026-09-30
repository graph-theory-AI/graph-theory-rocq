(** * GTMisc.conjectures.X110 -- v2 guarded Chen-Chvatal row *)

From mathcomp Require Import all_boot.
From GTMisc.conjectures Require Import X55.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X110 statements *****************************************************)

(** Corpus row: studies:std_chen_chv_tal_conjecture_146
    Site: none
    Review: none
    English statement: (Chen and Chvatal, Chen-Chvatal conjecture, canonical n >= 2 form)
      For every finite metric space (V, d) with at least two points, either there are two
      distinct points whose line is all of V (a universal line), or the space has at least |V|
      distinct lines.
    Definitions: [x55_metric d], [x55_between], [x55_line d a b], [x55_universal_line d],
      [x55_lines d] - the metric-line vocabulary, reused verbatim from
      graph-theory-misc/theories/conjectures/X55.v: a natural-valued metric, metric collinearity
      of three points, the line through two points, the existence of a line equal to the whole
      space, and the set of all lines through two distinct points.
    Notes: this row states the same conjecture as the corpus row of
      graph-theory-misc/theories/conjectures/X55.v; the two Rocq bodies are identical, the
      n >= 2 guard being already present there.  Recorded in
      meta/STATEMENT_IMPROVEMENTS.md as a duplicate encoding. *)
Definition chen_chvatal_guarded_metric_lines_statement : Prop :=
  forall (V : finType) (d : V -> V -> nat),
    (2 <= #|V|)%N ->
    x55_metric d ->
    x55_universal_line d \/ #|V| <= #|x55_lines d|.

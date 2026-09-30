(** * GTMisc.conjectures.X55 -- v2 Chen-Chvatal metric-line row *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X55 vocabulary ************************************************)

Definition x55_metric (V : finType) (d : V -> V -> nat) : Prop :=
  (forall x y : V, d x y = 0 <-> x = y) /\
  (forall x y : V, d x y = d y x) /\
  forall x y z : V, d x z <= d x y + d y z.

Definition x55_between (V : finType) (d : V -> V -> nat) (a b x : V) : bool :=
  (d a b == d a x + d x b) ||
  (d a x == d a b + d b x) ||
  (d b x == d b a + d a x).

Definition x55_line (V : finType) (d : V -> V -> nat) (a b : V) : {set V} :=
  [set x : V | x55_between d a b x].

Definition x55_universal_line (V : finType) (d : V -> V -> nat) : Prop :=
  exists a b : V, a != b /\ x55_line d a b = [set: V].

Definition x55_lines (V : finType) (d : V -> V -> nat) : {set {set V}} :=
  [set L : {set V} |
      [exists a : V, [exists b : V, (a != b) && (L == x55_line d a b)]]].

(** ** X55 statements ******************************************************)

(** Corpus row: studies:std_chen_chv_tal_conjecture
    Site: none
    Review: none
    English statement: (Chen and Chvatal, Chen-Chvatal conjecture)
      For every finite metric space (V, d) with at least two points, either there are two
      distinct points a, b whose line is all of V (a universal line), or the number of distinct
      lines of the space is at least |V|.
    Definitions: [x55_metric d] - d is a metric on the finite type V: d x y = 0 exactly when
      x = y, d is symmetric, and d satisfies the triangle inequality (this file);
      [x55_between d a b x] - x is collinear with a and b, i.e. one of the three points lies
      between the other two in the metric sense (this file); [x55_line d a b] - the set of
      points collinear with a and b (this file); [x55_universal_line d] - some line through two
      distinct points is the whole space (this file); [x55_lines d] - the set of all lines
      through two distinct points (this file).
    Notes: distances are natural numbers, so the statement is about integer-valued finite
      metric spaces rather than arbitrary real ones; this is the usual formalization choice for
      the combinatorial content of the conjecture.  Lines are collected as a set of vertex
      sets, so two coinciding lines are counted once, as required.
      graph-theory-misc/theories/conjectures/X110.v carries a second corpus row with a
      byte-identical body. *)
Definition chen_chvatal_metric_lines_statement : Prop :=
  forall (V : finType) (d : V -> V -> nat),
    (2 <= #|V|)%N ->
    x55_metric d ->
    x55_universal_line d \/ #|V| <= #|x55_lines d|.

(** Witness hint (second-reader re-read after the bridgeless/simple_mgraph
    repair, 2026-09-23): an axiom-free REFUTATION of
    [Cycle.conjectures.X212.orientable_five_cycle_double_cover_statement]
    (corpus row bm:bm-026, the orientable five cycle double cover conjecture,
    status `open`).

    This is NOT the defect that was repaired.  [bridgeless] is now the textbook
    cut-edge notion and [two_edge_connected] is now genuine 2-edge-connectivity;
    the row survives a SECOND, independent bug in the shared degree layer.

    [connectivity.mdeg]/[connectivity.subdeg] count the edges INCIDENT to a
    vertex ([#|edges_at v :&: H|]), so a LOOP contributes 1, not 2.  In every
    standard convention a loop contributes 2 to the degree, which is what makes
    a loop a cycle: a single loop is an element of the cycle space and a circuit
    of length 1.  Under the encoding it is neither -- [U6.even_subgraph [set e]]
    and [U6.is_circuit [set e]] both fail on it, because [subdeg [set e] v = 1]
    is odd and is neither 0 nor 2.

    The one-vertex, one-loop multigraph [Lp] below is connected and bridgeless
    (a loop is never a cut edge, [connectivity.loop_not_bridge]), hence
    [two_edge_connected]; but its only edge must lie in exactly two of the five
    members of the cover, and any member containing it equals [[set: edge Lp]],
    which is not an [even_subgraph].  So the conclusion is unsatisfiable and the
    statement is false -- while the conjecture itself plainly holds there
    (cover the loop twice).

    The SAME graph refutes [U6.cycle_double_cover_statement], a committed `done`
    OPG row, through [is_circuit] instead of [even_subgraph]; that proof is
    recorded in meta/X211-X229_faithfulness_audit.md (section "Re-read after the
    bridgeless/simple_mgraph repair").  Rows guarded by [loopless] --
    [small_cycle_double_cover_statement] (via [simple_mgraph]) and the [U10]
    [cubic_bridgeless] rows (via [cubic]) -- are NOT affected.

    Repair: make [mdeg]/[subdeg] count a loop twice (the textbook degree), or
    add a [loopless] hypothesis to the affected rows.  This hint must STOP
    compiling once that is done.

    STALE BY DESIGN since the loop-degree repair of 2026-09-23 (main session):
    [Cycle.foundations.connectivity.subdeg] now counts ARC ENDS
    ([#|ends_at H false v| + #|ends_at H true v|]), so the loop of [Lp] has the
    textbook degree 2 and [subdeg_full_Lp] below -- which asserts 1 -- no longer
    holds.  The file is KEPT UNCHANGED apart from this note, and must keep
    failing to compile: `python3 meta/vacuity_probe.py --names orientable_five_cycle_double_cover_statement`
    reports `hint-stale-FIX-OK`, which is the fix-verification signal.  The
    conclusion the old convention made unsatisfiable is now EXHIBITED on this
    very graph: [Cycle.conjectures.grounding_X212.x212_orientable_5_Lp] is a five-member
    orientable even double cover of [Lp].
    See meta/STATEMENT_IMPROVEMENTS.md, section "Loop degree: `subdeg` now
    counts arc ends (2026-09-23)". *)

From GraphTheory Require Import mgraph.
From GTBase Require Import base.
From Cycle.foundations Require Import connectivity.
From Cycle.conjectures Require Import U6 grounding_U6 X212.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* One vertex, one LOOP. *)
Definition Lp : mgraph := mgraph.add_edge U tt tt tt.

Lemma card_Lp : #|Lp| = 1.
Proof. by rewrite card_unit. Qed.

Lemma card_edge_Lp : #|edge Lp| = 1.
Proof. by rewrite /Lp /U card_option card_void. Qed.

Lemma edge_Lp_eq (e : edge Lp) : e = None.
Proof. by case: e => [[]|]. Qed.

Lemma src_Lp (e : edge Lp) : source e = tt. Proof. by case: (source e). Qed.
Lemma tgt_Lp (e : edge Lp) : target e = tt. Proof. by case: (target e). Qed.

Lemma mconnected_Lp : mconnected Lp.
Proof. by move=> [] []; exists [::]. Qed.

Lemma bridgeless_Lp : bridgeless Lp.
Proof. by move=> e; apply: loop_not_bridge; rewrite src_Lp tgt_Lp. Qed.

Lemma two_edge_connected_Lp : two_edge_connected Lp.
Proof. by split; [exact: mconnected_Lp | exact: bridgeless_Lp]. Qed.

(* The loop is incident to the unique vertex, so [subdeg [set e] v = 1] is ODD:
   the single-loop edge set is NOT an [even_subgraph] and NOT a [is_circuit]. *)
Lemma subdeg_full_Lp (v : Lp) : subdeg [set: edge Lp] v = 1.
Proof.
rewrite /subdeg setIT -card_edge_Lp; apply: eq_card => e.
by rewrite inE /incident; apply/existsP; exists false; case: (source e).
Qed.

Lemma not_even_subgraph_Lp (C : {set edge Lp}) :
  (None : edge Lp) \in C -> ~ even_subgraph C.
Proof.
move=> hC ev; have := ev tt.
suff -> : subdeg C tt = 1 by [].
rewrite -[C](_ : [set: edge Lp] = C); first exact: subdeg_full_Lp.
by apply/setP => e; rewrite inE [e]edge_Lp_eq hC.
Qed.

Lemma subdeg_C_Lp (C : {set edge Lp}) : (None : edge Lp) \in C -> subdeg C tt = 1.
Proof.
move=> hC; rewrite -[C](_ : [set: edge Lp] = C); first exact: subdeg_full_Lp.
by apply/setP => e; rewrite inE [e]edge_Lp_eq hC.
Qed.

(* bm-026 : REFUTED *)
Lemma refuted_orientable5 : ~ orientable_five_cycle_double_cover_statement.
Proof.
move=> H; have v1 : (0 < #|Lp|)%N by rewrite card_Lp.
move: H => H; have [C [d [ev _ cov _]]] := H Lp v1 two_edge_connected_Lp.
have : 0 < #|[set i : 'I_5 | (None : edge Lp) \in C i]| by rewrite cov.
case/card_gt0P => i; rewrite inE => hi.
by have := ev i tt; rewrite (subdeg_C_Lp hi).
Qed.

Print Assumptions refuted_orientable5.

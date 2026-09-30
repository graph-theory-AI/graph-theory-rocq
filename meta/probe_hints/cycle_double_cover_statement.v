(** Witness hint (second-reader re-read after the bridgeless/simple_mgraph
    repair, 2026-09-23): an axiom-free REFUTATION of
    [Cycle.conjectures.U6.cycle_double_cover_statement] (corpus row
    opg:cycle_double_cover_conjecture, the Cycle Double Cover Conjecture,
    statement leg `done`).

    This is NOT the bridgeless defect, which is repaired: [bridgeless] is the
    textbook cut-edge notion.  The row survives a SECOND, independent bug in the
    shared degree layer.

    [connectivity.mdeg]/[connectivity.subdeg] counted the edges INCIDENT to a
    vertex ([#|edges_at v :&: H|]), so a LOOP contributed 1, not 2.  In every
    standard convention a loop contributes 2 to the degree, which is exactly
    what makes a loop a cycle: a single loop is a circuit of length 1 and an
    element of the cycle space.  Under that encoding it was neither, so
    [U6.is_circuit [set e]] failed on it ([subgraph_kregular _ 2] wants 0 or 2,
    and got 1).

    The one-vertex, one-loop multigraph [Lp] below is [mconnected] and
    [bridgeless] (a loop is never a cut edge, [connectivity.loop_not_bridge]).
    Its single edge must be covered twice, and every candidate member containing
    it equals [[set: edge Lp]], whose [subdeg] at the unique vertex was 1 -- so
    no member was a circuit and the conclusion was unsatisfiable, although the
    conjecture plainly holds there (cover the loop twice).

    Sibling hint: meta/probe_hints/orientable_five_cycle_double_cover_statement.v
    refutes [X212.orientable_five_cycle_double_cover_statement] with the SAME
    graph, through [even_subgraph] instead of [is_circuit].

    This hint must STOP compiling once [mdeg]/[subdeg] count a loop twice.  See
    meta/X211-X229_faithfulness_audit.md, section "Re-read after the
    bridgeless/simple_mgraph repair".

    STALE BY DESIGN since the loop-degree repair of 2026-09-23 (main session):
    [Cycle.foundations.connectivity.subdeg] now counts ARC ENDS
    ([#|ends_at H false v| + #|ends_at H true v|]), so the loop of [Lp] has the
    textbook degree 2 and [subdeg_full_Lp] below -- which asserts 1 -- no longer
    holds.  The file is KEPT UNCHANGED apart from this note, and must keep
    failing to compile: `python3 meta/vacuity_probe.py --names cycle_double_cover_statement`
    reports `hint-stale-FIX-OK`, which is the fix-verification signal.  The
    conclusion the old convention made unsatisfiable is now EXHIBITED on this
    very graph: [Cycle.conjectures.grounding_U6.cdc_Gloop] (equally
    [grounding_X212.x212_cdc_Lp]) is a cycle double cover of [Lp].
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

Lemma subdeg_full_Lp (v : Lp) : subdeg [set: edge Lp] v = 1.
Proof.
rewrite /subdeg setIT -card_edge_Lp; apply: eq_card => e.
by rewrite inE /incident; apply/existsP; exists false; case: (source e).
Qed.

Lemma subdeg_C_Lp (C : {set edge Lp}) : (None : edge Lp) \in C -> subdeg C tt = 1.
Proof.
move=> hC; rewrite -[C](_ : [set: edge Lp] = C); first exact: subdeg_full_Lp.
by apply/setP => e; rewrite inE [e]edge_Lp_eq hC.
Qed.

(* The Cycle Double Cover Conjecture as encoded : REFUTED *)
Lemma refuted_cdc : ~ cycle_double_cover_statement.
Proof.
move=> H.
have v1 : (0 < #|Lp|)%N by rewrite card_Lp.
have e1 : (0 < #|edge Lp|)%N by rewrite card_edge_Lp.
have [L [circ cnt]] := H Lp v1 e1 bridgeless_Lp.
have : 0 < count (fun C : {set edge Lp} => (None : edge Lp) \in C) L by rewrite cnt.
rewrite -has_count => /hasP[C CL hC].
have [_ reg _] := circ C CL.
by have := reg tt; rewrite (subdeg_C_Lp hC); case.
Qed.

Print Assumptions refuted_cdc.

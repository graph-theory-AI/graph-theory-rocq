(** Curated refutation witness (second-reader readback, 2026-09-23).
    Condition (ii) of X219's Conjecture-7 encoding has no lower guard on the
    maximum degrees: with DA = DB = 1 the hypotheses [C * trunc_log 2 1 <= kA]
    and [C * trunc_log 2 1 <= kB] read [0 <= kA], [0 <= kB], so the body claims
    that every bipartite graph of maximum degree one is (1,1)-choosable.  A
    single edge whose two lists are the same one-element palette refutes it.
    This file must STOP compiling once the row is repaired (a Delta_0 threshold
    or a [2 <= DA], [2 <= DB] guard in (ii)). *)

From GTBase Require Export base.
From Chromatic.conjectures Require Import X219.

Set Implicit Arguments.

Lemma refuted : ~ asymmetric_bipartite_list_colouring_statement.
Proof.
case=> _ [] [C [_ Hii]] _.
have deg : forall x : complete 2, #|N(x)| <= 1.
  move=> x; have -> : N(x) = [set~ x].
    by apply/setP => y; rewrite !inE /edge_rel /= eq_sym.
  by rewrite cardsC1 card_ord.
have bip : x219_bipartition [set (ord0 : complete 2)].
  move=> u v; rewrite /edge_rel /= !inE.
  by case: u => -[|[|u]] hu //=; case: v => -[|[|v]] hv //=.
have H := Hii (complete 2) [set (ord0 : complete 2)] 1 1 1 1 bip
            (fun v _ => deg v) (fun v _ => deg v) isT isT.
have tl : C * trunc_log 2 1 <= 1 by rewrite muln0.
have cu : 1 <= #|[set: unit]| by apply/card_gt0P; exists tt; rewrite inE.
have [f [fL fP]] := H tl tl unit (fun _ => [set: unit])
                      (fun v _ => cu) (fun v _ => cu).
have adj : (ord0 : complete 2) -- (Ordinal (isT : 1 < 2)).
  by rewrite /edge_rel /=.
by move: (fP _ _ adj); case: (f ord0); case: (f (Ordinal (isT : 1 < 2))).
Qed.

Print Assumptions refuted.

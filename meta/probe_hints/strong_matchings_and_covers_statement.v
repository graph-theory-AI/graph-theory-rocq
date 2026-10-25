(** Witness hint (Any-lane guard, 2026-10-25): an axiom-free REFUTATION of
    [Infinite.conjectures.D4inf4.strong_matchings_and_covers_statement] as encoded before its
    nonempty-edge guard (corpus row opg:strong_matchings_and_covers).

    [iHypergraph] does not forbid an edge with no vertex.  Such an edge has at most k vertices
    for EVERY k (the covering map from 'I_k has nothing to cover), and no vertex set meets it, so
    [hcover] fails and no strongly minimal cover exists.  The one-edge hypergraph below refutes
    the body at k = 1, which also shows that a guard [1 <= k] would not repair it; hypergraph
    edges are nonempty in the source.  With the guard [forall e, exists v, hinc e v] this file
    no longer compiles (hint-stale-FIX-OK). *)
From mathcomp Require Import all_boot.
From Infinite.conjectures Require Import D4inf4.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition empty_edge : iHypergraph := @Build_iHypergraph unit unit (fun _ _ => False).

Lemma refuted : ~ strong_matchings_and_covers_statement.
Proof.
move=> /(_ empty_edge 1) [].
  by move=> e; exists (fun _ => tt) => v [].
by move=> _ [X [/(_ tt) [v [_ []]] _]].
Qed.

Print Assumptions refuted.

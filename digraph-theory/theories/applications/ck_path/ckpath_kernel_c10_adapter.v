(** * Adapter from the CK a=2 kernel to the C10 hand interface *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import
  prelude digraph oriented dipath lemma7 ckpath_kernel_cases ckpath_c10_hand.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Exactly the prefix, gateway, and closure data consumed by
    [ckpath_c10_hand]. *)
Record ckpath_c10_prefix_data (D : orientedDigraph) (c : seq D)
    (S : {set D}) (v0 v1 : D) : Prop := C10PrefixData {
  c10_prefix_v0_outside : v0 \in c10_outside c;
  c10_prefix_v1_outside : v1 \in c10_outside c;
  c10_prefix_distinct : v0 != v1;
  c10_prefix_arc : v0 --> v1;
  c10_prefix_next : forall s, s \in S -> v1 --> next c s;
  c10_prefix_S_subset : S \subset c10_cycle_set c;
  c10_prefix_S_closed :
    forall s z, s \in S -> s --> z -> z \in c10_cycle_set c
}.

(** At [a=2], the CK path decomposes as [v0 :: v1 :: c].  Uniqueness
    places the two prefix vertices outside [c], while
    [S = prev_c(B)] and [v1 -> B] give [v1 -> next_c(S)]. *)
Theorem ckpath_kernel_c10_adapter (D : orientedDigraph) (x : D) (p : seq D) :
  ckpath_kernel_facts 6 x p 2 ->
  ckpath_c10_prefix_data (ckC x p 2) (ckS x p 2)
    x (nth x (x :: p) 1).
Proof.
case: p => [|y t] /=.
- move=> [_ _ [[_ hsize _ hlen] _ _ _ _]].
  exfalso.
  move: hlen.
  by rewrite -hsize.
move=> [_ _ [[hp _ _ _] [dc _ _] _ hclose _]].
have up := dipath_uniq hp.
move: up; rewrite /= => /and3P[xNyt yNt ut].
have /andP[xDy xNt] : (x != y) && (x \notin t).
  by move: xNyt; rewrite !inE negb_or.
have [axy _] := dipath_cons hp.
constructor.
- rewrite /c10_outside /c10_cycle_set /ckC /= !inE.
  by rewrite drop0.
- rewrite /c10_outside /c10_cycle_set /ckC /= !inE drop0.
  exact: yNt.
- exact: xDy.
- exact: axy.
- move=> s.
  rewrite /ckS => /imsetP[b bB ->].
  move: bB; rewrite /ckB inE => /andP[bC yb].
  have uc : uniq (ckC x (y :: t) 2) by case/and3P: dc.
  rewrite (next_prev uc b).
  by move: yb; rewrite /=.
- apply/subsetP=> s.
  rewrite /ckS => /imsetP[b bB ->].
  rewrite /c10_cycle_set inE mem_prev.
  move: bB; rewrite inE => /andP[].
  by [].
- move=> s z sS asz.
  rewrite /c10_cycle_set inE.
  exact: hclose sS asz.
Qed.

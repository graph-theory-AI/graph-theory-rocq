(** * Prefix adapters for the Cheng--Keevash path kernel

    These records expose exactly the path-prefix and cycle-side data used by
    the [a = 2] and [a = 3] splice arguments.  Neither adapter depends on the
    out-degree: the numerical information remains in [ckpath_kernel_facts]. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import
  prelude digraph oriented dipath lemma7 ckpath_kernel_cases.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Definitions.
Variable D : finType.

Definition ckpath_cycle_set (c : seq D) : {set D} := [set z in c].
Definition ckpath_outside (c : seq D) : {set D} := ~: ckpath_cycle_set c.
Definition ckpath_successor_set (c : seq D) (S : {set D}) : {set D} :=
  [set next c s | s in S].

End Definitions.

Record ckpath_prefix2_data (D : orientedDigraph) (c : seq D)
    (S : {set D}) (v0 v1 : D) : Prop := CKPrefix2Data {
  prefix2_v0_outside : v0 \in ckpath_outside c;
  prefix2_v1_outside : v1 \in ckpath_outside c;
  prefix2_distinct : v0 != v1;
  prefix2_arc : v0 --> v1;
  prefix2_next : forall s, s \in S -> v1 --> next c s;
  prefix2_S_subset : S \subset ckpath_cycle_set c;
  prefix2_S_closed :
    forall s z, s \in S -> s --> z -> z \in ckpath_cycle_set c
}.

Record ckpath_prefix3_data (D : orientedDigraph) (c : seq D)
    (S : {set D}) (v0 v1 v2 : D) : Prop := CKPrefix3Data {
  prefix3_v0_outside : v0 \in ckpath_outside c;
  prefix3_v1_outside : v1 \in ckpath_outside c;
  prefix3_v2_outside : v2 \in ckpath_outside c;
  prefix3_v0_v1_distinct : v0 != v1;
  prefix3_v0_v2_distinct : v0 != v2;
  prefix3_v1_v2_distinct : v1 != v2;
  prefix3_arc01 : v0 --> v1;
  prefix3_arc12 : v1 --> v2;
  prefix3_next : forall s, s \in S -> v2 --> next c s;
  prefix3_S_subset : S \subset ckpath_cycle_set c;
  prefix3_S_closed :
    forall s z, s \in S -> s --> z -> z \in ckpath_cycle_set c
}.

(** At [a = 2], the kernel path decomposes as [v0 :: v1 :: c]. *)
Theorem ckpath_kernel_prefix2_adapter (D : orientedDigraph) (d : nat)
    (x : D) (p : seq D) :
  ckpath_kernel_facts d x p 2 ->
  ckpath_prefix2_data (ckC x p 2) (ckS x p 2)
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
- rewrite /ckpath_outside /ckpath_cycle_set /ckC /= !inE.
  by rewrite drop0.
- rewrite /ckpath_outside /ckpath_cycle_set /ckC /= !inE drop0.
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
  rewrite /ckpath_cycle_set inE mem_prev.
  move: bB; rewrite inE => /andP[].
  by [].
- move=> s z sS asz.
  rewrite /ckpath_cycle_set inE.
  exact: hclose sS asz.
Qed.

(** At [a = 3], the kernel path decomposes as
    [v0 :: v1 :: v2 :: c]. *)
Theorem ckpath_kernel_prefix3_adapter (D : orientedDigraph) (d : nat)
    (x : D) (p : seq D) :
  ckpath_kernel_facts d x p 3 ->
  ckpath_prefix3_data (ckC x p 3) (ckS x p 3)
    x (nth x (x :: p) 1) (nth x (x :: p) 2).
Proof.
case: p => [|y p] /=.
- move=> [_ _ [[_ hsize _ hlen] _ _ _ _]].
  exfalso; move: hlen; by rewrite -hsize.
case: p => [|z t] /=.
- move=> [_ _ [[_ hsize _ hlen] _ _ _ _]].
  exfalso; move: hlen; by rewrite -hsize.
move=> [_ _ [[hp _ _ _] [dc _ _] _ hclose _]].
have up := dipath_uniq hp.
move: up; rewrite /= => /and4P[xNyzt yNzt zNt ut].
have /andP[xDy xNzt] : (x != y) && (x \notin z :: t).
  by move: xNyzt; rewrite !inE negb_or.
have /andP[xDz xNt] : (x != z) && (x \notin t).
  by move: xNzt; rewrite !inE negb_or.
have /andP[yDz yNt] : (y != z) && (y \notin t).
  by move: yNzt; rewrite !inE negb_or.
have [axy hpyt] := dipath_cons hp.
have [ayz _] := dipath_cons hpyt.
constructor.
- rewrite /ckpath_outside /ckpath_cycle_set /ckC /= !inE drop0.
  exact: xNt.
- rewrite /ckpath_outside /ckpath_cycle_set /ckC /= !inE drop0.
  exact: yNt.
- rewrite /ckpath_outside /ckpath_cycle_set /ckC /= !inE drop0.
  exact: zNt.
- exact: xDy.
- exact: xDz.
- exact: yDz.
- exact: axy.
- exact: ayz.
- move=> s.
  rewrite /ckS => /imsetP[b bB ->].
  move: bB; rewrite /ckB inE => /andP[bC zb].
  have uc : uniq (ckC x (y :: z :: t) 3) by case/and3P: dc.
  rewrite (next_prev uc b).
  by move: zb; rewrite /=.
- apply/subsetP=> s.
  rewrite /ckS => /imsetP[b bB ->].
  rewrite /ckpath_cycle_set inE mem_prev.
  move: bB; rewrite inE => /andP[].
  by [].
- move=> s w sS asw.
  rewrite /ckpath_cycle_set inE.
  exact: hclose sS asw.
Qed.

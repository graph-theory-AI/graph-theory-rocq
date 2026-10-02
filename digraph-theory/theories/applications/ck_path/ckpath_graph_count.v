(** * Counting Boolean predicates along a duplicate-free finite sequence *)

From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented ckpath_cardinality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma count_true_bits_map_pred (T : Type) (p : pred T) (s : seq T) :
  count_true_bits (map p s) = count p s.
Proof.
elim: s => [|x s IH] //=.
by rewrite IH; case: (p x).
Qed.

Lemma count_true_bits_pred_card (T : finType) (p : pred T) (s : seq T) :
  uniq s ->
  count_true_bits (map p s) = #|[set x in s | p x]|.
Proof.
move=> us.
rewrite count_true_bits_map_pred -size_filter.
have ufilter : uniq (filter p s) := filter_uniq p us.
have hcard : #|filter p s| = size (filter p s) by exact/card_uniqP.
rewrite -hcard.
apply: eq_card => x.
by rewrite !inE mem_filter andbC.
Qed.

Lemma count_true_bits_map_enum_pred (T : finType)
    (p : pred T) (labels : seq T) (code : nat -> T) ids :
  uniq labels -> map code ids = labels ->
  count_true_bits (map (fun i => p (code i)) ids) =
    #|[set x in labels | p x]|.
Proof.
move=> ulabels Hlabels.
have Hmap : [seq p (code i) | i <- ids] = map p labels.
  rewrite -Hlabels -map_comp.
  reflexivity.
rewrite Hmap.
exact: count_true_bits_pred_card ulabels.
Qed.

Lemma pred_card_subset (T : finType) (A B : {set T}) :
  A \subset B -> #|[set x in B | x \in A]| = #|A|.
Proof.
move=> /subsetP AB.
apply: eq_card => x.
rewrite !inE.
case xA: (x \in A); last by rewrite andbF.
have xB := AB x xA.
by rewrite xB.
Qed.

Lemma pred_card_outdeg (D : diGraphType) (A : {set D}) (q : D) :
  #|[set x in A | q --> x]| = outdeg_in A q.
Proof.
by rewrite /outdeg_in.
Qed.

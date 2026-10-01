From mathcomp Require Import all_boot all_fingroup.
From Digraph.applications Require Import color_avoiding_paths.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Renaming.
Variable f : 'I_6 -> 'I_6.
Hypothesis fK : involutive f.
Let fi : injective f := can_inj fK.

Lemma palette_renaming : perm_eq (map f colors6) colors6.
Proof.
apply: uniq_perm; first by rewrite map_inj_uniq // /colors6.
- by [].
- move=> c; rewrite colors6_full; apply/mapP.
  by exists (f c); rewrite ?colors6_full ?fK.
Qed.

Lemma missing_renaming w : missing (map f w) = missing w.
Proof.
rewrite /missing -(perm_has _ palette_renaming) has_map.
apply: eq_has=> c; by rewrite /= (mem_map fi).
Qed.

Lemma missing_count_renaming w :
  count (fun c => c \notin map f w) colors6 = count (fun c => c \notin w) colors6.
Proof.
have /seq.permP counts := palette_renaming.
rewrite -(counts (fun c => c \notin map f w)) count_map.
apply: eq_count=> c; by rewrite /= (mem_map fi).
Qed.

Lemma good_word_renaming w : good_word (map f w) = good_word w.
Proof.
rewrite /good_word behead_map -map_take !missing_renaming.
case: (missing (behead w)) => //; case: (missing (take 7 w)) => //.
apply: eq_has=> i; rewrite /omit_pair -map_take -map_drop -map_cat.
by rewrite missing_count_renaming.
Qed.
End Renaming.

Lemma every_word_sound k prefix w :
  every_word k prefix -> size w = k -> good_word (rev w ++ prefix).
Proof.
elim: w k prefix => [|c w IH] [|k] prefix //=.
move=> cert [wk].
have cert_all : all (fun d => every_word k (d :: prefix)) colors6 := cert.
have cert_c := allP cert_all c (colors6_full c).
by rewrite rev_cons -cats1 -catA; exact: IH cert_c wk.
Qed.


Lemma suffix_good k prefix t :
  every_word k prefix -> size t = k -> good_word (t ++ prefix).
Proof.
move=> cert ts; have rs : size (rev t) = k by rewrite size_rev.
by have := every_word_sound cert rs; rewrite revK.
Qed.

Lemma two_suffixes_suffice :
  every_word 6 [:: c0; c0] -> every_word 6 [:: c1; c0] ->
  forall w : seq 'I_6, size w = 8 -> good_word w.
Proof.
move=> cert00 cert10 w ws.
case/lastP: w ws=> [|u c]; first discriminate.
case/lastP: u=> [|t d]; first discriminate.
rewrite !size_rcons => [[ts]].
rewrite -(good_word_renaming (tpermK c c0)) !map_rcons tpermL.
case: (boolP (tperm c c0 d == c0))=> [/eqP dc0 | dNc0].
- rewrite dc0 -!cats1 -catA.
  apply: suffix_good cert00 _; by rewrite size_map.
- rewrite -(good_word_renaming (tpermK (tperm c c0 d) c1)) !map_rcons tpermL.
  have c1Nc0 : c1 != c0 by vm_compute.
  rewrite (tpermD dNc0 c1Nc0) -!cats1 -catA.
  apply: suffix_good cert10 _; by rewrite !size_map.
Qed.

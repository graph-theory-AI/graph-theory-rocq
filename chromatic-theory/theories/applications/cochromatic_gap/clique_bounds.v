(** * Small forbidden configurations bound finite homogeneous sets.

    A large finite set admits an injective map from a small ordinal.
    Therefore absence of a five-clique bounds every clique by four,
    and absence of an independent triple bounds every stable set by two. *)
From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph coloring dom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition clique5b (G : sgraph) (a b c d e : G) :=
  [&& a -- b, a -- c, a -- d, a -- e, b -- c,
      b -- d, b -- e, c -- d, c -- e & d -- e].

Lemma large_set_embedding (T : finType) (A : {set T}) n : n <= #|A| ->
  exists f : 'I_n -> T, injective f /\ forall i, f i \in A.
Proof.
move=> hn.
pose f (i : 'I_n) : T := @enum_val T (mem A) (widen_ord hn i).
exists f; split; last by move=> i; exact: enum_valP.
move=> i j he; have hw := enum_val_inj he.
apply: ord_inj.
exact: (congr1 (@nat_of_ord _) hw).
Qed.

Lemma no_clique5_bound (G : sgraph) :
  (forall a b c d e : G, ~~ clique5b a b c d e) ->
  forall K : {set G}, clique K -> #|K| <= 4.
Proof.
move=> hno K hK; apply/negPn/negP; rewrite -ltnNge=> hk.
have [f [hi hf]] := large_set_embedding hk.
have he (i j : 'I_5) : i != j -> f i -- f j.
  move=> hij; apply: hK; rewrite ?hf //.
  by rewrite (inj_eq hi).
pose i0 : 'I_5 := @Ordinal 5 0 erefl.
pose i1 : 'I_5 := @Ordinal 5 1 erefl.
pose i2 : 'I_5 := @Ordinal 5 2 erefl.
pose i3 : 'I_5 := @Ordinal 5 3 erefl.
pose i4 : 'I_5 := @Ordinal 5 4 erefl.
have hc : clique5b (f i0) (f i1) (f i2) (f i3) (f i4).
  by rewrite /clique5b !he.
by have := hno (f i0) (f i1) (f i2) (f i3) (f i4); rewrite hc.
Qed.

Lemma no_stable3_bound (G : sgraph) :
  (forall a b c : G, uniq [:: a; b; c] -> [|| a -- b, a -- c | b -- c]) ->
  forall A : {set G}, stable A -> #|A| <= 2.
Proof.
move=> hno A /stableP hA; apply/negPn/negP; rewrite -ltnNge=> ha.
have [f [hi hf]] := large_set_embedding ha.
pose i0 : 'I_3 := @Ordinal 3 0 erefl.
pose i1 : 'I_3 := @Ordinal 3 1 erefl.
pose i2 : 'I_3 := @Ordinal 3 2 erefl.
have hu : uniq [:: f i0; f i1; f i2].
  by rewrite /= !inE !(inj_eq hi).
have hab := hA (f i0) (f i1) (hf i0) (hf i1).
have hac := hA (f i0) (f i2) (hf i0) (hf i2).
have hbc := hA (f i1) (f i2) (hf i1) (hf i2).
by have := hno _ _ _ hu; rewrite (negbTE hab) (negbTE hac) (negbTE hbc).
Qed.

(** * Hypergraph.foundations.hypergraph_matchings -- matchings of a supplied hyperedge family

    Library migration D6 (registry entry [matching], semantic class [hypergraph-edge-family];
    report meta/migration_reports/matching.md; record meta/LIBRARY_MIGRATION_D6.md; public client
    theories/examples/hyperedge_matchings.v).

    [hg_matching M E]: the family [M : {set {set T}}] is a subfamily of the hyperedge family
    [E : {set {set T}}] and its distinct members are pairwise disjoint.  The carrier [T] is an
    arbitrary finite type and [M] comes before [E].  No uniformity, positivity, nonempty-edge,
    covering, maximality or simplicity premise: the empty hyperedge [set0] is disjoint from every
    set, so it may be a member (with an empty carrier, [[set set0]] is a matching of size one of
    [[set set0]]), and a set family cannot repeat a hyperedge.  The disjointness clause is exactly
    the one MathComp's [trivIset] reflects ([hg_matchingP], through [trivIsetP]).  MathComp's
    [partition] also forbids [set0] and asks for a covering, and the simple-graph
    [GraphTheory.connectivity.matching] asks for genuine graph edges, so neither is this notion.
    Matching numbers (an attained maximum) are not defined here.

    Axiom-free: no Axiom/Parameter/Admitted. *)
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Matchings.
Variable T : finType.
Implicit Types (M N E F : {set {set T}}) (e f : {set T}).

Definition hg_matching M E : Prop :=
  M \subset E /\
  {in M &, forall e f : {set T}, e != f -> [disjoint e & f]}.

(** Boolean view: the subfamily test and MathComp's [trivIset], reflected by [trivIsetP]. *)
Lemma hg_matchingP M E : reflect (hg_matching M E) ((M \subset E) && trivIset M).
Proof.
apply: (iffP andP) => [[ME /trivIsetP dis] | [ME dis]]; split=> //.
exact/trivIsetP.
Qed.

Lemma hg_matching_sub M E : hg_matching M E -> M \subset E.
Proof. by case. Qed.

Lemma hg_matching_trivIset M E : hg_matching M E -> trivIset M.
Proof. by move=> /hg_matchingP /andP[]. Qed.

Lemma hg_matching_card M E : hg_matching M E -> #|M| <= #|E|.
Proof. by move=> /hg_matching_sub; exact: subset_leq_card. Qed.

(** The empty family is a matching of every hyperedge family, and the only one of the empty
    family. *)
Lemma hg_matching0 E : hg_matching set0 E.
Proof. by split; [exact: sub0set | move=> e f; rewrite in_set0]. Qed.

Lemma hg_matching_set0E M : hg_matching M set0 <-> M = set0.
Proof.
split=> [/hg_matching_sub|->]; last exact: hg_matching0.
by rewrite subset0 => /eqP.
Qed.

(** A single hyperedge, the empty one included, is a matching exactly when it belongs to [E]. *)
Lemma hg_matching1 e E : hg_matching [set e] E <-> e \in E.
Proof.
split=> [/hg_matching_sub|eE]; first by rewrite sub1set.
split; first by rewrite sub1set.
by move=> f g; rewrite !inE => /eqP-> /eqP->; rewrite eqxx.
Qed.

(** Subfamily and ambient-family monotonicity. *)
Lemma hg_matchingS N M E : N \subset M -> hg_matching M E -> hg_matching N E.
Proof.
move=> NM [ME dis]; split; first exact: subset_trans NM ME.
by move=> e f eN fN; apply: dis; exact: (subsetP NM).
Qed.

Lemma hg_matching_ambient M E F : E \subset F -> hg_matching M E -> hg_matching M F.
Proof. by move=> EF [ME dis]; split=> //; exact: subset_trans ME EF. Qed.

(** Two distinct members that meet rule a family out. *)
Lemma hg_matching_overlap M E e f :
  e \in M -> f \in M -> e != f -> ~~ [disjoint e & f] -> ~ hg_matching M E.
Proof. by move=> eM fM ef /negP nd [_ dis]; apply: nd; exact: dis. Qed.

(** The empty hyperedge, when it is one, can always join a matching. *)
Lemma hg_matching_set0U M E : set0 \in E -> hg_matching M E -> hg_matching (set0 |: M) E.
Proof.
move=> E0 [ME dis]; split; first by rewrite subUset sub1set E0.
move=> e f; rewrite !inE => /orP[/eqP->|eM] /orP[/eqP->|fM] ef.
- by rewrite eqxx in ef.
- by rewrite -setI_eq0 set0I.
- by rewrite -setI_eq0 setI0.
- exact: dis.
Qed.

End Matchings.

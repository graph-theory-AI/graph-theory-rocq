(** * Digraph.oriented — oriented digraphs (no loops, no antiparallel pairs)

    The [Oriented] structure sits between [DiGraph] and [Tournament]
    (CK3 plan, Decision D9): an oriented digraph is a finite digraph whose
    arc relation is irreflexive and asymmetric. Tournaments acquire the
    structure through the [DiGraph_IsTournament] factory in
    core/tournament.v, so every existing tournament instance is an oriented
    digraph silently.

    Theory (dossier items O1, O2 — stated for arbitrary vertex subsets and
    arbitrary k, per Decision D12):
    - out-degrees at the digraph level ([outdeg], [outdeg_in]) — defined for
      ANY finite digraph;
    - O1: twice the arc count of D[A] is at most |A|(|A|−1)
      ([oriented_arcs_bound]); some vertex of a nonempty A has inner
      out-degree ≤ (|A|−1)./2 ([oriented_avg_bound]); |A| ≥ 2k+1 when all
      inner out-degrees are ≥ k ([oriented_mindeg_card], [oriented_card]);
    - O2: the alias [outsel f] keeps only the arcs selected by [f];
      [outsel] of an oriented digraph is oriented, and so is every subtype
      of an oriented digraph; with [f := ksel k], every out-degree becomes
      exactly k whenever k ≤ δ⁺(D) ([outsel_ksel_outdeg]). *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph.
Set SsrOldRewriteGoalsOrder.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The structure *)

HB.mixin Record DiGraph_IsOriented V of DiGraph V := {
  arc_irrefl : irreflexive (arc : rel V);
  arc_asymm  : forall u v : V, arc u v -> arc v u = false
}.

#[short(type="orientedDigraph")]
HB.structure Definition Oriented := { V of DiGraph V & DiGraph_IsOriented V }.

(** ** Out-degrees, at the general digraph level *)

Section OutDegree.
Variable D : diGraphType.
Implicit Types (v : D) (A : {set D}).

Definition outdeg v := #|[set w | v --> w]|.

(** Out-degree into a fixed vertex subset — the induced out-degree when
    [v \in A]. *)
Definition outdeg_in A v := #|[set w in A | v --> w]|.

Lemma outdeg_inT v : outdeg_in setT v = outdeg v.
Proof. by apply: eq_card => w; rewrite !inE. Qed.

Lemma outdeg_in_le A v : outdeg_in A v <= outdeg v.
Proof.
by apply: subset_leq_card; apply/subsetP=> w; rewrite !inE => /andP[].
Qed.

Lemma outdeg_in_mono A (B : {set D}) v : A \subset B -> outdeg_in A v <= outdeg_in B v.
Proof.
move=> /subsetP sAB; apply: subset_leq_card; apply/subsetP=> w.
by rewrite !inE => /andP[/sAB-> ->].
Qed.

Lemma outdeg_in_sumE A v : outdeg_in A v = \sum_(w in A) (v --> w).
Proof.
rewrite /outdeg_in -sum1dep_card big_mkcondr /=; apply: eq_bigr => w _.
by case: (v --> w).
Qed.

End OutDegree.

(** The induced subgraph on [A] has the inner out-degrees. *)
Lemma outdeg_induced (D : diGraphType) (A : {set D}) (u : induced_digraph A) :
  outdeg u = outdeg_in A (val u).
Proof.
rewrite /outdeg /outdeg_in -(card_imset _ val_inj); apply: eq_card => w.
apply/imsetP/idP=> [[z + ->]|].
  by rewrite !inE sub_arcE => az; rewrite (valP z) az.
rewrite inE => /andP[wA arcw].
by exists (Sub w wA); rewrite ?inE ?sub_arcE ?SubK.
Qed.

(** ** O1: the counting and average bounds *)

Section OrientedCounting.
Variable O : orientedDigraph.
Implicit Types (A : {set O}).

Lemma arc_pair_bound (v w : O) : (v --> w) + (w --> v) <= (v != w).
Proof.
case: (eqVneq v w) => [->|_]; first by rewrite arc_irrefl.
case avw: (v --> w); last by rewrite add0n leq_b1.
by rewrite (arc_asymm _ _ avw) addn0.
Qed.

(** O1, counting form: twice the arc count of D[A] is ≤ |A|(|A|−1). *)
Lemma oriented_arcs_bound A :
  2 * (\sum_(v in A) outdeg_in A v) <= #|A| * (#|A| - 1).
Proof.
rewrite mul2n -addnn.
under eq_bigr do rewrite outdeg_in_sumE.
rewrite {2}exchange_big /= -big_split /=.
apply: leq_trans (_ : \sum_(v in A) (#|A| - 1) <= _); last first.
  by rewrite sum_nat_const mulnC.
apply: leq_sum => v vA.
apply: leq_trans (_ : \sum_(w in A) ((v != w) : nat) <= _).
  rewrite -big_split /=; apply: leq_sum => w _; exact: arc_pair_bound.
have -> : \sum_(w in A) ((v != w) : nat) = #|A :\ v|.
  rewrite -sum1dep_card big_mkcond [RHS]big_mkcond /=.
  by apply: eq_bigr => w _; rewrite !inE eq_sym andbC;
     case: (w \in A); case: (w != v).
by rewrite (cardsD1 v A) vA add1n subSS subn0.
Qed.

(** O1(a): some vertex of a nonempty A has inner out-degree ≤ (|A|−1)./2. *)
Lemma oriented_avg_bound A :
  A != set0 -> exists2 x, x \in A & outdeg_in A x <= (#|A| - 1)./2.
Proof.
move=> An0.
case: (boolP [exists x in A, outdeg_in A x <= (#|A| - 1)./2]).
  by case/exists_inP=> x xA xle; exists x.
rewrite negb_exists_in => /forall_inP big_; exfalso.
have m_gt0 : 0 < #|A| by rewrite card_gt0.
have mle : #|A| <= 2 * ((#|A| - 1)./2).+1.
  rewrite mulnS mul2n -[X in X <= _](subnK m_gt0) addn1.
  rewrite -[X in X.+1 <= _]odd_double_half.
  by rewrite addnC [X in _ < X]addnC ltn_add2l ltnS leq_b1.
have sumlo : #|A| * ((#|A| - 1)./2).+1 <= \sum_(v in A) outdeg_in A v.
  by rewrite -sum_nat_const; apply: leq_sum => v /big_; rewrite -ltnNge.
have := oriented_arcs_bound A.
rewrite leqNgt => /negP; apply.
have step1 : #|A| * (#|A| - 1) < #|A| * #|A|.
  by rewrite ltn_pmul2l // ltn_subrL m_gt0.
apply: leq_trans step1 _.
apply: leq_trans (_ : 2 * (#|A| * ((#|A| - 1)./2).+1) <= _); last first.
  by rewrite leq_pmul2l.
by rewrite mulnCA leq_pmul2l.
Qed.

(** O1(b): if all inner out-degrees are at least k, then |A| ≥ 2k+1. *)
Lemma oriented_mindeg_card A k :
  A != set0 -> (forall v, v \in A -> k <= outdeg_in A v) -> 2 * k + 1 <= #|A|.
Proof.
move=> An0 dmin.
have m_gt0 : 0 < #|A| by rewrite card_gt0.
have [x xA xle] := oriented_avg_bound An0.
have kle : k <= (#|A| - 1)./2 by exact: leq_trans (dmin x xA) xle.
rewrite addn1 -[X in _ <= X](subnK m_gt0) addn1 ltnS mul2n.
have := leq_double k (#|A| - 1)./2; rewrite kle => dble.
apply: leq_trans (_ : (#|A| - 1)./2.*2 <= _); first by rewrite dble.
by rewrite -[X in _ <= X]odd_double_half leq_addl.
Qed.

(** O1(c): a nonempty oriented digraph with min out-degree ≥ k has
    ≥ 2k+1 vertices. *)
Lemma oriented_card k :
  0 < #|O| -> (forall v : O, k <= outdeg v) -> 2 * k + 1 <= #|O|.
Proof.
move=> n_gt0 dmin; rewrite -cardsT.
apply: oriented_mindeg_card => [|v _].
  by apply/set0Pn; have /card_gt0P[x _] := n_gt0; exists x; rewrite inE.
by rewrite outdeg_inT.
Qed.

End OrientedCounting.

(** ** Subtypes of an oriented digraph are oriented *)

Section SubOriented.
Variables (O : orientedDigraph) (P : pred O).

Fact sub_oarc_irrefl : irreflexive (arc : rel {x : O | P x}).
Proof. by move=> u; rewrite sub_arcE arc_irrefl. Qed.

Fact sub_oarc_asymm (u v : {x : O | P x}) : arc u v -> arc v u = false.
Proof. rewrite !sub_arcE; exact: arc_asymm. Qed.

HB.instance Definition _ :=
  DiGraph_IsOriented.Build {x | P x} sub_oarc_irrefl sub_oarc_asymm.

End SubOriented.

(** Object-level version for statements. *)
Definition induced_oriented (O : orientedDigraph) (S : {set O}) :
  orientedDigraph := {x : O | x \in S} : orientedDigraph.

(** ** O2: out-selection — keep only the arcs chosen by [f] *)

(** The alias takes [f] as a REAL parameter (M2 lesson: a type alias must
    use its parameters, or section discharge drops them and all selections
    collapse onto one type). *)
Definition outsel (D : diGraphType) (f : D -> {set D}) : Type := D.

Section OutSelection.
Variables (D : diGraphType) (f : D -> {set D}).

HB.instance Definition _ := Finite.on (outsel f).
HB.instance Definition _ :=
  HasArc.Build (outsel f) (fun u v : D => (v \in f u) && (u --> v)).

Lemma outsel_arcE (u v : outsel f) :
  (u --> v) = ((v : D) \in f (u : D)) && ((u : D) --> (v : D)).
Proof. by []. Qed.

Lemma outsel_arc_sub (u v : outsel f) : u --> v -> (u : D) --> (v : D).
Proof. by rewrite outsel_arcE => /andP[]. Qed.

End OutSelection.

(** [outsel] of an oriented digraph is oriented (a sub-relation of an
    irreflexive asymmetric relation is one). *)

Section OutSelectionOriented.
Variables (O : orientedDigraph) (f : O -> {set O}).

Fact outsel_irrefl : irreflexive (arc : rel (outsel f)).
Proof. by move=> u; rewrite outsel_arcE arc_irrefl andbF. Qed.

Fact outsel_asymm (u v : outsel f) : arc u v -> arc v u = false.
Proof.
by rewrite !outsel_arcE => /andP[_ a]; rewrite (arc_asymm _ _ a) andbF.
Qed.

HB.instance Definition _ :=
  DiGraph_IsOriented.Build (outsel f) outsel_irrefl outsel_asymm.

End OutSelectionOriented.

(** ** The canonical k-subset selector *)

Section KSelection.
Variables (D : diGraphType) (k : nat).

Definition ksel (v : D) : {set D} := [set x in take k (enum [set w | v --> w])].

Lemma ksel_sub v : ksel v \subset [set w | v --> w].
Proof.
apply/subsetP=> x; rewrite !inE => /mem_take.
by rewrite mem_enum inE.
Qed.

Lemma ksel_card v : k <= outdeg v -> #|ksel v| = k.
Proof.
move=> kle; rewrite /ksel cardsE /=.
rewrite (card_uniqP _) ?size_take.
  by rewrite -cardE; case: ltngtP kle.
by rewrite take_uniq // enum_uniq.
Qed.

(** O2's exit: in [outsel ksel], every out-degree is exactly k. *)
Lemma outsel_ksel_outdeg (v : outsel ksel) :
  (forall u : D, k <= outdeg u) -> outdeg v = k.
Proof.
move=> dmin.
rewrite /outdeg -(ksel_card (dmin (v : D))).
apply: eq_card => w; rewrite !inE outsel_arcE /ksel inE.
apply: andb_idr => /mem_take wk.
by move: wk; rewrite mem_enum inE.
Qed.

End KSelection.

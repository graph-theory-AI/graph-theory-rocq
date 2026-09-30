(** * Packing.conjectures.implications_X226 — implication spine for wave X226.

    The corpus records two confirmed [implies] relations out of Conjecture 1.8
    (meta/corpus_relations.json):

      gc:e012   arxiv:2302.04986#00  ==>  arxiv:2302.04986#01
                (every forest H  ==>  H = P_t, t >= 6)
      gc:e013   arxiv:2302.04986#00  ==>  arxiv:2302.04986#04
                (every forest H  ==>  H = S_a u S_b)

    Both endpoints of both edges are formalised in [X226.v], so both are
    discharged here as Qed theorems (status=verified).  Each is a pure
    instantiation of the universally quantified forest hypothesis, so the whole
    mathematical content is the missing side condition: the graph named by the
    TARGET row really is a forest.  That is what the first half of this file
    proves, through coq-graph-theory's [K3_free_forest] (a graph is a forest iff
    it has no K_3 minor):

      [x226_path_is_forest]        P_t has no K_3 minor: the branch sets of a
                                   minor map are connected, hence (this is
                                   [x226_path_interval]) intervals of 'I_t, hence
                                   linearly ordered, and the two extreme ones of
                                   three pairwise adjacent intervals are separated
                                   by the middle one.
      [x226_two_stars_is_forest]   a star has no K_3 minor (at most one of three
                                   disjoint branch sets contains the centre, and
                                   two leaf-only sets are never adjacent), and the
                                   disjoint union of two forests is a forest
                                   ([sgraph.join_is_forest]).

    These are also faithfulness evidence for X226: they confirm that the concrete
    carriers [x226_path_graph t] and [sjoin (x226_star a) (x226_star b)] are the
    kind of object Conjecture 1.8 quantifies over.

    No Axiom / Parameter / Admitted; [Print Assumptions] at the end. *)

From GTBase Require Import base.
(* [minor] is imported (base only re-exports the [minor]/[minor_rmap] abbreviations):
   [minorRE] and [K3_free_forest] live there.  [preliminaries] supplies [restrict]. *)
From GraphTheory Require Import minor preliminaries.
From Packing.conjectures Require Import X226.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ============================================================================
    P_t is a forest.
    ========================================================================== *)

Section PathForest.
Variable t : nat.
Local Notation P := (x226_path_graph t).

Lemma x226_path_edge (i j : P) :
  (i -- j) = (i != j) && (((val i).+1 == val j) || ((val j).+1 == val i)).
Proof. by []. Qed.

Lemma x226_disj_mem (A B : {set P}) (u : P) :
  [disjoint A & B] -> u \in A -> u \in B -> False.
Proof.
rewrite -setI_eq0 => /eqP/setP/(_ u); rewrite !inE => H uA uB.
by move: H; rewrite uA uB.
Qed.

Lemma x226_path_between (S : {set P}) (k : P) (p : seq P) :
  forall i : P, path (restrict S (--)) i p ->
  i \in S -> val i <= val k -> val k <= val (last i p) -> k \in S.
Proof.
elim: p => [|z p IH] i /=.
  move=> _ iS lik lki.
  by have -> : k = i by apply: val_inj; apply/eqP; rewrite eqn_leq lki lik.
case/andP => /andP[/andP[_ zS] /andP[_ iz]] pth iS lik lkj.
have [ki|ki] := eqVneq (val k) (val i).
  by have -> : k = i by apply: val_inj.
have lik' : val i < val k by rewrite ltn_neqAle eq_sym ki lik.
apply: (IH z pth zS) => //.
move: iz => /orP[/eqP ez|/eqP ez].
  by rewrite -ez.
by apply: leq_trans (ltnW lik'); rewrite -ez.
Qed.

Lemma x226_path_interval (S : {set P}) (i j k : P) :
  connected S -> i \in S -> j \in S -> val i <= val k -> val k <= val j -> k \in S.
Proof.
move=> cS iS jS lik lkj.
have /connectP[p pth lst] := cS i j iS jS.
by apply: (x226_path_between pth iS lik); rewrite -lst.
Qed.

Definition x226_lt_set (A B : {set P}) : Prop :=
  forall a b : P, a \in A -> b \in B -> val a < val b.

Lemma x226_sep (A B : {set P}) (x y : P) :
  connected A -> connected B -> [disjoint A & B] ->
  x \in A -> y \in B -> val x < val y -> x226_lt_set A B.
Proof.
move=> cA cB dAB xA yB lxy a b aA bB.
have step1 : val a < val y.
  rewrite ltnNge; apply/negP => lya.
  have yA : y \in A by apply: (x226_path_interval cA xA aA (ltnW lxy) lya).
  exact: (x226_disj_mem dAB yA yB).
rewrite ltnNge; apply/negP => lba.
have aB : a \in B by apply: (x226_path_interval cB bB yB lba (ltnW step1)).
exact: (x226_disj_mem dAB aA aB).
Qed.

Lemma x226_lt_total (A B : {set P}) :
  connected A -> connected B -> [disjoint A & B] -> A != set0 -> B != set0 ->
  x226_lt_set A B \/ x226_lt_set B A.
Proof.
move=> cA cB dAB /set0Pn[x xA] /set0Pn[y yB].
have nxy : val x != val y.
  apply/eqP => e; apply: (x226_disj_mem dAB xA).
  by have -> : x = y by apply: val_inj.
have [lxy|lyx] := ltnP (val x) (val y).
  by left; exact: (x226_sep cA cB dAB xA yB lxy).
right; apply: (x226_sep cB cA _ yB xA) => //.
  by rewrite disjoint_sym.
by rewrite ltn_neqAle eq_sym nxy lyx.
Qed.

Lemma x226_path_K3_free : ~ minor P 'K_3.
Proof.
case/minorRE => phi [phi0 phiC phiD phiN].
have mid : forall i j k : ('K_3),
    x226_lt_set (phi i) (phi j) -> x226_lt_set (phi j) (phi k) -> i != k -> False.
  move=> i j k lij ljk ik.
  have /neighborP[u [w [uA wC uw]]] : neighbor (phi i) (phi k) by exact: phiN ik.
  have /set0Pn[m mB] := phi0 j.
  have l1 := lij u m uA mB.
  have l2 := ljk m w mB wC.
  move: uw; rewrite x226_path_edge => /andP[_ /orP[/eqP e|/eqP e]].
    have h2 : (val u).+1 < val w by apply: leq_ltn_trans l2.
    by rewrite -e ltnn in h2.
  have h2 : val u < val w by apply: ltn_trans l1 l2.
  have h3 : val w < val u by rewrite -e.
  by move: (ltn_trans h2 h3); rewrite ltnn.
have D : forall i j : ('K_3),
    i != j -> x226_lt_set (phi i) (phi j) \/ x226_lt_set (phi j) (phi i).
  move=> i j ij; apply: x226_lt_total; by [exact: phiC|exact: phiD ij|exact: phi0].
pose k0 : 'K_3 := ord0.
pose k1 : 'K_3 := @Ordinal 3 1 isT.
pose k2 : 'K_3 := @Ordinal 3 2 isT.
case: (D k0 k1 isT) => d01; case: (D k0 k2 isT) => d02; case: (D k1 k2 isT) => d12.
- exact: (mid k0 k1 k2 d01 d12 isT).
- exact: (mid k0 k2 k1 d02 d12 isT).
- exact: (mid k0 k1 k2 d01 d12 isT).
- exact: (mid k2 k0 k1 d02 d01 isT).
- exact: (mid k1 k0 k2 d01 d02 isT).
- exact: (mid k1 k0 k2 d01 d02 isT).
- exact: (mid k1 k2 k0 d12 d02 isT).
- exact: (mid k2 k1 k0 d12 d01 isT).
Qed.

Lemma x226_path_is_forest : is_forest [set: P].
Proof. exact: (proj1 (K3_free_forest _) x226_path_K3_free). Qed.

End PathForest.

(** ============================================================================
    The star S_a, and the disjoint union of two stars, are forests.
    ========================================================================== *)

Lemma x226_star_edge (a : nat) (u v : x226_star a) :
  (u -- v) = (u == ord0) (+) (v == ord0).
Proof. by []. Qed.

Lemma x226_star_K3_free (a : nat) : ~ minor (x226_star a) 'K_3.
Proof.
case/minorRE => phi [_ _ phiD phiN].
pose z : x226_star a := ord0.
have key : forall i j : ('K_3), i != j -> z \notin phi i -> z \notin phi j -> False.
  move=> i j ij zi zj.
  have /neighborP[u [v [ui vj uv]]] : neighbor (phi i) (phi j) by exact: phiN ij.
  have u0 : (u == ord0) = false.
    apply/negbTE; apply/negP => /eqP uz; move/negP: zi; apply.
    by rewrite /z -uz.
  have v0 : (v == ord0) = false.
    apply/negbTE; apply/negP => /eqP vz; move/negP: zj; apply.
    by rewrite /z -vz.
  by move: uv; rewrite x226_star_edge u0 v0.
have Dis : forall i j : ('K_3), i != j -> z \in phi i -> z \notin phi j.
  move=> i j ij zi; apply/negP => zj.
  by have := phiD i j ij; rewrite -setI_eq0 => /eqP/setP/(_ z); rewrite !inE zi zj.
have [h|h] := boolP (z \in phi ord0).
  by apply: (key (@Ordinal 3 1 isT) (@Ordinal 3 2 isT) isT); apply: (Dis ord0) h.
have [h1|h1] := boolP (z \in phi (@Ordinal 3 1 isT)).
  by apply: (key ord0 (@Ordinal 3 2 isT) isT) => //; apply: (Dis (@Ordinal 3 1 isT)) h1.
by apply: (key ord0 (@Ordinal 3 1 isT) isT).
Qed.

Lemma x226_star_is_forest (a : nat) : is_forest [set: x226_star a].
Proof. exact: (proj1 (K3_free_forest _) (@x226_star_K3_free a)). Qed.

Lemma x226_two_stars_is_forest (a b : nat) :
  is_forest [set: sjoin (x226_star a) (x226_star b)].
Proof.
exact (@join_is_forest (@Forest (x226_star a) (@x226_star_is_forest a))
                       (@Forest (x226_star b) (@x226_star_is_forest b))).
Qed.

(** ============================================================================
    The two corpus edges.
    ========================================================================== *)

(*@EDGE from=eta_bounded_forest_free_classes_statement to=eta_bounded_path_free_classes_statement kind=implies status=verified proof=eta_bounded_forest_free_classes_implies_eta_bounded_path_free_classes cite="gc:e012; arXiv:2302.04986, Conjecture 1.8 specialised to H = P_t (a path is a forest)" *)

Theorem eta_bounded_forest_free_classes_implies_eta_bounded_path_free_classes :
  eta_bounded_forest_free_classes_statement ->
  eta_bounded_path_free_classes_statement.
Proof. by move=> H t _; apply: H; exact: (@x226_path_is_forest t). Qed.

(*@EDGE from=eta_bounded_forest_free_classes_statement to=eta_bounded_two_stars_free_classes_statement kind=implies status=verified proof=eta_bounded_forest_free_classes_implies_eta_bounded_two_stars_free_classes cite="gc:e013; arXiv:2302.04986, Conjecture 1.8 specialised to H = S_a u S_b (a disjoint union of two stars is a forest)" *)

Theorem eta_bounded_forest_free_classes_implies_eta_bounded_two_stars_free_classes :
  eta_bounded_forest_free_classes_statement ->
  eta_bounded_two_stars_free_classes_statement.
Proof. by move=> H a b _ _; apply: H; exact: (@x226_two_stars_is_forest a b). Qed.

(** The hypercube row [arxiv:2401.00299#04] carries no corpus relation, and none
    of the three eta rows relates to it, so no further edge is scheduled. *)

(** ============================================================================
    Axiom audit.
    ========================================================================== *)

Print Assumptions x226_path_is_forest.
Print Assumptions x226_two_stars_is_forest.
Print Assumptions eta_bounded_forest_free_classes_implies_eta_bounded_path_free_classes.
Print Assumptions eta_bounded_forest_free_classes_implies_eta_bounded_two_stars_free_classes.

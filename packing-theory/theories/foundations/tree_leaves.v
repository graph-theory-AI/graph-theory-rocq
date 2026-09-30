(** * Packing.foundations.tree_leaves -- leaves of a forest vs. its maximum degree

    General helper for the wave X47/X48 tree-decomposition rows: in any forest, the
    maximum degree is at most the number of leaves ([Delta G <= #|leaves|]).  The
    proof is the standard one: for any vertex [v], every neighbour [u] of [v] starts
    a branch of [G - v] that contains a leaf, and distinct neighbours give distinct
    leaves, because in a forest an irredundant path leaving [v] meets exactly one
    neighbour of [v].

    Nothing here is specific to trees: connectedness is never used, so the bound
    holds for every forest (a tree is the connected case).

    Contents:
    - [forest_nbr_on_irred]: in a forest, all neighbours of [x] lying on one
      irredundant path out of [x] coincide (they are its second vertex);
    - [forest_branch_leaf]: for every edge [v -- a] of a forest, the component of
      [a] in [G - v] contains a leaf of [G];
    - [forest_branch_uniq]: a vertex [w] of [G - v] is reached from at most one
      neighbour of [v];
    - [forest_Delta_leq_leaves]: [Delta G <= #|[set v | #|N(v)| == 1]|]. *)

From GTBase Require Export base.
From GraphTheory Require Import preliminaries.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ForestLeaves.
Variable G : sgraph.
Hypothesis forestG : is_forest [set: G].

(** ** Neighbours of the start vertex on an irredundant path *)

Lemma forest_nbr_on_irred (x y : G) (p : Path x y) :
  irred p -> forall u u', u \in p -> x -- u -> u' \in p -> x -- u' -> u = u'.
Proof.
move=> Ip u u' up xu u'p xu'.
have [e|xy] := eqVneq x y.
  subst y; rewrite (irredxx Ip) mem_idp in up.
  by move: xu; rewrite (eqP up) sg_irrefl.
case: (splitL p xy) => a [xa] [q [def_p _]]; subst p.
move: Ip; rewrite irred_edgeL => /andP[xNq Iq].
suff K : forall z, z \in pcat (edgep xa) q -> x -- z -> z = a.
  by rewrite (K u up xu) (K u' u'p xu').
move=> z zp xz.
have [//|zNa] := eqVneq z a.
have zNx : z != x by rewrite eq_sym sg_edgeNeq.
have zq : z \in q.
  by move: zp; rewrite mem_pcat mem_edgep (negbTE zNx) (negbTE zNa) /=.
case def_q : _ / (isplitP Iq zq) => [r1 r2 Ir1 _ _].
have xNr1 : x \notin r1.
  by apply: contraNN xNq => xr1; rewrite def_q mem_pcat xr1.
have Ixz : irred (pcat (edgep xa) r1) by rewrite irred_edgeL xNr1 Ir1.
have E : pcat (edgep xa) r1 = edgep xz.
  exact: (forestT_unique forestG Ixz (irred_edge xz)).
have aNx : a != x by apply: contraNneq xNq => e; rewrite -e; exact: path_begin.
have aP : a \in pcat (edgep xa) r1 by rewrite mem_pcat mem_edgep eqxx orbT.
move: aP; rewrite E mem_edgep (negbTE aNx) /= => /eqP az.
by rewrite az.
Qed.

(** ** Every branch at a vertex contains a leaf *)

(** Induction on the number of vertices outside the path: an irredundant path out
    of [a] avoiding [v] either ends in a leaf, or can be extended. *)
Lemma forest_branch_leaf_ind (v : G) (n : nat) :
  forall (a w : G) (p : Path a w), v -- a -> irred p -> v \notin p ->
  #|~: [set z in p]| <= n ->
  exists (w' : G) (q : Path a w'), [/\ irred q, v \notin q & #|N(w')| == 1].
Proof.
elim: n => [|n IH] a w p va Ip vNp Hn.
  move: Hn; rewrite leqn0 => /eqP/cards0_eq H0.
  have H1 : v \notin ~: [set z in p] by rewrite H0 in_set0.
  have vp : v \in p by move: H1; rewrite !inE negbK.
  by move: vNp; rewrite vp.
have [wl|wNl] := boolP (#|N(w)| == 1).
  by exists w, p; split.
(* the full path from [v] through [a] to [w] *)
have IP : irred (pcat (edgep va) p) by rewrite irred_edgeL vNp Ip.
have wp : w \in p := path_end p.
have vw : v != w by apply: contraNneq vNp => ->.
case: (splitR (pcat (edgep va) p) vw) => d [P'] [dw] def_P.
have dP : d \in pcat (edgep va) p by rewrite def_P mem_pcat path_end.
(* a neighbour of [w] on the full path is necessarily [d] *)
have uniqd : forall z, z \in pcat (edgep va) p -> w -- z -> z = d.
  move=> z zP wz; apply: (@forest_nbr_on_irred w v (prev (pcat (edgep va) p))).
  - by rewrite irred_rev.
  - by rewrite mem_prev.
  - exact: wz.
  - by rewrite mem_prev.
  - by rewrite sgP.
have dN : d \in N(w) by rewrite in_opn sgP.
have gt0 : 0 < #|N(w)| by apply/card_gt0P; exists d.
have card2 : 2 <= #|N(w)| by rewrite ltn_neqAle eq_sym wNl gt0.
have sub2 : ~~ (N(w) \subset [set d]).
  apply/negP => sub; have := subset_leq_card sub; rewrite cards1 => le1.
  by move: (leq_trans card2 le1).
case/subsetPn: sub2 => z zN zNd.
have wz : w -- z by rewrite -in_opn.
have zNP : z \notin pcat (edgep va) p.
  apply: contraNN zNd => zP; rewrite inE; apply/eqP; exact: uniqd.
have zNp : z \notin p by apply: contraNN zNP => zp; rewrite mem_pcat zp orbT.
pose q := pcat p (edgep wz).
have Iq : irred q by rewrite /q irred_edgeR zNp Ip.
have vNq : v \notin q.
  rewrite /q mem_pcat mem_edgep (negbTE vNp) /=.
  apply/norP; split; first by rewrite (negbTE vw).
  by apply: contraNneq zNP => <-; rewrite mem_pcat mem_edgep eqxx.
apply: (IH a z q va Iq vNq).
have sub : ~: [set t in q] \subset (~: [set t in p]) :\ z.
  apply/subsetP => t; rewrite !inE => tNq; apply/andP; split.
    by apply: contraNneq tNq => ->; rewrite mem_edgep eqxx !orbT.
  by apply: contraNN tNq => tp; rewrite tp orTb.
apply: (leq_trans (subset_leq_card sub)).
have zin : z \in ~: [set t in p] by rewrite !inE.
have H2 : (z \in ~: [set t in p]) + #|(~: [set t in p]) :\ z| <= n.+1.
  by rewrite -cardsD1; exact: Hn.
by move: H2; rewrite zin /= ltnS.
Qed.

Lemma forest_branch_leaf (v a : G) : v -- a ->
  exists (w : G) (q : Path a w), [/\ irred q, v \notin q & #|N(w)| == 1].
Proof.
move=> va; apply: (@forest_branch_leaf_ind v #|G| a a (idp a)) => //.
- exact: irred_idp.
- by rewrite mem_idp sg_edgeNeq.
- exact: max_card.
Qed.

(** ** Distinct neighbours of [v] reach distinct vertices of [G - v] *)

(** [branch_conn v] : connectivity in [G - v], i.e. "in the same branch at [v]". *)
Definition branch_conn (v : G) := connect (restrict (~: [set v]) (--)).

Lemma forest_reach_path (v u w : G) : v -- u -> branch_conn v u w ->
  exists p : Path v w, irred p /\ u \in p.
Proof.
move=> vu; have [e _|uw] := eqVneq u w.
  subst w; exists (edgep vu); split; first exact: irred_edge.
  by rewrite mem_edgep eqxx orbT.
case/(connect_irredRP uw) => p Ip /subsetP subp.
have vNp : v \notin p by apply/negP => vp; move: (subp v vp); rewrite !inE eqxx.
exists (pcat (edgep vu) p); split; first by rewrite irred_edgeL vNp Ip.
by rewrite mem_pcat mem_edgep eqxx orbT.
Qed.

Lemma forest_branch_uniq (v u u' w : G) :
  v -- u -> v -- u' -> branch_conn v u w -> branch_conn v u' w -> u = u'.
Proof.
move=> vu vu' /(forest_reach_path vu)[p [Ip up]] /(forest_reach_path vu')[p' [Ip' u'p']].
have E : p = p' by exact: (forestT_unique forestG Ip Ip').
by apply: (forest_nbr_on_irred Ip up vu) => //; rewrite E.
Qed.

(** ** The bound *)

Lemma forest_Delta_leq_leaves : Delta G <= #|[set v : G | #|N(v)| == 1]|.
Proof.
rewrite /Delta; apply/bigmax_leqP => v _.
pose L := [set v0 : G | #|N(v0)| == 1].
pose br (w : G) : G := odflt v [pick u | (v -- u) && branch_conn v u w].
apply: (@leq_trans #|br @: L|); last exact: leq_imset_card.
apply: subset_leq_card; apply/subsetP => u; rewrite in_opn => vu.
have [w [q [Iq vNq lw]]] := forest_branch_leaf vu.
have Bvw : branch_conn v u w.
  rewrite /branch_conn; apply: (connectRI q) => z zq; rewrite !inE.
  by apply: contraNneq vNq => <-.
have brw : br w = u.
  rewrite /br; case: pickP => [u' /andP[vu' Bu']|/(_ u)]; last by rewrite vu Bvw.
  by rewrite (forest_branch_uniq vu vu' Bvw Bu').
by rewrite -brw; apply: imset_f; rewrite inE.
Qed.

End ForestLeaves.

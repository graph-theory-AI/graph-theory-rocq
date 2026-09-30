(** * Cycle.foundations.matchings_cuts — perfect matchings versus odd edge cuts

    The parity facts that link a perfect matching of a multigraph to the edge
    cuts of the graph, derived from the handshake identity
    [cycle_space.sum_subdeg_cut].  Stated WITHOUT the conjecture-level
    vocabulary of [U6.v] / [U10.v]: a perfect matching appears as the unfolded
    [forall v, subdeg M v = 1], [cubic] as [loopless] plus [mdeg _ = 3].

    - [pm_cut_parity]: a perfect matching meets [cut S] in [#|S|] edges mod 2.
    - [cubic_cut_parity]: in a 3-regular multigraph, [odd #|cut S| = odd #|S|].
    - [pm_meets_odd_cut] (F27): in a 3-regular multigraph, every perfect
      matching meets every ODD edge cut, in particular non-trivially. *)

From GraphTheory Require Import mgraph.
From GTBase Require Export base.
From Cycle.foundations Require Export cycle_space.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A perfect matching meets [cut S] in a number of edges congruent to [#|S|]:
    the [M]-degree sum over [S] is [#|S|], and the handshake identity says that
    sum counts the cut edges once and the inside edges twice. *)
Lemma pm_cut_parity (G : mgraph) (M : {set edge G}) (S : {set G}) :
  (forall v : G, subdeg M v = 1) -> odd #|M :&: cut S| = odd #|S|.
Proof.
move=> pm.
have h := sum_subdeg_cut M S.
have e1 : \sum_(v in S) subdeg M v = #|S|.
  by rewrite -sum1_card; apply: eq_bigr => v _; exact: pm v.
by rewrite -e1 h oddD oddM /=.
Qed.

(** In a 3-regular multigraph a cut is odd exactly when its side is odd. *)
Lemma cubic_cut_parity (G : mgraph) (S : {set G}) :
  (forall v : G, mdeg v = 3) -> odd #|cut S| = odd #|S|.
Proof. by move=> reg; rewrite (@reg_cut_parity _ 3 S reg) oddM /= andbT. Qed.

(** In a [(2t+1)]-regular multigraph a cut is odd exactly when its side is. *)
Lemma reg_odd_cut_parity (G : mgraph) (t : nat) (S : {set G}) :
  (forall v : G, mdeg v = (2 * t + 1)%N) -> odd #|cut S| = odd #|S|.
Proof.
move=> reg; rewrite (@reg_cut_parity _ (2 * t + 1)%N S reg) oddM oddD oddM /=.
by rewrite andbT.
Qed.

(** F27: in a 3-regular multigraph every perfect matching MEETS every odd edge
    cut (it meets it in an odd, hence positive, number of edges). *)
Lemma pm_meets_odd_cut (G : mgraph) (M : {set edge G}) (S : {set G}) :
  (forall v : G, mdeg v = 3) -> (forall v : G, subdeg M v = 1) ->
  odd #|cut S| -> M :&: cut S != set0.
Proof.
move=> reg pm oc.
have h : odd #|M :&: cut S| by rewrite (@pm_cut_parity _ M S pm) -cubic_cut_parity.
rewrite -card_gt0 lt0n; apply/negP => /eqP h0.
by rewrite h0 in h.
Qed.

(** ** Class-1 regular multigraphs decompose into perfect matchings *)

(** If a LOOPLESS multigraph is [k]-regular and its chromatic index is [k] (the
    class-1 property, [k] being then the maximum degree), the [k] colour classes
    of an optimal edge colouring are PERFECT MATCHINGS: they partition the edge
    set, each meets every vertex at most once (a colour class is an independent
    set of the line graph, i.e. a matching) and, since a vertex lies on exactly
    [k] edges lying in [k] pairwise distinct classes, each class meets every
    vertex exactly once. *)
Lemma class1_pm_partition (G : mgraph) (k : nat) :
  loopless G -> (forall v : G, mdeg v = k) -> chromatic_index G = k ->
  exists P : {set {set edge G}},
    [/\ #|P| = k, partition P [set: edge G]
      & forall M : {set edge G}, M \in P -> forall v : G, subdeg M v = 1].
Proof.
move=> hll hreg hci.
have [P hcol hPk] : exists2 P : {set {set edge G}},
    @coloring (line_graph G) P [set: edge G] & #|P| = k.
  move: hci; rewrite /chromatic_index; case: chiP => P hcol hmin hPk.
  by exists P.
have [hpart hstab] := andP hcol.
have hcov : cover P = [set: edge G] := cover_partition hpart.
have htriv : trivIset P by have [_ h _] := and3P hpart.
have hstab' : forall M : {set edge G}, M \in P -> @stable (line_graph G) M.
  move=> M hM; move: (forallP hstab M); rewrite hM /=.
  by [].
have hnadj : forall (M : {set edge G}) (e f : edge G),
    M \in P -> e \in M -> f \in M -> e != f -> ~~ share_endpoint e f.
  move=> M e f hM he hf hef.
  have /stableP hs := hstab' M hM.
  have := hs e f he hf; rewrite /edge_rel /= /line_rel hef /=.
  by [].
have hmatch : forall (M : {set edge G}) (v : G),
    M \in P -> (#|edges_at v :&: M| <= 1)%N.
  move=> M v hM; rewrite leqNgt; apply/negP => /card_gt1P[e [f [he hf hef]]].
  move: he hf; rewrite !inE => /andP[hie heM] /andP[hif hfM].
  have := hnadj M e f hM heM hfM hef.
  by move/negP; apply; apply/existsP; exists v; rewrite hie hif.
have hge : forall (M : {set edge G}) (v : G),
    M \in P -> (1 <= #|edges_at v :&: M|)%N.
  move=> M v hM.
  have hinj : {in edges_at v &, injective (pblock P)}.
    move=> e f he hf hpb; apply/eqP; apply/negPn/negP => hne.
    have hMe : pblock P e \in P by rewrite pblock_mem // hcov inE.
    have h1 : e \in pblock P e by rewrite mem_pblock hcov inE.
    have h2 : f \in pblock P e by rewrite hpb mem_pblock hcov inE.
    have := hnadj _ e f hMe h1 h2 hne.
    move/negP; apply; apply/existsP; exists v.
    by move: he hf; rewrite !inE => -> ->.
  have himg : [set pblock P e | e in edges_at v] = P.
    apply/eqP; rewrite eqEcard; apply/andP; split.
      apply/subsetP => B /imsetP[e he ->].
      by rewrite pblock_mem // hcov inE.
    rewrite (card_in_imset hinj) hPk -(hreg v) (mdeg_loopless v hll).
    exact: leqnn.
  move: hM; rewrite -himg => /imsetP[e he hMe].
  apply/card_gt0P; exists e; rewrite !inE hMe.
  move: he; rewrite inE => ->.
  by rewrite mem_pblock hcov inE.
exists P; split => // M hM v; rewrite (subdeg_loopless _ _ hll).
by apply/eqP; rewrite eqn_leq (hmatch M v hM) (hge M v hM).
Qed.

(** In a loopless [k]-regular class-1 multigraph every ODD vertex set has an
    edge cut of at least [k] edges: the [k] colour classes are perfect
    matchings, each meets the cut in an ODD ([pm_cut_parity]) hence positive
    number of edges, and they are pairwise disjoint. *)
Lemma reg_class1_odd_cut (G : mgraph) (k : nat) (X : {set G}) :
  loopless G -> (forall v : G, mdeg v = k) -> chromatic_index G = k ->
  odd #|X| -> (k <= #|cut X|)%N.
Proof.
move=> hll hreg hci hX.
have [P [hPk hpart hpm]] := class1_pm_partition hll hreg hci.
have htriv : trivIset P by have [_ h _] := and3P hpart.
have hcov : cover P = [set: edge G] := cover_partition hpart.
have hsum : \sum_(M in P) #|M :&: cut X| = #|cut X|.
  transitivity (\sum_(M in P) \sum_(e in cut X) (e \in M)).
    by apply: eq_bigr => M _; rewrite setIC card_setI_sum.
  rewrite exchange_big /= -sum1_card.
  apply: eq_bigr => e he.
  have hb : pblock P e \in P by rewrite pblock_mem // hcov inE.
  rewrite (bigD1 (pblock P e) hb) /=.
  have -> : (e \in pblock P e) = true by rewrite mem_pblock hcov inE.
  rewrite big1 //= => M /andP[hM hne].
  apply/eqP; rewrite eqb0; apply/negP => heM.
  by move: hne; rewrite (def_pblock htriv hM heM) eqxx.
rewrite -hsum -hPk -sum1_card.
apply: leq_sum => M hM.
have hodd : odd #|M :&: cut X|.
  by rewrite (@pm_cut_parity _ M X (hpm M hM)).
rewrite lt0n; apply/negP => /eqP h0.
by rewrite h0 in hodd.
Qed.

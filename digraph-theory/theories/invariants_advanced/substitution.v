(** * Digraph.substitution — the substitution lower bound

    The first marquee theorem of the library (paper "Substitution lower
    bound"; docs/DESIGN.md §6):

        ω̄(S) + ω̄(H)  ≤  ω̄(S[H]) + 1        (S, H nonempty)

    i.e. ω̄(S[H]) ≥ ω̄(S) + ω̄(H) − 1, stated subtraction-free.

    Proof, for an arbitrary order [p] on S[H]: each block {s}×H carries the
    order induced by [p], and the blocks themselves are ordered by the
    position of their ≺ₚ-minimum ([posmin], realized as a permutation of S
    via [realize]). Take a maximum backedge clique [KS] of that block order
    (≥ ω̄(S) blocks) and let [sa] be its ≺-last block. Then:
    - the block-minimum representatives of the other [KS]-blocks, and
    - a full maximum backedge clique of the induced order on block [sa]
      (≥ ω̄(H) vertices, "promote the last block"),
    form a backedge clique of [p]: cross-block pairs are backedges because
    representatives sit at block-minimal positions and arcs between
    [KS]-blocks point ≺-backwards ([cross_edgeE]); intra-block pairs reduce
    to the H-clique ([block_edgeE]). Size: (ω̄(S) − 1) + ω̄(H). *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude interop_graph_theory digraph tournament order.
From Digraph Require Import omegabar.
From Digraph Require Import product.
Set SsrOldRewriteGoalsOrder.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Substitution.
Variables S H : tournament.
Hypothesis Spos : 0 < #|S|.
Hypothesis Hpos : 0 < #|H|.

Section WithOrder.
Variable p : {perm lexprod S H}.

Local Notation pos := (fun u : lexprod S H => val (enum_rank (p u))).

Let h0 : H := enum_val (Ordinal Hpos).

(** The ≺ₚ-minimum of a block, and its position. *)
Definition hmin (s : S) : H := [arg min_(h < h0) pos (s, h)].
Definition posmin (s : S) : nat := pos (s, hmin s).

Lemma posmin_le (s : S) (h : H) : posmin s <= pos (s, h).
Proof. by rewrite /posmin /hmin; case: arg_minnP => // m _; apply. Qed.

Lemma pos_inj (u v : lexprod S H) : pos u = pos v -> u = v.
Proof. by move/val_inj/enum_rank_inj/perm_inj. Qed.

Lemma posmin_neq (s s' : S) : s != s' -> posmin s != posmin s'.
Proof.
move=> sDs'; apply/eqP=> /pos_inj e.
by move/eqP: sDs'; case: e => ->.
Qed.

(** The block order on S, realized as a permutation. *)
Let rS := [rel s s' : S | posmin s < posmin s'].
Fact rS_irr : irreflexive rS. Proof. by move=> s /=; rewrite ltnn. Qed.
Fact rS_trans : transitive rS. Proof. by move=> a b c /=; apply: ltn_trans. Qed.
Fact rS_total (s s' : S) : s != s' -> rS s s' || rS s' s.
Proof. by move=> sDs'; rewrite /= -neq_ltn posmin_neq. Qed.

Let qS : {perm S} := realize rS.
Let qSE := ltp_realizeE rS_irr rS_trans rS_total.

(** The order induced by [p] inside block [s]. *)
Let rH (s : S) := [rel h h' : H | pos (s, h) < pos (s, h')].
Fact rH_irr (s : S) : irreflexive (rH s).
Proof. by move=> h /=; rewrite ltnn. Qed.
Fact rH_trans (s : S) : transitive (rH s).
Proof. by move=> a b c /=; apply: ltn_trans. Qed.
Fact rH_total (s : S) (h h' : H) : h != h' -> rH s h h' || rH s h' h.
Proof.
move=> hDh'; rewrite /= -neq_ltn; apply/eqP=> /pos_inj e.
by move/eqP: hDh'; case: e => ->.
Qed.

Let qH (s : S) : {perm H} := realize (rH s).
Let qHE (s : S) := ltp_realizeE (@rH_irr s) (@rH_trans s) (@rH_total s).

(** Edge correspondences between [backedge p] and the auxiliary graphs. *)

Lemma cross_edgeE (s s' : S) (h h' : H) : s != s' -> s' --> s ->
  (((s, h) : backedge p) -- (((s', h') : lexprod S H) : backedge p))
  = (pos (s, h) < pos (s', h')).
Proof.
move=> sDs' arc_s's.
rewrite backedgeE !lexprod_arcE /= (negbTE sDs') eq_sym (negbTE sDs') /=.
by rewrite arc_s's (negbTE (arc_asym arc_s's)) /= andbT andbF orbF.
Qed.

Lemma block_edgeE (s : S) (h h' : H) :
  (((s, h) : backedge p) -- (((s, h') : lexprod S H) : backedge p))
  = ((h : backedge (qH s)) -- (h' : backedge (qH s))).
Proof. by rewrite !backedgeE !lexprod_arcE /= eqxx !arcxx /= !qHE. Qed.

(** The bound, for this arbitrary order. *)
Lemma omegab_at_lexprod_ge : ω̄(S) + ω̄(H) <= omegab_at p + 1.
Proof.
have oS : ω̄(S) <= omegab_at qS := omegabar_min qS.
rewrite /omegab_at in oS; case: omegaP oS => KS KSmax oS.
have KS_cl := maxclique_clique KSmax.
have KSpos : 0 < #|KS| by apply: leq_trans oS; apply: omegabar_gt0.
have [s0 s0KS] := card_gt0P KSpos.
have [sa saKS samax] := arg_maxnP posmin s0KS.
have oH : ω̄(H) <= omegab_at (qH sa) := omegabar_min (qH sa).
rewrite /omegab_at in oH; case: omegaP oH => KH KHmax oH.
have KH_cl := maxclique_clique KHmax.
pose RR : {set lexprod S H} := [set (s, hmin s) | s in KS :\ sa].
pose BB : {set lexprod S H} := [set (sa, h) | h in KH].
have RRBB0 : RR :&: BB = set0.
  apply/eqP; rewrite setI_eq0; apply/pred0P=> u /=.
  apply/negP=> /andP[/imsetP[s sKS ->] /imsetP[h _ [e _]]].
  by move: sKS; rewrite !inE e eqxx.
have cardRR : #|RR| = #|KS|.-1.
  rewrite card_imset; last by move=> a b [].
  by move: (cardsD1 sa KS); rewrite (saKS : sa \in KS) add1n => ->.
have cardBB : #|BB| = #|KH|.
  by rewrite card_imset //; move=> a b [].
have cardKK : #|RR :|: BB| = #|KS|.-1 + #|KH|.
  by rewrite cardsU RRBB0 cards0 subn0 cardRR cardBB.
have rep_lt (s : S) : s \in KS :\ sa -> posmin s < posmin sa.
  rewrite !inE => /andP[sDsa sKS].
  rewrite ltn_neqAle posmin_neq //=; exact: samax.
have rep_arc (s : S) : s \in KS :\ sa -> sa --> s.
  move=> sD; have lt := rep_lt _ sD.
  move: sD; rewrite !inE => /andP[sDsa sKS].
  have := KS_cl _ _ sKS (saKS : sa \in KS) sDsa.
  by rewrite backedgeE !qSE /= lt (leq_gtF (ltnW lt)) /= orbF.
have repblock (s : S) (h : H) : s \in KS :\ sa -> h \in KH ->
    (((s, hmin s) : backedge p) -- (((sa, h) : lexprod S H) : backedge p)).
  move=> sD hKH.
  have sDsa : s != sa by move: sD; rewrite !inE => /andP[].
  rewrite (cross_edgeE _ _ sDsa (rep_arc _ sD)).
  exact: leq_trans (rep_lt _ sD) (posmin_le sa h).
have reprep (s s' : S) : s \in KS :\ sa -> s' \in KS :\ sa -> s != s' ->
    (((s, hmin s) : backedge p) -- (((s', hmin s') : lexprod S H) : backedge p)).
  move=> sD s'D sDs'.
  have sKS : s \in KS by move: sD; rewrite !inE => /andP[].
  have s'KS : s' \in KS by move: s'D; rewrite !inE => /andP[].
  have := KS_cl _ _ sKS s'KS sDs'.
  rewrite backedgeE !qSE => /orP[/andP[l a]|/andP[l a]].
  - by rewrite (cross_edgeE _ _ sDs' a).
  - by rewrite sg_sym (cross_edgeE _ _ _ a) // eq_sym.
have KKcliq : RR :|: BB \in cliques [set: backedge p].
  rewrite inE subsetT /=; apply/cliqueP=> u v.
  move=> /setUP[/imsetP[s sD ->]|/imsetP[h hKH ->]]
         /setUP[/imsetP[s' s'D ->]|/imsetP[h' h'KH ->]] neq.
  - by apply: reprep => //; apply: contraNneq neq => ->.
  - exact: repblock.
  - by rewrite sg_sym; apply: repblock.
  - have hDh' : h != h' by apply: contraNneq neq => ->.
    by rewrite block_edgeE; apply: KH_cl.
have bound := clique_bound KKcliq.
apply: leq_trans (leq_add oS oH) _.
rewrite -(prednK KSpos) addSn addn1 ltnS -cardKK.
exact: bound.
Qed.

End WithOrder.

(** The substitution lower bound: ω̄(S[H]) ≥ ω̄(S) + ω̄(H) − 1. *)
Theorem omegabar_lexprod_ge :
  ω̄(S) + ω̄(H) <= ω̄(lexprod_tournament S H) + 1.
Proof.
have [p obp] := omegabar_witness (lexprod_tournament S H).
rewrite obp; exact: omegab_at_lexprod_ge.
Qed.

End Substitution.

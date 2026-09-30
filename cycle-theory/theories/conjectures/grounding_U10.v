(** * Cycle.conjectures.grounding_U10 — grounding lemmas for milestone U10

    Qed-closed, axiom-free sanity results for the new primitives introduced in
    [Cycle.conjectures.U10] (perfect matchings, the Petersen / Kneser graph
    KG(5,2), odd edge-cuts).  For each primitive we provide:
      - a SATISFIABLE witness (the predicate is inhabited / non-contradictory);
      - at least one textbook IDENTITY it must satisfy.

    Witness models used:
      - [Ge]: the single-edge graph on 2 vertices ([inl tt -- inr tt]).  Its one
        edge meets each vertex exactly once, so [[set: edge Ge]] is a PERFECT
        MATCHING, [[:: setT; setT]] is a perfect-matching double cover, and the
        cut [cut [set inl tt]] of one endpoint is an ODD edge-cut (cardinality 1).
      - [Gt]: the triple-edge dipole on 2 vertices (3 parallel edges
        [inl tt -- inr tt]).  This is the SMALLEST bridgeless cubic multigraph;
        it is the non-vacuity witness that [cubic_bridgeless] is inhabited.
      - The Petersen vertices [pv01,pv23,pv24,pv34] (2-subsets of ['I_5]) and the
        Petersen edges [Pe_a,Pe_b,Pe_c] (a star centred at [pv01]) ground
        [petersenV], [padj], [petersen], [Pedge], [psupp], [Padj] and [mut_adj3].

    Everything below is [Qed]-closed and (by [Print Assumptions]) closed under the
    global context — no [Axiom]/[Parameter]/[Admitted]. *)

From GraphTheory Require Import mgraph sgraph.
From GTBase Require Import base.
From Cycle.conjectures Require Import U6 U10.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ================================================================= *)
(** ** The single-edge witness graph [Ge] (perfect matchings, odd cuts) *)

Definition Ge0 : mgraph := two_graph tt tt.
Definition Ge : mgraph := mgraph.add_edge Ge0 (inl tt) (inr tt) tt.

Lemma card_edge_Ge : #|edge Ge| = 1.
Proof. by rewrite /Ge /Ge0 card_option card_sum !card_void. Qed.

Lemma inc_all_Ge (v : Ge) (e : edge Ge) : incident v e.
Proof.
rewrite /incident; apply/existsP.
case: e => [[]|]; case: v => -[];
  first [ by move=> a; case: a | by exists false | by exists true ].
Qed.

Lemma edges_at_Ge (v : Ge) : edges_at v = [set: edge Ge].
Proof. by apply/setP => e; rewrite !inE inc_all_Ge. Qed.

(** [Ge] is LOOPLESS, so the arc-end degree [subdeg] agrees with the incidence
    count (a loop would count twice). *)
Lemma loopless_Ge : loopless Ge.
Proof. by case=> [[[]|[]]|]. Qed.

Lemma subdeg_Ge (H : {set edge Ge}) (v : Ge) : subdeg H v = #|H|.
Proof. by rewrite (subdeg_loopless _ _ loopless_Ge) edges_at_Ge setTI. Qed.

Lemma src_Ge (e : edge Ge) : source e = inl tt.
Proof. by do ![case: e => [e|] //=]. Qed.

Lemma tgt_Ge (e : edge Ge) : target e = inr tt.
Proof. by do ![case: e => [e|] //=]. Qed.

(** ** [is_perfect_matching] : witness + identity *)

(** WITNESS: the whole (one-edge) edge set is a perfect matching of [Ge]. *)
Lemma is_pm_setT_Ge : is_perfect_matching [set: edge Ge].
Proof. by move=> v; rewrite subdeg_Ge cardsT card_edge_Ge. Qed.

(** IDENTITY: a perfect matching is in particular a (U6-)matching. *)
Lemma is_pm_is_matching (G : mgraph) (M : {set edge G}) :
  is_perfect_matching M -> is_matching M.
Proof. by move=> H v; rewrite H. Qed.

(** ** [perfect_matching_cover] : witness + identity *)

(** IDENTITY: a [k]-cover has exactly [k] members. *)
Lemma pmc_size (G : mgraph) (k : nat) (L : seq {set edge G}) :
  perfect_matching_cover k L -> size L = k.
Proof. by case. Qed.

(** WITNESS: in [Ge] the unique edge, taken twice, is a 2-member double cover. *)
Lemma pmc_Ge : perfect_matching_cover 2 [:: [set: edge Ge]; [set: edge Ge]].
Proof.
split.
- by [].
- by move=> M; rewrite !inE => /orP[]/eqP->; exact: is_pm_setT_Ge.
- by move=> e; rewrite /= !in_setT.
Qed.

(** ** [is_odd_edge_cut] / [contains_odd_edge_cut] : witnesses + identities *)

(** In [Ge] the cut of one endpoint is the whole (one-edge) edge set. *)
Lemma cut_Ge : cut (G:=Ge) [set inl tt] = [set: edge Ge].
Proof. by apply/setP => e; rewrite !inE (src_Ge e) (tgt_Ge e) eqxx. Qed.

(** WITNESS: that cut, of cardinality 1, is an odd edge-cut. *)
Lemma odd_cut_Ge : is_odd_edge_cut (G:=Ge) [set: edge Ge].
Proof.
exists [set inl tt]; split.
- by rewrite cut_Ge.
- by rewrite -card_gt0 cardsT card_edge_Ge.
- by rewrite cardsT card_edge_Ge.
Qed.

(** IDENTITY: an odd edge-cut has odd cardinality. *)
Lemma odd_cut_odd (G : mgraph) (T : {set edge G}) :
  is_odd_edge_cut T -> odd #|T|.
Proof. by case=> S [_ _]. Qed.

(** IDENTITY: an odd edge-cut is nonempty.  (Witnesses the remark in [U10] that
    the [T != set0] conjunct is redundant: [odd #|T|] already forces it, since
    [odd #|set0| = false].) *)
Lemma is_odd_edge_cut_neq0 (G : mgraph) (T : {set edge G}) :
  is_odd_edge_cut T -> T != set0.
Proof. by move/odd_cut_odd; apply: contraTneq => ->; rewrite cards0. Qed.

(** IDENTITY: an odd edge-cut contains itself (it is its own odd subcut). *)
Lemma odd_cut_contains (G : mgraph) (H : {set edge G}) :
  is_odd_edge_cut H -> contains_odd_edge_cut H.
Proof. by exists H; split; [exact: subxx |]. Qed.

(** WITNESS: [[set: edge Ge]] contains an odd edge-cut. *)
Lemma contains_odd_Ge : contains_odd_edge_cut (G:=Ge) [set: edge Ge].
Proof. exact: odd_cut_contains odd_cut_Ge. Qed.

(** ================================================================= *)
(** ** The triple-edge dipole [Gt] (a bridgeless cubic multigraph) *)

Definition Gt0 : mgraph := two_graph tt tt.
Definition Gt1 : mgraph := mgraph.add_edge Gt0 (inl tt) (inr tt) tt.
Definition Gt2 : mgraph := mgraph.add_edge Gt1 (inl tt) (inr tt) tt.
Definition Gt  : mgraph := mgraph.add_edge Gt2 (inl tt) (inr tt) tt.

Lemma card_edge_Gt : #|edge Gt| = 3.
Proof. by rewrite /Gt /Gt2 /Gt1 /Gt0 !card_option card_sum !card_void. Qed.

Lemma src_Gt (e : edge Gt) : source e = inl tt.
Proof. by do ![case: e => [e|] //=]. Qed.

Lemma tgt_Gt (e : edge Gt) : target e = inr tt.
Proof. by do ![case: e => [e|] //=]. Qed.

Lemma loopless_Gt : loopless Gt.
Proof. by move=> e; rewrite (src_Gt e) (tgt_Gt e). Qed.

Lemma inc_all_Gt (v : Gt) (e : edge Gt) : incident v e.
Proof.
rewrite /incident; apply/existsP; case: v => -[].
- by exists false; rewrite (src_Gt e).
- by exists true; rewrite (tgt_Gt e).
Qed.

Lemma edges_at_Gt (v : Gt) : edges_at v = [set: edge Gt].
Proof. by apply/setP => e; rewrite !inE inc_all_Gt. Qed.

Lemma mdeg_Gt (v : Gt) : mdeg v = 3.
Proof. by rewrite (mdeg_loopless _ loopless_Gt) edges_at_Gt cardsT card_edge_Gt. Qed.

Lemma cubic_Gt : cubic Gt.
Proof. by split; [exact: loopless_Gt | exact: mdeg_Gt]. Qed.

Lemma bridgeless_Gt : bridgeless Gt.
Proof.
move=> e He.
pose e' : edge Gt := if e == None then Some None else None.
have ne : e' != e.
  rewrite /e'; case: ifPn => [/eqP -> // | hne].
  by rewrite eq_sym.
have hw : uwalk (source e) (target e) [:: e'].
  by apply: uwalk_one; [rewrite (src_Gt e') (src_Gt e) | rewrite (tgt_Gt e') (tgt_Gt e)].
case: (He _ hw) => f; rewrite inE => /eqP ->; rewrite mem_seq1 => /eqP ef.
by move: ne; rewrite ef eqxx.
Qed.

(** ** [cubic_bridgeless] : witness + identities *)

(** WITNESS: the triple-edge dipole is bridgeless and cubic (non-vacuity guard
    for all three rows: the hypothesis class is genuinely inhabited). *)
Lemma cubic_bridgeless_Gt : cubic_bridgeless Gt.
Proof. by split; [exact: cubic_Gt | exact: bridgeless_Gt]. Qed.

(** IDENTITIES: the two projections. *)
Lemma cubic_bridgeless_cubic (G : mgraph) : cubic_bridgeless G -> cubic G.
Proof. by case. Qed.

Lemma cubic_bridgeless_bridgeless (G : mgraph) :
  cubic_bridgeless G -> bridgeless G.
Proof. by case. Qed.

(** ================================================================= *)
(** ** The Petersen / Kneser graph KG(5,2) *)

(** Four concrete 2-subsets of ['I_5]. *)
Notation O5 i := (@Ordinal 5 i isT).

Lemma c01 : #|[set O5 0; O5 1]| == 2. Proof. by rewrite cards2. Qed.
Lemma c23 : #|[set O5 2; O5 3]| == 2. Proof. by rewrite cards2. Qed.
Lemma c24 : #|[set O5 2; O5 4]| == 2. Proof. by rewrite cards2. Qed.
Lemma c34 : #|[set O5 3; O5 4]| == 2. Proof. by rewrite cards2. Qed.

Definition pv01 : petersenV := Sub [set O5 0; O5 1] c01.
Definition pv23 : petersenV := Sub [set O5 2; O5 3] c23.
Definition pv24 : petersenV := Sub [set O5 2; O5 4] c24.
Definition pv34 : petersenV := Sub [set O5 3; O5 4] c34.

(** ** [petersenV] : witness ([pv01]) + identity (10 vertices) *)

(** IDENTITY: the Petersen graph has exactly 10 vertices ['C(5,2)]. *)
Lemma card_petersenV : #|petersenV| = 10.
Proof. by rewrite card_sig -cardsE card_draws card_ord. Qed.

(** ** [padj] : witnesses + identities *)

(** WITNESSES: pairwise-disjoint 2-subsets are [padj]-adjacent. *)
Lemma pj_01_23 : padj pv01 pv23.
Proof.
by rewrite /padj !SubK -setI_eq0; apply/eqP/setP => z;
  rewrite !inE -!val_eqE /=; case: (val z) => [|[|[|[|[|n]]]]].
Qed.

Lemma pj_01_24 : padj pv01 pv24.
Proof.
by rewrite /padj !SubK -setI_eq0; apply/eqP/setP => z;
  rewrite !inE -!val_eqE /=; case: (val z) => [|[|[|[|[|n]]]]].
Qed.

Lemma pj_01_34 : padj pv01 pv34.
Proof.
by rewrite /padj !SubK -setI_eq0; apply/eqP/setP => z;
  rewrite !inE -!val_eqE /=; case: (val z) => [|[|[|[|[|n]]]]].
Qed.

(** IDENTITY: adjacent Kneser vertices are distinct ([padj] is irreflexive,
    re-using U10's [padj_irrefl]). *)
Lemma padj_neq (x y : petersenV) : padj x y -> x != y.
Proof. by move=> H; apply/negP => /eqP exy; move: H; rewrite exy padj_irrefl. Qed.

(** ** [petersen] : witness ([pv01] adjacent to [pv23] in the sgraph) *)
Lemma petersen_adj : (pv01 : petersen) -- pv23.
Proof. exact: pj_01_23. Qed.

(** ** [Pedge] : witnesses (a star of three edges centred at [pv01]) *)
Definition Pe_a : Pedge := Sub (pv01, pv23) pj_01_23.
Definition Pe_b : Pedge := Sub (pv01, pv24) pj_01_24.
Definition Pe_c : Pedge := Sub (pv01, pv34) pj_01_34.

(** ** [psupp] : identity (every Petersen edge has a 2-element support) *)
Lemma psupp_card (q : Pedge) : #|psupp q| = 2.
Proof. by rewrite /psupp cards2 (padj_neq (valP q)). Qed.

Lemma psupp_a : psupp Pe_a = [set pv01; pv23].
Proof. by rewrite /psupp SubK. Qed.
Lemma psupp_b : psupp Pe_b = [set pv01; pv24].
Proof. by rewrite /psupp SubK. Qed.
Lemma psupp_c : psupp Pe_c = [set pv01; pv34].
Proof. by rewrite /psupp SubK. Qed.

(** Distinctness of the four Kneser vertices used above. *)
Lemma pv23_neq_pv01 : pv23 != pv01.
Proof. by apply/eqP => /(congr1 val); rewrite !SubK => /setP/(_ (O5 2)); rewrite !inE -!val_eqE. Qed.
Lemma pv24_neq_pv01 : pv24 != pv01.
Proof. by apply/eqP => /(congr1 val); rewrite !SubK => /setP/(_ (O5 2)); rewrite !inE -!val_eqE. Qed.
Lemma pv34_neq_pv01 : pv34 != pv01.
Proof. by apply/eqP => /(congr1 val); rewrite !SubK => /setP/(_ (O5 3)); rewrite !inE -!val_eqE. Qed.
Lemma pv23_neq_pv24 : pv23 != pv24.
Proof. by apply/eqP => /(congr1 val); rewrite !SubK => /setP/(_ (O5 3)); rewrite !inE -!val_eqE. Qed.
Lemma pv23_neq_pv34 : pv23 != pv34.
Proof. by apply/eqP => /(congr1 val); rewrite !SubK => /setP/(_ (O5 2)); rewrite !inE -!val_eqE. Qed.
Lemma pv24_neq_pv34 : pv24 != pv34.
Proof. by apply/eqP => /(congr1 val); rewrite !SubK => /setP/(_ (O5 2)); rewrite !inE -!val_eqE. Qed.

(** ** [Padj] : witnesses + identity *)

(** IDENTITY: edge-adjacency in the Petersen graph is irreflexive. *)
Lemma Padj_irrefl (q : Pedge) : Padj q q = false.
Proof. by rewrite /Padj eqxx. Qed.

(** WITNESSES: the three star edges are pairwise [Padj]-adjacent (they share the
    centre [pv01] and have distinct supports). *)
Lemma Padj_ab : Padj Pe_a Pe_b.
Proof.
rewrite /Padj psupp_a psupp_b; apply/andP; split.
- apply/eqP => /setP/(_ pv23).
  by rewrite !inE eqxx orbT (negbTE pv23_neq_pv01) (negbTE pv23_neq_pv24).
- by apply/set0Pn; exists pv01; rewrite !inE !eqxx.
Qed.

Lemma Padj_bc : Padj Pe_b Pe_c.
Proof.
rewrite /Padj psupp_b psupp_c; apply/andP; split.
- apply/eqP => /setP/(_ pv24).
  by rewrite !inE eqxx orbT (negbTE pv24_neq_pv01) (negbTE pv24_neq_pv34).
- by apply/set0Pn; exists pv01; rewrite !inE !eqxx.
Qed.

Lemma Padj_ac : Padj Pe_a Pe_c.
Proof.
rewrite /Padj psupp_a psupp_c; apply/andP; split.
- apply/eqP => /setP/(_ pv23).
  by rewrite !inE eqxx orbT (negbTE pv23_neq_pv01) (negbTE pv23_neq_pv34).
- by apply/set0Pn; exists pv01; rewrite !inE !eqxx.
Qed.

(** ** [mut_adj3] : witnesses + identity *)

(** WITNESS: the three star edges are mutually adjacent (the codomain shape that
    a Petersen colouring must produce). *)
Lemma mut_adj3_star : mut_adj3 Padj Pe_a Pe_b Pe_c.
Proof. by rewrite /mut_adj3 Padj_ab Padj_bc Padj_ac. Qed.

(** IDENTITY: a mutually-adjacent triple is, in particular, pairwise related. *)
Lemma mut_adj3_l (T : Type) (r : rel T) (a b c : T) :
  mut_adj3 r a b c -> r a b.
Proof. by case/and3P. Qed.

(** WITNESS: any triple is mutually adjacent under the always-true relation. *)
Lemma mut_adj3_true (T : Type) (a b c : T) :
  mut_adj3 (fun _ _ => true) a b c.
Proof. by []. Qed.

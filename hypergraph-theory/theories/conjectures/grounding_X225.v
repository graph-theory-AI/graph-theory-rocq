(** * Hypergraph.conjectures.grounding_X225 -- grounding lemmas for wave X225

    Qed-closed, axiom-free sanity results for the four X225 statements and for
    the primitives they use ([hg_loopless], [hg_has_clique_minor],
    [hg_colourable], [hg_turan], [hg_dmax] in
    [Hypergraph.foundations.hypergraph]; [x225_latin_square] /
    [x225_latin_hypergraph] in [Hypergraph.conjectures.X225]).

    Per statement:
    - NON-VACUITY: the hypotheses are satisfiable together and the conclusion is
      attainable (a loopless K_3-minor-free 3-colourable hypergraph; a
      2-uniform 2-partite pattern with a hyperedge; a 2 x 2 Latin square whose
      hypergraph H_L is 3-uniform and non-empty).
    - GUARD-HAS-TEETH: dropping [hg_loopless] makes rows #00/#01 FALSE (the
      one-vertex hypergraph whose only hyperedge is empty has no minor and no
      proper colouring); dropping the K_3-minor hypothesis makes row #01 FALSE
      (K_4, which HAS a K_3 minor, is loopless and not 3-colourable); dropping
      [F != set0] makes row 2401.00359#01 FALSE (the empty pattern has
      [d_max = 0] and Turan number 0, so the cleared inequality degenerates to
      [n^{c_k} <= K]); dropping [x225_latin_square] admits constant "squares".
    - SETTLED CASE recorded by the source: the tightness half of Conjecture 2 at
      [t = 2], i.e. [h(2) >= ceil(3/2) = 2] -- the 3-uniform hypergraph with a
      single hyperedge is K_2-minor-free and not 1-colourable.  This is also the
      cross-check that fixes the branch-set connectivity convention. *)

From GTBase Require Import base.
From Hypergraph.foundations Require Import hypergraph.
From Hypergraph.conjectures Require Import X225.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation x225_I2 i := (@Ordinal 2 i isT).

Lemma x225_widen_inj (n m : nat) (le : n <= m) : injective (widen_ord le).
Proof. by move=> x y /(congr1 val) /= /val_inj. Qed.

Lemma x225_ord2 (i : 'I_2) : (i = ord0) \/ (i = x225_I2 1).
Proof. by case: i => -[|[|m]] Hm; [left|right|]; try exact: val_inj. Qed.

Lemma x225_ord2_neq : (ord0 : 'I_2) != x225_I2 1.
Proof. by apply/eqP => /(congr1 val). Qed.

(** ** Rows arxiv:2206.13635#00 / #01 -- non-vacuity *)

(** A single 2-element hyperedge on two vertices. *)
Definition x225_edge2 : {set {set 'I_2}} := [set [set: 'I_2]].

Lemma x225_edge2_loopless : hg_loopless x225_edge2.
Proof. by move=> e; rewrite inE => /eqP->; rewrite cardsT card_ord. Qed.

Lemma x225_edge2_no_k3_minor : ~ hg_has_clique_minor x225_edge2 3.
Proof. by move/hg_minor_card; rewrite card_ord. Qed.

Lemma x225_edge2_colourable : hg_colourable x225_edge2 3.
Proof.
exists (fun v : 'I_2 => if v == ord0 then x225_I3 0 else x225_I3 1).
move=> e; rewrite inE => /eqP->.
by exists ord0, (x225_I2 1); split; rewrite ?inE.
Qed.

(** NON-VACUITY: the hypotheses of row #01 are satisfiable and its conclusion
    holds there, so the statement is not empty. *)
Lemma x225_minor_hypotheses_satisfiable :
  [/\ hg_loopless x225_edge2,
      ~ hg_has_clique_minor x225_edge2 3 &
      hg_colourable x225_edge2 3].
Proof.
split; [exact: x225_edge2_loopless | exact: x225_edge2_no_k3_minor |
        exact: x225_edge2_colourable].
Qed.

(** ** The looplessness guard has teeth *)

(** One vertex, one EMPTY hyperedge: no minor, and no proper colouring at all. *)
Definition x225_empty_edge : {set {set 'I_1}} := [set set0].

Lemma x225_empty_edge_not_loopless : ~ hg_loopless x225_empty_edge.
Proof. by move/(_ set0); rewrite inE eqxx cards0 => /(_ isT). Qed.

Lemma x225_empty_edge_no_minor t : 1 < t -> ~ hg_has_clique_minor x225_empty_edge t.
Proof. by move=> t1 /hg_minor_card; rewrite card_ord leqNgt t1. Qed.

Lemma x225_empty_edge_not_colourable m : ~ hg_colourable x225_empty_edge m.
Proof.
case=> col /(_ set0); rewrite inE eqxx => /(_ isT)[x [y [xe _ _]]].
by rewrite inE in xe.
Qed.

Lemma x225_loopless_guard_has_teeth :
  [/\ ~ hg_loopless x225_empty_edge,
      ~ hg_has_clique_minor x225_empty_edge 3 &
      ~ hg_colourable x225_empty_edge 3].
Proof.
split; [exact: x225_empty_edge_not_loopless | exact: x225_empty_edge_no_minor |
        exact: x225_empty_edge_not_colourable].
Qed.

(** ** The K_3-minor guard has teeth: K_4 is loopless, has a K_3 minor, and is
    not 3-colourable. *)

Definition x225_K4 : {set {set 'I_4}} := [set e : {set 'I_4} | #|e| == 2].

Lemma x225_K4_loopless : hg_loopless x225_K4.
Proof. by move=> e; rewrite inE => /eqP->. Qed.

Lemma x225_K4_edge (x y : 'I_4) : x != y -> [set x; y] \in x225_K4.
Proof. by move=> xy; rewrite inE cards2 xy. Qed.

Lemma x225_K4_not_colourable : ~ hg_colourable x225_K4 3.
Proof.
case=> col colP.
have /injectivePn[x [y xy cxy]] : ~~ injectiveb col.
  by apply/negP => /injectiveP/leq_card; rewrite !card_ord.
have [u [w [uxy wxy cuw]]] := colP _ (x225_K4_edge xy).
move: uxy wxy cuw; rewrite !inE.
by case/orP => /eqP->; case/orP => /eqP->; rewrite ?cxy eqxx.
Qed.

Lemma x225_K4_has_k3_minor : hg_has_clique_minor x225_K4 3.
Proof.
pose w (h : 'I_3) : 'I_4 := widen_ord (isT : 3 <= 4) h.
have wneq (h h' : 'I_3) : h != h' -> w h != w h'.
  by apply: contra => /eqP/x225_widen_inj->.
exists (fun h => [set w h]); split.
  split.
  - by move=> h; apply/set0Pn; exists (w h); rewrite inE eqxx.
  - by move=> h h' hh'; rewrite disjoints1 inE wneq.
  - by move=> h u v; rewrite !inE => /eqP-> /eqP->; exact: connect0.
move=> h h' hh'; exists [set w h; w h']; split.
- exact: x225_K4_edge (wneq _ _ hh').
- by [].
- by apply/set0Pn; exists (w h); rewrite !inE eqxx.
- by apply/set0Pn; exists (w h'); rewrite !inE eqxx orbT.
Qed.

Lemma x225_minor_guard_has_teeth :
  [/\ hg_loopless x225_K4, hg_has_clique_minor x225_K4 3 &
      ~ hg_colourable x225_K4 3].
Proof.
split; [exact: x225_K4_loopless | exact: x225_K4_has_k3_minor |
        exact: x225_K4_not_colourable].
Qed.

(** ** Settled case: the tightness half of Conjecture 2 at [t = 2] *)

(** Three vertices, a single 3-element hyperedge. *)
Definition x225_triple : {set {set 'I_3}} := [set [set: 'I_3]].

Lemma x225_triple_loopless : hg_loopless x225_triple.
Proof. by move=> e; rewrite inE => /eqP->; rewrite cardsT card_ord. Qed.

Lemma x225_triple_not_1_colourable : ~ hg_colourable x225_triple 1.
Proof.
case=> col /(_ [set: 'I_3]); rewrite inE eqxx => /(_ isT)[x [y [_ _]]].
by rewrite (ord1 (col x)) (ord1 (col y)) eqxx.
Qed.

Lemma x225_triple_no_k2_minor : ~ hg_has_clique_minor x225_triple 2.
Proof.
case=> B [[Bne Bdis Bcon] Bjoin].
have small (h h' : 'I_2) : h != h' -> #|B h| <= 1.
  move=> hh'; rewrite leqNgt; apply/negP => /card_gt1P[u [v [uB vB uv]]].
  have restr : hg_restrict x225_triple (B h) = set0.
    apply/setP => f; rewrite !inE; apply/negbTE; apply/negP => /andP[/eqP fT sub].
    have [z zB'] : exists z, z \in B h' by apply/set0Pn; exact: Bne.
    have zBh : z \in B h by apply: (subsetP sub); rewrite fT inE.
    by have := Bdis _ _ hh'; rewrite -setI_eq0 => /eqP/setP/(_ z); rewrite !inE zBh zB'.
  move: (Bcon h u v uB vB); rewrite restr => /hg_connect0 uv'.
  by rewrite uv' eqxx in uv.
have [e [eE esub _ _]] := Bjoin ord0 (x225_I2 1) x225_ord2_neq.
move: eE; rewrite inE => /eqP eT.
have cover : #|[set: 'I_3]| <= #|B ord0| + #|B (x225_I2 1)|.
  apply: leq_trans (leq_card_setU (B ord0) (B (x225_I2 1))).1.
  by apply: subset_leq_card; rewrite -eT.
move: cover; rewrite cardsT card_ord => H3.
have s0 := small ord0 (x225_I2 1) x225_ord2_neq.
have s1 : #|B (x225_I2 1)| <= 1 by apply: (small _ ord0); rewrite eq_sym x225_ord2_neq.
by move: (leq_trans H3 (leq_add s0 s1)).
Qed.

(** The source proves h(2) >= 2 = ceil(3(2-1)/2) by an explicit construction;
    this is that construction, and the reason the branch sets of
    [hg_has_clique_minor] must be connected INSIDE themselves. *)
Lemma x225_conj2_tight_at_two :
  exists (T : finType) (E : {set {set T}}),
    [/\ hg_loopless E,
        ~ hg_has_clique_minor E 2 &
        ~ hg_colourable E (ceil_div (3 * 2.-1) 2).-1].
Proof.
exists ('I_3 : finType), x225_triple; split.
- exact: x225_triple_loopless.
- exact: x225_triple_no_k2_minor.
- exact: x225_triple_not_1_colourable.
Qed.

(** ** Row arxiv:2401.00359#01 -- non-vacuity of the k-partite hypotheses *)

Lemma x225_pattern2_nonempty : x225_edge2 != set0.
Proof. by apply/set0Pn; exists [set: 'I_2]; rewrite inE eqxx. Qed.

Lemma x225_pattern2_uniform : hg_uniform x225_edge2 2.
Proof. by move=> e; rewrite inE => /eqP->; rewrite cardsT card_ord. Qed.

Lemma x225_pattern2_partite : hg_partite_uniform (fun v : 'I_2 => v) x225_edge2.
Proof.
move=> e; rewrite inE => /eqP-> j.
have -> : [set v in [set: 'I_2] | v == j] = [set j] by apply/setP => v; rewrite !inE.
by rewrite cards1.
Qed.

Lemma x225_turan_hypotheses_satisfiable :
  [/\ x225_edge2 != set0, hg_uniform x225_edge2 2 &
      hg_partite_uniform (fun v : 'I_2 => v) x225_edge2].
Proof.
split; [exact: x225_pattern2_nonempty | exact: x225_pattern2_uniform |
        exact: x225_pattern2_partite].
Qed.

(** ** The [F != set0] guard has teeth *)

Lemma x225_turan_empty (n : nat) : 1 < n ->
  hg_turan (set0 : {set {set 'I_2}}) 2 n = 0.
Proof.
move=> n1; apply/eqP; rewrite -leqn0 /hg_turan; apply/bigmax_leqP => E.
suff -> : hg_containsb (set0 : {set {set 'I_2}}) E by rewrite andbF.
apply/existsP; exists [ffun i => widen_ord n1 i]; apply/andP; split.
  by apply/injectiveP => x y; rewrite !ffunE => /x225_widen_inj.
by apply/forallP => e; rewrite inE.
Qed.

Lemma x225_empty_pattern_guard_has_teeth (ck K : nat) : 0 < ck ->
  ~ eventually (fun n =>
      (hg_turan (set0 : {set {set 'I_2}}) 2 n) ^ (hg_dmax (set0 : {set {set 'I_2}}) 2)
        * n ^ ck <= K * n ^ (2 * hg_dmax (set0 : {set {set 'I_2}}) 2)).
Proof.
move=> ck0 [N HN].
pose n := maxn N (maxn 2 K.+1).
have nN : N <= n by rewrite leq_maxl.
have n2 : 1 < n by rewrite /n; apply: leq_trans (leq_maxr N _); exact: leq_maxl.
have nK : K < n by rewrite /n; apply: leq_trans (leq_maxr N _); exact: leq_maxr.
move: (HN n nN); rewrite hg_dmax0 x225_turan_empty // expn0 mul1n muln0 expn0 muln1.
move=> Hle; have n0 : 0 < n by apply: ltnW.
have nck : n <= n ^ ck by rewrite -{1}(expn1 n); apply: leq_pexp2l.
by move: (leq_trans nck Hle); rewrite leqNgt nK.
Qed.

(** ** Row arxiv:2401.00359#02 -- a genuine 2 x 2 Latin square *)

Definition x225_L2 (i j : 'I_2) : 'I_2 := if i == ord0 then j else rev_ord j.

Lemma x225_rev2 (j : 'I_2) : rev_ord j != j.
Proof. by case: (x225_ord2 j) => ->; apply/eqP => /(congr1 val). Qed.

Lemma x225_L2_latin : x225_latin_square x225_L2.
Proof.
split => [i|j] x y; rewrite /x225_L2.
  by case: (i == ord0); [|exact: rev_ord_inj].
case: (x225_ord2 x) => ->; case: (x225_ord2 y) => ->;
  rewrite ?eqxx ?(negbTE x225_ord2_neq) //.
  by move=> /eqP; rewrite eq_sym (negbTE (x225_rev2 j)).
by move=> /eqP; rewrite (negbTE (x225_rev2 j)).
Qed.

Lemma x225_latin_hypergraph_nonempty (d : nat) (L : 'I_d -> 'I_d -> 'I_d) :
  0 < d -> x225_latin_hypergraph L != set0.
Proof.
move=> d0; apply/set0Pn.
pose i0 := Ordinal d0.
exists [set (x225_I3 0, i0); (x225_I3 1, i0); (x225_I3 2, L i0 i0)].
by apply: imset2_f; rewrite inE.
Qed.

Lemma x225_latin_hypergraph_uniform (d : nat) (L : 'I_d -> 'I_d -> 'I_d) :
  hg_uniform (x225_latin_hypergraph L) 3.
Proof.
move=> e /imset2P[i j _ _ ->].
rewrite cardsU cards2 cards1 xpair_eqE /=.
have -> : [set (x225_I3 0, i); (x225_I3 1, j)] :&: [set (x225_I3 2, L i j)] = set0.
  apply/setP => v; rewrite !inE; apply/negbTE; apply/negP => /andP[vab /eqP eqv].
  by rewrite eqv !xpair_eqE /= in vab.
by rewrite cards0.
Qed.

Lemma x225_latin_guard_has_teeth : ~ x225_latin_square (fun _ _ : 'I_2 => ord0).
Proof.
case=> H _; move: (H ord0 ord0 (x225_I2 1) (erefl _)).
by move/(congr1 val).
Qed.

Print Assumptions kt_minor_free_hypergraph_chromatic_three_halves_statement.
Print Assumptions k3_minor_free_hypergraph_three_colourable_statement.
Print Assumptions kpartite_hypergraph_turan_exponent_dmax_statement.
Print Assumptions latin_square_hypergraph_turan_exponent_statement.
Print Assumptions x225_minor_hypotheses_satisfiable.
Print Assumptions x225_loopless_guard_has_teeth.
Print Assumptions x225_minor_guard_has_teeth.
Print Assumptions x225_conj2_tight_at_two.
Print Assumptions x225_turan_hypotheses_satisfiable.
Print Assumptions x225_empty_pattern_guard_has_teeth.
Print Assumptions x225_L2_latin.
Print Assumptions x225_latin_hypergraph_uniform.
Print Assumptions x225_latin_guard_has_teeth.

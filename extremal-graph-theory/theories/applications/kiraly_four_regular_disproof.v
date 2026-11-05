(** * Extremal.applications.kiraly_four_regular_disproof -- Kiraly's 4-regular cycle bound is false as printed

    Wave X289, row studies:std_kir_ly_s_cycle_count_conjecture_for_4_regular_gr (PROGRAMME A6).
    [kiraly_four_regular_cycle_count_disproved] refutes [kiraly_four_regular_cycle_count_statement] of
    conjectures/X289.v ("a 4-regular simple graph with m edges has at most 1.99^{m/2} cycles", Kiraly, EGRES
    TR-2009-03, Conjecture 7.14, with no constant) at K_5: it is 4-regular with m = 10 edges and has at least 37
    cycles, while 37^2 * 100^10 > 199^10 (37 > 1.99^5 ~ 31.21).  The asymptotic form of the conjecture holds
    (arXiv:1907.12091v1, Theorem 3); only the literal universal inequality is refuted.

    - [seq_cycle_family_cycle]: the edge set of a duplicate-free cyclic sequence of at least three vertices whose
      cyclically consecutive entries are adjacent is a cycle in the sense of Extremal.foundations.edge_cycles
      (edge_family_cycle), with the sequence's vertices as support.  The proof reads the edge set as the pairs
      [x; next c x] (GTBase seq_next_edge_set_uniq) and uses that next c moves the index by one modulo size c.
    - [seq_cycle_edge_set_mem_pair]: for i != j, the pair [i; j] is a member of that edge set exactly when i and j are
      cyclically consecutive in the sequence.
    - [kiraly_k5_cycle_count]: 37 explicit cycles of K_5 (10 triangles, 15 four-cycles, 12 five-cycles) are valid
      and have pairwise different edge sets, checked by vm_compute on the sequences only (their membership masks
      over the 10 pairs of K_5); finite sets of edge sets are never evaluated.
    Everything is closed by [Qed]; see the [Print Assumptions] audit at the end.  Imported by
    conjectures/grounding_X289.v for its K_5 witnesses. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph.
From GTBase Require Import base.
From Extremal.foundations Require Import edge_cycles.
From Extremal.conjectures Require Import X289.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Edge sets of cyclic sequences *)

Section SeqFamily.
Variable G : sgraph.
Implicit Types (c : seq G) (x y v : G).

Lemma seq_cycle_family_support c :
  edge_family_support (seq_cycle_edge_set c) = [set x in c].
Proof.
apply/setP => v; rewrite in_edge_family_support inE; apply/existsP/idP.
- case=> e /andP[eF ve]; have := subsetP (seq_cycle_edge_set_sub eF) v ve.
  by rewrite /seq_vertices inE.
- move=> vc; exists [set v; next c v]; rewrite !inE eqxx andbT.
  rewrite -in_seq_cycle_edge_set; apply: (subsetP (seq_next_edge_set_sub c)); apply/seq_next_edge_setP; by exists v.
Qed.

Lemma seq_cycle_index_next c x : uniq c -> x \in c -> index (next c x) c = (index x c).+1 %% size c.
Proof.
move=> uc xc; rewrite next_nth xc; case: c uc xc => [//|y p] uc xc.
have ilt : index x (y :: p) < (size p).+1 by rewrite -[(size p).+1]/(size (y :: p)) index_mem.
move: ilt; set i := index x (y :: p) => ilt.
case: (ltnP i (size p)) => [ip | pi].
- have -> : nth y p i = nth y (y :: p) i.+1 by [].
  by rewrite index_uniq // modn_small.
- have ieq : i = size p by apply/eqP; rewrite eqn_leq pi -ltnS ilt.
  by rewrite nth_default ?ieq // modnn /= eqxx.
Qed.

Lemma seq_cycle_next_neq c x : uniq c -> 1 < size c -> x \in c -> next c x != x.
Proof.
move=> uc c1 xc; apply/negP => /eqP e.
have := seq_cycle_index_next uc xc; rewrite e => /eqP.
have ilt : index x c < size c by rewrite index_mem.
rewrite -[X in X == _](@modn_small _ (size c)) // -addn1 -{1}[index x c]addn0 eqn_modDl.
by rewrite !modn_small // (ltn_trans _ c1).
Qed.

Lemma seq_cycle_next_next_neq c x : uniq c -> 2 < size c -> x \in c -> next c (next c x) != x.
Proof.
move=> uc c2 xc; apply/negP => /eqP e.
have nxc : next c x \in c by rewrite mem_next.
have := seq_cycle_index_next uc nxc; rewrite e (seq_cycle_index_next uc xc).
rewrite -[((index x c).+1 %% size c).+1]addn1 modnDml -addn1 -addnA => /eqP.
have ilt : index x c < size c by rewrite index_mem.
rewrite -[X in X == _](@modn_small _ (size c)) // -{1}[index x c]addn0 eqn_modDl.
by rewrite mod0n modn_small.
Qed.

Lemma seq_cycle_next_pair_inj c : uniq c -> 2 < size c ->
  {in c &, injective (fun x => [set x; next c x])}.
Proof.
move=> uc c2 x y xc yc /= exy; case: (eqVneq x y) => // nxy; exfalso.
have /set2P[/eqP | xny] : x \in [set y; next c y] by rewrite -exy !inE eqxx.
  by rewrite (negbTE nxy).
have /set2P[/eqP | ynx] : y \in [set x; next c x] by rewrite exy !inE eqxx.
  by rewrite eq_sym (negbTE nxy).
by have := seq_cycle_next_next_neq uc c2 xc; rewrite -ynx -xny eqxx.
Qed.

Lemma seq_cycle_family_card c : uniq c -> 2 < size c -> #|seq_cycle_edge_set c| = size c.
Proof.
move=> uc c2; rewrite -seq_next_edge_set_uniq // /seq_next_edge_set card_in_imset.
  by move=> x y; rewrite !inE; apply: seq_cycle_next_pair_inj.
by rewrite cardsE; apply/card_uniqP.
Qed.

Lemma seq_cycle_family_degree c v : uniq c -> 2 < size c -> v \in c ->
  incidence_degree (seq_cycle_edge_set c) v = 2.
Proof.
move=> uc c2 vc; rewrite /incidence_degree -seq_next_edge_set_uniq //.
have pvc : path.prev c v \in c by rewrite path.mem_prev.
have npv : next c (path.prev c v) = v by rewrite next_prev.
rewrite (_ : [set e in seq_next_edge_set c | v \in e] = [set [set v; next c v]; [set path.prev c v; v]]).
  apply/setP => e; rewrite !inE; apply/andP/orP.
  - case=> /seq_next_edge_setP[x xc ->]; rewrite !inE => /orP[/eqP <- | /eqP vx]; first by left.
    by right; rewrite vx prev_next.
  - case=> /eqP ->; (split; last by rewrite !inE eqxx ?orbT); apply/seq_next_edge_setP.
      by exists v.
    by exists (path.prev c v); rewrite ?npv.
rewrite cards2; case: eqP => // e; exfalso.
have pv : v = path.prev c v by apply: (seq_cycle_next_pair_inj uc c2 vc pvc) => /=; rewrite npv e.
by have := seq_cycle_next_neq uc (ltnW c2) vc; rewrite {1}pv npv eqxx.
Qed.

Lemma seq_cycle_family_connect c x y : uniq c -> x \in c -> y \in c ->
  connect (edge_family_rel (seq_cycle_edge_set c)) x y.
Proof.
move=> uc xc yc; have [i p rcx] := rot_to xc.
have cyc : path (frel (next c)) x (rcons p x) by have := cycle_next uc; rewrite -(rot_cycle i) rcx.
have inc z : z \in x :: rcons p x -> z \in c.
  by rewrite -[x :: rcons p x]/(rcons (x :: p) x) mem_rcons inE -rcx mem_rot => /orP[/eqP -> |].
have pth : path (edge_family_rel (seq_cycle_edge_set c)) x (rcons p x).
  apply: (@sub_in_path _ (mem c) _ _ _ x (rcons p x) _ cyc); last by apply/allP => z /inc.
  move=> a b ac bc /= /eqP <-; rewrite /edge_family_rel -seq_next_edge_set_uniq //.
  by apply/seq_next_edge_setP; exists a.
apply: (path_connect pth).
by rewrite -[x :: rcons p x]/(rcons (x :: p) x) mem_rcons inE -rcx mem_rot yc orbT.
Qed.

Lemma seq_cycle_family_cycle c : uniq c -> 2 < size c -> cycle (--) c ->
  edge_family_cycle (seq_cycle_edge_set c).
Proof.
move=> uc c2 cyc; apply/edge_family_cycleP; rewrite seq_cycle_family_support cardsE (card_uniqP uc).
split=> //.
- exact: seq_cycle_edge_set_cycle.
- exact: seq_cycle_family_card.
- by move=> v; rewrite inE; apply: seq_cycle_family_degree.
- by move=> x y; rewrite !inE; apply: seq_cycle_family_connect.
Qed.

Lemma seq_cycle_edge_set_mem_pair c i j : i != j ->
  ([set i; j] \in seq_cycle_edge_set c) = seq_cyclic_consecutiveb c i j.
Proof.
move=> nij; apply/seq_cycle_edge_setP/seq_cyclic_consecutiveP => [[u [v [cuv e]]] | cij]; last by exists i, j.
have iuv : i \in [set u; v] by rewrite -e !inE eqxx.
have juv : j \in [set u; v] by rewrite -e !inE eqxx orbT.
move: iuv juv; rewrite !inE => /orP[/eqP iu | /eqP iv] /orP[/eqP ju | /eqP jv]; subst.
- by rewrite eqxx in nij.
- by [].
- exact/seq_cyclic_consecutive_sym.
- by rewrite eqxx in nij.
Qed.

End SeqFamily.

(** ** Thirty-seven cycles of K_5 *)

Local Notation v0 := (@Ordinal 5 0 erefl).
Local Notation v1 := (@Ordinal 5 1 erefl).
Local Notation v2 := (@Ordinal 5 2 erefl).
Local Notation v3 := (@Ordinal 5 3 erefl).
Local Notation v4 := (@Ordinal 5 4 erefl).

Definition kiraly_k5_cycles : seq (seq 'K_5) :=
  [:: [:: v0; v1; v2];
  [:: v0; v1; v3];
  [:: v0; v1; v4];
  [:: v0; v2; v3];
  [:: v0; v2; v4];
  [:: v0; v3; v4];
  [:: v1; v2; v3];
  [:: v1; v2; v4];
  [:: v1; v3; v4];
  [:: v2; v3; v4];
  [:: v0; v1; v2; v3];
  [:: v0; v1; v3; v2];
  [:: v0; v2; v1; v3];
  [:: v0; v1; v2; v4];
  [:: v0; v1; v4; v2];
  [:: v0; v2; v1; v4];
  [:: v0; v1; v3; v4];
  [:: v0; v1; v4; v3];
  [:: v0; v3; v1; v4];
  [:: v0; v2; v3; v4];
  [:: v0; v2; v4; v3];
  [:: v0; v3; v2; v4];
  [:: v1; v2; v3; v4];
  [:: v1; v2; v4; v3];
  [:: v1; v3; v2; v4];
  [:: v0; v1; v2; v3; v4];
  [:: v0; v1; v2; v4; v3];
  [:: v0; v1; v3; v2; v4];
  [:: v0; v1; v3; v4; v2];
  [:: v0; v1; v4; v2; v3];
  [:: v0; v1; v4; v3; v2];
  [:: v0; v2; v1; v3; v4];
  [:: v0; v2; v1; v4; v3];
  [:: v0; v2; v3; v1; v4];
  [:: v0; v2; v4; v1; v3];
  [:: v0; v3; v1; v2; v4];
  [:: v0; v3; v2; v1; v4]].

Definition kiraly_k5_pairs : seq ('K_5 * 'K_5) :=
  [:: (v0, v1); (v0, v2); (v0, v3); (v0, v4); (v1, v2); (v1, v3); (v1, v4); (v2, v3); (v2, v4); (v3, v4)].

Definition kiraly_k5_mask (c : seq 'K_5) : seq bool := [seq seq_cyclic_consecutiveb c p.1 p.2 | p <- kiraly_k5_pairs].

Lemma kiraly_k5_cycles_ok : all (fun c => [&& uniq c, 2 < size c & cycle (@sedge 'K_5) c]) kiraly_k5_cycles.
Proof. by vm_compute. Qed.

Lemma kiraly_k5_masks_uniq : uniq (map kiraly_k5_mask kiraly_k5_cycles).
Proof. by vm_compute. Qed.

Lemma kiraly_k5_pairs_neq : all (fun p : 'K_5 * 'K_5 => p.1 != p.2) kiraly_k5_pairs.
Proof. by vm_compute. Qed.

Lemma kiraly_k5_cycle_count : 37 <= edge_family_cycle_count 'K_5.
Proof.
have minj := uniq_map_inj_in kiraly_k5_masks_uniq.
have Luniq : uniq kiraly_k5_cycles by move: kiraly_k5_masks_uniq; apply: map_uniq.
have inj : {in kiraly_k5_cycles &, injective (@seq_cycle_edge_set 'K_5)}.
  move=> c c' cL c'L e; apply: minj => //; rewrite /kiraly_k5_mask; apply/eq_in_map => p pP.
  by rewrite -!seq_cycle_edge_set_mem_pair ?e //; exact: (allP kiraly_k5_pairs_neq).
have sub : [set F in map (@seq_cycle_edge_set 'K_5) kiraly_k5_cycles] \subset [set F | edge_family_cycle F].
  apply/subsetP => F; rewrite in_set => /mapP[c cL ->]; rewrite in_set.
  by have /and3P[uc c2 cy] := allP kiraly_k5_cycles_ok c cL; apply: seq_cycle_family_cycle.
have u : uniq (map (@seq_cycle_edge_set 'K_5) kiraly_k5_cycles) by rewrite map_inj_in_uniq.
rewrite /edge_family_cycle_count; apply: leq_trans (subset_leq_card sub).
by rewrite cardsE (card_uniqP u) size_map.
Qed.

Lemma kiraly_k5_regular : regular 'K_5 4.
Proof.
move=> v; have -> : N(v) = [set~ v] by apply/setP => w; rewrite !inE /= eq_sym.
by rewrite cardsC1 card_ord.
Qed.

Lemma kiraly_k5_edges : #|E('K_5)| = 10.
Proof. by rewrite card_edge_Kn. Qed.

(** ** The disproof *)

(** Monotonicity of a fixed power, proved on variables: a count of K_5 never meets a closing tactic. *)
Lemma kiraly_leq_pow m n e : m <= n -> m ^ e <= n ^ e.
Proof.
move=> mn; elim: e => [|e ih]; first by rewrite !expn0.
by rewrite !expnS; apply: leq_mul.
Qed.

Theorem kiraly_four_regular_cycle_count_disproved : ~ kiraly_four_regular_cycle_count_statement.
Proof.
move/(_ 'K_5 kiraly_k5_regular); rewrite kiraly_k5_edges => h.
have lt : 199 ^ 10 < 37 ^ 2 * 100 ^ 10.
  apply: (@leq_trans ((2 * 100) ^ 10)); first by rewrite ltn_exp2r.
  rewrite expnMn; apply: leq_mul (leqnn _).
  by rewrite -[2 ^ 10]/(32 ^ 2) leq_exp2r.
have c2 := @kiraly_leq_pow 37 (edge_family_cycle_count 'K_5) 2 kiraly_k5_cycle_count.
have := leq_trans (leq_mul c2 (leqnn (100 ^ 10))) h.
by rewrite leqNgt lt.
Qed.

Print Assumptions kiraly_four_regular_cycle_count_disproved.

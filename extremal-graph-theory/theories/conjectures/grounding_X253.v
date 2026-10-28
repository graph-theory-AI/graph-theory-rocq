(** * Extremal.conjectures.grounding_X253 -- grounding certificates of wave X253.

    For each of the two rows: hyp_inhabited (the hypotheses hold on a concrete instance, with a concrete Turan value
    where the row has a Turan hypothesis, and the statement then yields its conclusion there) and not_trivially_true in
    the contract form of meta/EXPANSION_PLAN.md 4.4 (a variant obtained from the body is false and implies the row):
    erdos:926 without its Turan hypothesis (n = 0, m = 1: 1 <= c * 0); erdos:1078 without its minimum-degree hypothesis
    (the edgeless r-partite graph with parts of size n has no K_r for r >= 2).  The concrete Turan value is
    ex(1; H_4) = 0 ('K_1), as grounding_X252's ex(1; G_3) = 0; erdos:1078 has no relational hypothesis, and its
    inhabitants are the complete r-partite graphs K_r(n) (GTBase complete_multipartite_graph r n) for every r and n,
    since the statement's r0 and n0 are existential.  The wave has no local helper, so no helper_sanity certificate. *)

From Extremal.conjectures Require Import D2tur grounding_X239 X253.
(* GTBase last: its canonical [edge_count] must shadow D2tur's eta-alias of the same name. *)
From GTBase Require Import base common complete_multipartite_graphs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** erdos:926 ************************************************************ *)

(** A concrete Turan value: ex(1; H_4) = 0 ('K_1 is H_4-free, as H_4 has more than one vertex). *)
Lemma g253_turan_H4_1 : is_turan_number 1 (fun _ : 'I_1 => add_node (subdivision 'K_4 2) [set v | is_inl v]) 0.
Proof.
split.
- exists 'K_1; split; [by rewrite card_ord | by rewrite /D2tur.edge_count (proj2 edge_count_K0_K1) |].
  move=> i [h hi _].
  have e : h None = h (Some (inl ord0)) by rewrite (ord1 (h None)) (ord1 (h (Some _))).
  by have := hi _ _ e.
- by move=> m' [G [hG <- _]]; exact: g239_edge_count_le hG.
Qed.

(** hyp_inhabited: k = 4 meets the guard and its Turan hypothesis has a value (ex(1; H_4) = 0); the statement then
    gives its bound there. *)
Definition g253_ap_hyp_claim : Prop :=
  [/\ 4 <= 4, is_turan_number 1 (fun _ : 'I_1 => add_node (subdivision 'K_4 2) [set v | is_inl v]) 0 &
      (clique_subdivision_apex_turan_three_halves_statement ->
         exists c : nat,
           forall n m : nat,
             is_turan_number n (fun _ : 'I_1 => add_node (subdivision 'K_4 2) [set v | is_inl v]) m ->
             m ^ 2 <= c * n ^ 3)].

Theorem g253_ap_hyp_inhabited : g253_ap_hyp_claim.
Proof. by split; [| exact: g253_turan_H4_1 | move=> h; exact: h 4 (leqnn 4)]. Qed.

(** not_trivially_true: without the Turan hypothesis, n = 0 and m = 1 refute the bound; the variant implies the
    row. *)
Definition g253_ap_no_turan : Prop :=
  forall k : nat, 4 <= k -> exists c : nat, forall n m : nat, m ^ 2 <= c * n ^ 3.

Definition g253_ap_ntt_claim : Prop :=
  ~ g253_ap_no_turan /\ (g253_ap_no_turan -> clique_subdivision_apex_turan_three_halves_statement).

Theorem g253_ap_not_trivially_true : g253_ap_ntt_claim.
Proof.
split; last first.
  by move=> h k k4; have [c hc] := h k k4; exists c => n m _; exact: hc.
by move=> h; have [c hc] := h 4 (leqnn 4); have := hc 0 1; rewrite exp1n muln0.
Qed.

(** ** erdos:1078 *********************************************************** *)

(** K_r(n) = complete_multipartite_graph r n with p = the first coordinate: fibres of size n, no edge inside a part,
    every degree (r - 1) n. *)
Lemma g253_cmp_fibre (r n : nat) (i : 'I_r) : #|[set v : complete_multipartite_graph r n | v.1 == i]| = n.
Proof.
have -> : [set v : complete_multipartite_graph r n | v.1 == i] = [set (i, a) | a : 'I_n].
  by apply/setP => -[a b]; rewrite inE /=; apply/eqP/imsetP => [<-|[c _ [-> _]]] //; exists b.
by rewrite card_imset ?card_ord // => a b [].
Qed.

Lemma g253_cmp_parts (r n : nat) (x y : complete_multipartite_graph r n) : x -- y -> x.1 != y.1.
Proof. by []. Qed.

Lemma g253_cmp_deg (r n : nat) (v : complete_multipartite_graph r n) : #|N(v)| + n = r * n.
Proof.
have -> : N(v) = ~: [set w : complete_multipartite_graph r n | w.1 == v.1].
  by apply/setP => w; rewrite !inE complete_multipartite_edgeE eq_sym.
have h := cardsC [set w : complete_multipartite_graph r n | w.1 == v.1].
rewrite g253_cmp_fibre in h; rewrite addnC h; exact: card_complete_multipartite_graph.
Qed.

(** At q = 2 the minimum-degree clause holds with equality: (4r + 2) n = 4 (r - 1) n + 6 n. *)
Lemma g253_cmp_deg2 (r n : nat) (v : complete_multipartite_graph r n) :
  (2 * 2 * r + 2) * n <= 2 * 2 * #|N(v)| + 3 * 2 * n.
Proof.
have e := g253_cmp_deg v.
by rewrite mulnDl -mulnA -e mulnDr -addnA leq_add2l -mulnDl.
Qed.

(** hyp_inhabited: q = 2 meets the guard, and K_r(n) is an r-partite graph with parts of size n meeting the q = 2 degree
    clause for every r and n; the statement at q = 2 then gives, for all large r and n, a K_r in K_r(n). *)
Definition g253_mp_hyp_claim : Prop :=
  [/\ 1 <= 2, (forall (r n : nat) (i : 'I_r), #|[set v : complete_multipartite_graph r n | v.1 == i]| = n),
      (forall (r n : nat) (x y : complete_multipartite_graph r n), x -- y -> x.1 != y.1),
      (forall (r n : nat) (v : complete_multipartite_graph r n),
         (2 * 2 * r + 2) * n <= 2 * 2 * #|N(v)| + 3 * 2 * n) &
      (balanced_multipartite_min_degree_clique_statement ->
         exists r0 : nat, forall r : nat, r0 <= r -> exists n0 : nat, forall n : nat, n0 <= n ->
           has_subgraph (complete_multipartite_graph r n) 'K_r)].

Theorem g253_mp_hyp_inhabited : g253_mp_hyp_claim.
Proof.
split; [done | exact: g253_cmp_fibre | exact: g253_cmp_parts | exact: g253_cmp_deg2 |].
move=> h; have [r0 hr0] := h 2 isT; exists r0 => r hr; have [n0 hn0] := hr0 r hr; exists n0 => n hn.
exact: (hn0 n (complete_multipartite_graph r n) (fun v => v.1) hn (@g253_cmp_fibre r n) (@g253_cmp_parts r n)
          (@g253_cmp_deg2 r n)).
Qed.

(** not_trivially_true: without the minimum-degree hypothesis, at q = 1, r = r0 + 2 and n = n0 the edgeless r-partite
    graph (K_r(n) with every edge deleted, p = the first coordinate) would contain K_r, whose edge {0, 1} would map to
    an edge; the variant implies the row. *)
Definition g253_mp_no_degree : Prop :=
  forall q : nat, 1 <= q -> exists r0 : nat, forall r : nat, r0 <= r -> exists n0 : nat,
    forall (n : nat) (G : sgraph) (p : G -> 'I_r), n0 <= n ->
      (forall i : 'I_r, #|[set v | p v == i]| = n) ->
      (forall x y : G, x -- y -> p x != p y) ->
      has_subgraph G 'K_r.

Definition g253_mp_ntt_claim : Prop :=
  ~ g253_mp_no_degree /\ (g253_mp_no_degree -> balanced_multipartite_min_degree_clique_statement).

Theorem g253_mp_not_trivially_true : g253_mp_ntt_claim.
Proof.
split; last first.
  move=> h q q1; have [r0 hr0] := h q q1; exists r0 => r hr; have [n0 hn0] := hr0 r hr.
  by exists n0 => n G p hn hp hq _; exact: hn0 n G p hn hp hq.
move=> h; have [r0 hr0] := h 1 isT; have [n0 hn0] := hr0 r0.+2 (leqW (leqnSn r0)).
pose G := del_edge_set (complete_multipartite_graph r0.+2 n0) setT.
have hq : forall x y : G, x -- y -> x.1 != y.1 by move=> x y; rewrite del_edge_setE inE andbF.
have /has_subgraphP [f [_ hf]] := hn0 n0 G (fun v => v.1) (leqnn n0) (@g253_cmp_fibre r0.+2 n0) hq.
have := hf ord0 (@Ordinal r0.+2 1 isT) isT.
by rewrite del_edge_setE inE andbF.
Qed.

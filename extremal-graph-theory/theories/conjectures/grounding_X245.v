(** * Extremal.conjectures.grounding_X245 -- grounding certificates of wave X245.

    For each of the three rows: hyp_inhabited (the hypotheses hold on a concrete instance, and the statement then
    yields its conclusion there) and not_trivially_true in the contract form of meta/EXPANSION_PLAN.md 4.4 (the row
    with a load-bearing hypothesis dropped is false, and that variant implies the row): the Turan hypothesis for
    erdos:59 (H = K_3, m = 0: the empty graph and a one-edge graph on n0 + 2 vertices are two K_3-free graphs, and
    2^1 <= 1 fails), "d0 <= d" for erdos:578 (at d = 1 only E(K_2) contains Q_1, so a family has at most one member
    and 3 * 2 <= 3 * 1 + 2 fails) and the Ramsey hypothesis for erdos:1036 (equal-size induced subgraphs of K_N are
    isomorphic (diso_Kn), so a pairwise non-isomorphic family has at most N + 1 members, and N = 2^{4(p+1)} gives
    (N + 1)^p < 2^N).  The wave has no local helper, so no helper_sanity certificate.  Small instances: K_3 contains a
    cycle (C_3), the guard of erdos:59; ex(1; K_3) = 0 with the one graph on 'I_1; Q_0 = K_1 inside the one graph on
    'I_(2^0); 'K_2 at C = 3. *)

From Extremal.conjectures Require Import D2tur grounding_X239 X245.
(* GTBase last: its canonical [edge_count] must shadow D2tur's eta-alias of the same name. *)
From GTBase Require Import base common hypercubes.
From mathcomp Require Import zify.
From Stdlib Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Small instances *)

Lemma g245_turan_K3_1 : is_turan_number 1 (fun _ : 'I_1 => 'K_3) 0.
Proof.
split.
- exists 'K_1; split; [by rewrite card_ord | by rewrite /D2tur.edge_count (proj2 edge_count_K0_K1) |].
  by move=> i [h hi _]; have := leq_card h hi; rewrite !card_ord.
- by move=> m' [G [hG <- _]]; exact: g239_edge_count_le hG.
Qed.

(** A graph whose only possible edge is the pair e has no triangle. *)
Lemma g245_one_edge_no_K3 (G : sgraph) (e : {set G}) : ~ has_subgraph (del_edge_set G (E(G) :\: [set e])) 'K_3.
Proof.
case/has_subgraphP => f [fi fh].
have pe (x y : 'K_3) : x -- y -> [set f x; f y] = e.
  move=> xy; have := fh _ _ xy; rewrite del_edge_setE => /andP [fxy].
  by rewrite !inE in_edges fxy andbT negbK => /eqP.
have e01 := pe ord0 (Ordinal (isT : 1 < 3)) isT.
have e12 := pe (Ordinal (isT : 1 < 3)) (Ordinal (isT : 2 < 3)) isT.
have : f ord0 \in [set f (Ordinal (isT : 1 < 3)); f (Ordinal (isT : 2 < 3))] by rewrite e12 -e01 !inE eqxx.
by rewrite !inE => /orP [/eqP /fi | /eqP /fi].
Qed.

Lemma g245_no_edge_no_K3 (G : sgraph) : ~ has_subgraph (del_edge_set G (E(G) :\: set0)) 'K_3.
Proof.
case/has_subgraphP => f [_ fh].
have := fh ord0 (Ordinal (isT : 1 < 3)) isT; rewrite del_edge_setE setD0 => /andP [xy].
by rewrite in_edges xy.
Qed.

(** ** Row erdos:59 *)

(** K_3 contains a cycle (C_3), so it meets the guard of the row. *)
Lemma g245_K3_cycle : exists k : nat, 3 <= k /\ has_subgraph 'K_3 (cycle_graph k).
Proof.
exists 3; split => //; apply/has_subgraphP; exists (fun i : cycle_graph 3 => (i : 'K_3)); split; first by move=> i j.
by move=> i j /andP [ij _].
Qed.

Definition g245_count_hyp_claim : Prop :=
  [/\ exists k : nat, 3 <= k /\ has_subgraph 'K_3 (cycle_graph k),
      is_turan_number 1 (fun _ : 'I_1 => 'K_3) 0,
      (forall F : {set {set 'I_1}}, F \in [set set0] ->
         F \subset E('K_1) /\ ~ has_subgraph (del_edge_set 'K_1 (E('K_1) :\: F)) 'K_3) &
      (turan_exponent_free_graph_count_statement -> exists n0 : nat,
         forall n m : nat, n0 <= n -> is_turan_number n (fun _ : 'I_1 => 'K_3) m ->
           forall Fs : {set {set {set 'I_n}}},
             (forall F : {set {set 'I_n}}, F \in Fs ->
                F \subset E('K_n) /\ ~ has_subgraph (del_edge_set 'K_n (E('K_n) :\: F)) 'K_3) ->
             #|Fs| ^ 1 <= 2 ^ ((1 + 1) * m))].

Theorem g245_count_hyp_inhabited : g245_count_hyp_claim.
Proof.
split; [exact: g245_K3_cycle | exact: g245_turan_K3_1 | | by move=> h; exact: h 'K_3 1 isT g245_K3_cycle].
move=> F; rewrite inE => /eqP ->; split; first exact: sub0set.
exact: g245_no_edge_no_K3.
Qed.

Definition g245_count_no_turan : Prop :=
  forall (H : sgraph) (q : nat), 1 <= q -> (exists k : nat, 3 <= k /\ has_subgraph H (cycle_graph k)) ->
    exists n0 : nat,
    forall n m : nat, n0 <= n ->
      forall Fs : {set {set {set 'I_n}}},
        (forall F : {set {set 'I_n}}, F \in Fs ->
           F \subset E('K_n) /\ ~ has_subgraph (del_edge_set 'K_n (E('K_n) :\: F)) H) ->
        #|Fs| ^ q <= 2 ^ ((q + 1) * m).

Definition g245_count_ntt_claim : Prop :=
  ~ g245_count_no_turan /\ (g245_count_no_turan -> turan_exponent_free_graph_count_statement).

Theorem g245_count_not_trivially_true : g245_count_ntt_claim.
Proof.
split; last first.
  by move=> h H q q1 hc; have [n0 hn] := h H q q1 hc; exists n0 => n m nn _; exact: hn.
move=> h; have [n0 hn] := h 'K_3 1 isT g245_K3_cycle.
pose e : {set 'K_(n0.+2)} := [set ord0; Ordinal (isT : 1 < 2 + n0)].
have ne : (set0 : {set {set 'K_(n0.+2)}}) != [set e] by apply/eqP => /setP /(_ e); rewrite !inE eqxx.
have hF : forall F : {set {set 'I_n0.+2}}, F \in [set set0; [set e]] ->
    F \subset E('K_n0.+2) /\ ~ has_subgraph (del_edge_set 'K_n0.+2 (E('K_n0.+2) :\: F)) 'K_3.
  move=> F; rewrite !inE => /orP [/eqP -> | /eqP ->].
    by split; [exact: sub0set | exact: g245_no_edge_no_K3].
  split; last exact: g245_one_edge_no_K3.
  by rewrite sub1set; apply/(@edgesP 'K_(n0.+2)); exists ord0, (Ordinal (isT : 1 < 2 + n0)).
by have := hn n0.+2 0 (leqW (leqnSn n0)) [set set0; [set e]] hF; rewrite cards2 ne.
Qed.


(** ** Row erdos:578 *)

Lemma g245_K1_sub (G : sgraph) (x : G) : has_subgraph G 'K_1.
Proof.
apply/has_subgraphP; exists (fun _ => x); split; first by move=> i j _; rewrite (ord1 i) (ord1 j).
by move=> i j; rewrite /edge_rel /= (ord1 i) (ord1 j) eqxx.
Qed.

Definition g245_cube_hyp_claim : Prop :=
  [/\ (forall F : {set {set 'I_(2 ^ 0)}}, F \in [set set0] ->
         F \subset E('K_(2 ^ 0)) /\
         has_subgraph (del_edge_set 'K_(2 ^ 0) (E('K_(2 ^ 0)) :\: F)) (product_hypercube 0)),
      1 * 2 ^ #|E('K_(2 ^ 0))| <= 1 * #|[set (set0 : {set {set 'I_(2 ^ 0)}})]| + 2 ^ #|E('K_(2 ^ 0))| &
      (random_graph_spanning_hypercube_statement -> exists d0 : nat, forall d : nat, d0 <= d ->
         exists Fs : {set {set {set 'I_(2 ^ d)}}},
           (forall F : {set {set 'I_(2 ^ d)}}, F \in Fs ->
              F \subset E('K_(2 ^ d)) /\
              has_subgraph (del_edge_set 'K_(2 ^ d) (E('K_(2 ^ d)) :\: F)) (product_hypercube d)) /\
           1 * 2 ^ #|E('K_(2 ^ d))| <= 1 * #|Fs| + 2 ^ #|E('K_(2 ^ d))|)].

Theorem g245_cube_hyp_inhabited : g245_cube_hyp_claim.
Proof.
split; [ | by rewrite mul1n cards1 mul1n leq_addl | by move=> h; exact: h 1 isT].
move=> F; rewrite inE => /eqP ->; split; first exact: sub0set.
by rewrite product_hypercube0; apply: g245_K1_sub; exact: (ord0 : 'I_1).
Qed.

Definition g245_cube_no_size : Prop :=
  forall q : nat, 1 <= q -> exists d0 : nat, forall d : nat,
    exists Fs : {set {set {set 'I_(2 ^ d)}}},
      (forall F : {set {set 'I_(2 ^ d)}}, F \in Fs ->
         F \subset E('K_(2 ^ d)) /\
         has_subgraph (del_edge_set 'K_(2 ^ d) (E('K_(2 ^ d)) :\: F)) (product_hypercube d)) /\
      q * 2 ^ #|E('K_(2 ^ d))| <= q * #|Fs| + 2 ^ #|E('K_(2 ^ d))|.

Definition g245_cube_ntt_claim : Prop :=
  ~ g245_cube_no_size /\ (g245_cube_no_size -> random_graph_spanning_hypercube_statement).

Theorem g245_cube_not_trivially_true : g245_cube_ntt_claim.
Proof.
split; last first.
  by move=> h q q1; have [d0 hd] := h q q1; exists d0 => d _; exact: hd.
move=> h; have [d0 hd] := h 3 isT; have [Fs [hF hq]] := hd 1.
have cE : #|E('K_(2 ^ 1))| = 1 by rewrite card_edge_Kn.
have Fs1 : #|Fs| <= 1.
  apply: (@leq_trans #|[set E('K_(2 ^ 1))]|); last by rewrite cards1.
  apply/subset_leq_card/subsetP => F /hF [FE hs]; rewrite inE; apply/eqP.
  case/has_subgraphP: hs => f [_ fh].
  have := fh ((ord0, ord0) : product_hypercube 1) ((ord_max, ord0) : product_hypercube 1) isT.
  rewrite del_edge_setE => /andP [xy]; rewrite !inE in_edges xy andbT negbK => eF.
  apply/eqP; rewrite eqEcard FE cE card_gt0; apply/set0Pn.
  by exists [set f (ord0, ord0); f (ord_max, ord0)].
by have := leq_trans hq (leq_add (leq_mul (leqnn 3) Fs1) (leqnn _)); rewrite cE.
Qed.


(** ** Row erdos:1036 *)

Lemma g245_K2_ramsey3 : forall S : {set 'K_2}, cliqueb S || stable S -> 2 ^ #|S| < #|'K_2| ^ 3.
Proof.
move=> S _; rewrite card_ord.
apply: (@leq_ltn_trans (2 ^ 2)); last by [].
by rewrite leq_pexp2l //; have := max_card S; rewrite card_ord.
Qed.

(** Two equal-size induced subgraphs of K_n are isomorphic (both complete). *)
Lemma g245_Kn_induced_diso (n : nat) (A B : {set 'K_n}) : #|A| = #|B| -> inhabited (induced A ≃ induced B).
Proof.
move=> e.
have cmp (S : {set 'K_n}) (x y : induced S) : x != y -> x -- y.
  by move=> xy; rewrite /edge_rel /=; rewrite /edge_rel /= -(inj_eq val_inj) in xy.
have hA := diso_Kn (@cmp A); have hB := diso_Kn (@cmp B).
have cAB : #|induced A| = #|induced B| by rewrite !card_sig; exact: e.
rewrite cAB in hA; constructor; exact: diso_comp hA (diso_sym hB).
Qed.


(** A family of pairwise non-isomorphic induced subgraphs of K_n has at most n + 1 members. *)
Lemma g245_Kn_family (n : nat) (F : {set {set 'K_n}}) :
  (forall A B : {set 'K_n}, A \in F -> B \in F -> A != B -> ~ inhabited (induced A ≃ induced B)) -> #|F| <= n.+1.
Proof.
move=> h; pose f (A : {set 'K_n}) : 'I_n.+1 := inord #|A|.
have fi : {in F &, injective f}.
  move=> A B AF BF /(congr1 val).
  have bnd (S : {set 'K_n}) : #|S| < n.+1 by rewrite ltnS; apply: leq_trans (max_card _) _; rewrite card_ord.
  rewrite /f /= !inordK ?bnd // => e.
  by apply/eqP; apply: contraT => AB; case: (h A B AF BF AB); exact: g245_Kn_induced_diso e.
by rewrite -(card_in_imset fi); apply: leq_trans (max_card _) _; rewrite card_ord.
Qed.


Lemma g245_exp_gap (p : nat) : exists N : nat, N.+1 ^ p < 2 ^ N.
Proof.
have mono (a b e : nat) : a <= b -> a ^ e <= b ^ e by move=> ab; elim: e => // e IH; rewrite !expnS leq_mul.
exists (2 ^ (4 * p.+1)); set k := 4 * p.+1.
have h1 : (2 ^ k).+1 ^ p <= 2 ^ (k.+1 * p).
  by rewrite expnM; apply: mono; rewrite expnS mul2n -addnn -addn1 leq_add2l expn_gt0.
apply: leq_ltn_trans h1 _; rewrite ltn_exp2l //.
have h2 : p.+2 ^ 4 <= 2 ^ k by rewrite /k mulnC expnM; apply: mono; exact: ltn_expl.
by apply: leq_trans h2; rewrite /k; nia.
Qed.

Definition g245_iso_hyp_claim : Prop :=
  [/\ forall S : {set 'K_2}, cliqueb S || stable S -> 2 ^ #|S| < #|'K_2| ^ 3 &
      (ramsey_graph_many_nonisomorphic_induced_subgraphs_statement -> exists p : nat, 1 <= p /\
         forall G : sgraph,
           (forall S : {set G}, cliqueb S || stable S -> 2 ^ #|S| < #|G| ^ 3) ->
           exists F : {set {set G}},
             (forall A B : {set G}, A \in F -> B \in F -> A != B -> ~ inhabited (induced A ≃ induced B)) /\
             2 ^ #|G| <= #|F| ^ p)].

Theorem g245_iso_hyp_inhabited : g245_iso_hyp_claim.
Proof. by split; [exact: g245_K2_ramsey3 | move=> h; exact: h 3]. Qed.

Definition g245_iso_no_ramsey : Prop :=
  forall C : nat, exists p : nat, 1 <= p /\
    forall G : sgraph,
      exists F : {set {set G}},
        (forall A B : {set G}, A \in F -> B \in F -> A != B -> ~ inhabited (induced A ≃ induced B)) /\
        2 ^ #|G| <= #|F| ^ p.

Definition g245_iso_ntt_claim : Prop :=
  ~ g245_iso_no_ramsey /\ (g245_iso_no_ramsey -> ramsey_graph_many_nonisomorphic_induced_subgraphs_statement).

Theorem g245_iso_not_trivially_true : g245_iso_ntt_claim.
Proof.
split; last first.
  by move=> h C; have [p [p1 hp]] := h C; exists p; split => // G _; exact: hp.
move=> h; have [p [p1 hp]] := h 0; have [N hN] := g245_exp_gap p.
have [F [hF h2]] := hp 'K_N; have hF1 := g245_Kn_family hF.
rewrite card_ord in h2; have h3 : #|F| ^ p <= N.+1 ^ p by rewrite leq_exp2r.
by have := leq_ltn_trans (leq_trans h2 h3) hN; rewrite ltnn.
Qed.



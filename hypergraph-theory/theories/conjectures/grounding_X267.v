(** * Hypergraph.conjectures.grounding_X267 -- grounding certificates for wave X267 (2026-10-31)

    For each of the three rows: hyp_inhabited (the body's conditions hold together at a small instance, and the
    statement gives its consequence) and not_trivially_true (a variant without one hypothesis is false and implies
    the statement); helper_sanity is empty, as X267.v declares no local helper.
    - erdos:716: three disjoint triples on 9 vertices form a 3-uniform hypergraph whose three distinct edges span
      9 > 6 vertices; without the (6,3) hypothesis the row is false, as the complete 3-graph on n >= 9 vertices has
      C(n, 3) > n^2 edges.
    - arxiv:2505.05339#00 / #01: K_(3,3) and K_(4,4) are 3- and 4-regular, and colouring the edge {inl i, inr j}
      by (i + j) mod d is a proper d-edge-colouring; a graph the statement supplies has an edge.  Without "x -- y"
      (#00), resp. "u i -- v i" (#01), the row is false: deleting a vertex with all its neighbours lowers the
      independence number (an independent set avoiding them extends by the vertex), and four, resp. 2(d - 1) >=
      d + 1, deleted vertices cover a closed neighbourhood. *)

From GTBase Require Import base common edge_colourings.
From Hypergraph.foundations Require Import hypergraph.
From Hypergraph.conjectures Require Import X267.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** erdos:716 ************************************************************ *)

(** All 3-subsets of 'I_n: the complete 3-graph. *)
Definition g267_complete3 (n : nat) : {set {set 'I_n}} := [set A : {set 'I_n} | #|A| == 3].

Lemma g267_complete3_uniform (n : nat) : hg_uniform (g267_complete3 n) 3.
Proof. by move=> e; rewrite inE => /eqP. Qed.

Lemma g267_complete3_card (n : nat) : #|g267_complete3 n| = 'C(n, 3).
Proof. by rewrite /g267_complete3 card_draws card_ord. Qed.

(** C(n, 3) > n^2 for n >= 9. *)
Lemma g267_bin3_gt (n : nat) : 9 <= n -> n ^ 2 < 'C(n, 3).
Proof.
move=> h9; rewrite -(ltn_pmul2r (fact_gt0 3)) bin_ffact.
have -> : n = (n - 9) + 9 by rewrite subnK.
move: (n - 9) => k; rewrite !ffactnS ffactn0 muln1 /=.
rewrite [k + 9]addnC /= [9 + k]addnC.
rewrite expnS expn1 -mulnA ltn_pmul2l ?addn_gt0 ?orbT //.
apply: (@leq_trans ((8 + k) * 7)); last by rewrite leq_mul2l leq_addr orbT.
rewrite (_ : 3`! = 6) // mulnDl mulnDl.
rewrite (_ : 9 * 6 = 54) // (_ : 8 * 7 = 56) // [56 + _]addnC -addnS.
by apply: leq_add; [rewrite leq_mul2l orbT | ].
Qed.

(** The statement without its (6,3) hypothesis. *)
Definition g267_st_no63 : Prop :=
  forall p : nat, 1 <= p -> exists N : nat, forall (n : nat) (E : {set {set 'I_n}}),
    N <= n -> hg_uniform E 3 -> p * #|E| <= n ^ 2.

Definition g267_st_ntt_claim : Prop :=
  ~ g267_st_no63 /\ (g267_st_no63 -> six_three_hypergraph_statement).

Theorem g267_st_not_trivially_true : g267_st_ntt_claim.
Proof.
split.
- move=> h; have [N hN] := h 1 isT.
  have := hN (N + 9) (g267_complete3 (N + 9)) (leq_addr _ _) (@g267_complete3_uniform (N + 9)).
  rewrite mul1n g267_complete3_card leqNgt; apply/negP/negPn.
  by apply: g267_bin3_gt; rewrite leq_addl.
- move=> h p p1; have [N hN] := h p p1; exists N => n E hn hu _; exact: hN.
Qed.

(** Three pairwise disjoint 3-sets span 9 vertices. *)
Lemma g267_disjoint_span (n : nat) (e1 e2 e3 : {set 'I_n}) :
  #|e1| = 3 -> #|e2| = 3 -> #|e3| = 3 ->
  [disjoint e1 & e2] -> [disjoint e1 & e3] -> [disjoint e2 & e3] -> #|e1 :|: e2 :|: e3| = 9.
Proof.
move=> c1 c2 c3 d12 d13 d23; rewrite cardsU c3 cardsU c1 c2 (disjoint_setI0 d12) cards0.
have -> : (e1 :|: e2) :&: e3 = set0 by rewrite setIUl (disjoint_setI0 d13) (disjoint_setI0 d23) setU0.
by rewrite cards0.
Qed.

(** Three disjoint triples on 'I_9: a (6,3)-free 3-graph with three edges. *)
Definition g267_A : {set 'I_9} := [set (@Ordinal 9 0 isT); (@Ordinal 9 1 isT); (@Ordinal 9 2 isT)].
Definition g267_B : {set 'I_9} := [set (@Ordinal 9 3 isT); (@Ordinal 9 4 isT); (@Ordinal 9 5 isT)].
Definition g267_C : {set 'I_9} := [set (@Ordinal 9 6 isT); (@Ordinal 9 7 isT); (@Ordinal 9 8 isT)].
Definition g267_E : {set {set 'I_9}} := [set g267_A; g267_B; g267_C].

Lemma g267_ABC_card : [/\ #|g267_A| = 3, #|g267_B| = 3 & #|g267_C| = 3].
Proof. by split; rewrite /g267_A /g267_B /g267_C -setUA cardsU1 cards2 !inE. Qed.

Lemma g267_ABC_disjoint :
  [/\ [disjoint g267_A & g267_B], [disjoint g267_A & g267_C] & [disjoint g267_B & g267_C]].
Proof.
by split; rewrite -setI_eq0; apply/eqP/setP => x; rewrite !inE; apply/negP => /andP [/orP [/orP [] | ] /eqP -> ].
Qed.

Lemma g267_ABC_neq : [/\ g267_A != g267_B, g267_A != g267_C & g267_B != g267_C].
Proof.
split; apply/eqP => /setP.
- by move=> /(_ (@Ordinal 9 0 isT)); rewrite !inE.
- by move=> /(_ (@Ordinal 9 0 isT)); rewrite !inE.
- by move=> /(_ (@Ordinal 9 3 isT)); rewrite !inE.
Qed.

Lemma g267_E_mem (e : {set 'I_9}) : e \in g267_E -> [\/ e = g267_A, e = g267_B | e = g267_C].
Proof. by rewrite !inE => /orP [/orP [] | ] /eqP ->; [apply: Or31 | apply: Or32 | apply: Or33]. Qed.

Lemma g267_E_uniform : hg_uniform g267_E 3.
Proof. by move=> e /g267_E_mem []; case: g267_ABC_card => cA cB cC ->. Qed.

Lemma g267_E_disjoint (X Y : {set 'I_9}) :
  X \in g267_E -> Y \in g267_E -> X != Y -> [disjoint X & Y].
Proof.
case: g267_ABC_disjoint => dAB dAC dBC.
move=> /g267_E_mem [] -> /g267_E_mem [] -> //; rewrite ?eqxx // => _; by rewrite disjoint_sym.
Qed.

Lemma g267_E_card : #|g267_E| = 3.
Proof.
case: g267_ABC_neq => nAB nAC nBC.
by rewrite /g267_E -setUA cardsU1 cards2 !inE nBC (negbTE nAB) (negbTE nAC).
Qed.

Definition g267_st_hyp_claim : Prop :=
  [/\ hg_uniform g267_E 3, #|g267_E| = 3,
      (forall e1 e2 e3 : {set 'I_9}, e1 \in g267_E -> e2 \in g267_E -> e3 \in g267_E ->
         e1 != e2 -> e1 != e3 -> e2 != e3 -> 6 < #|e1 :|: e2 :|: e3|) &
      (six_three_hypergraph_statement ->
         exists N : nat, forall (n : nat) (E : {set {set 'I_n}}), N <= n -> hg_uniform E 3 ->
           (forall e1 e2 e3 : {set 'I_n}, e1 \in E -> e2 \in E -> e3 \in E ->
              e1 != e2 -> e1 != e3 -> e2 != e3 -> 6 < #|e1 :|: e2 :|: e3|) ->
           #|E| <= n ^ 2)].

Theorem g267_st_hyp_inhabited : g267_st_hyp_claim.
Proof.
split; [exact: g267_E_uniform | exact: g267_E_card | |].
- move=> e1 e2 e3 h1 h2 h3 n12 n13 n23.
  rewrite (g267_disjoint_span (g267_E_uniform h1) (g267_E_uniform h2) (g267_E_uniform h3)) //;
    exact: g267_E_disjoint.
- move=> h; have [N hN] := h 1 isT; exists N => n E hn hu h63.
  by rewrite -[#|E|]mul1n; exact: hN.
Qed.

(** ** arxiv:2505.05339 #00 and #01 ********************************************* *)

(** Deleting a closed neighbourhood lowers the independence number. *)
Lemma g267_closed_nbhd_drop (G : sgraph) (w : G) (C : {set G}) :
  w \in C -> N(w) \subset C -> α([set: G] :\: C) < α([set: G]).
Proof.
move=> wC NC; case: (alphaP ([set: G] :\: C)) => S /maxstabsetW /stabsetsP [SC stS].
have wS : w \notin S by apply/negP => /(subsetP SC); rewrite !inE wC.
have NS (z : G) : z \in S -> ~~ w -- z.
  move=> zS; apply/negP => wz; have : z \in C by apply: (subsetP NC); rewrite in_opn.
  by have := subsetP SC z zS; rewrite !inE => /andP [/negPf ->].
have st : stable (w |: S).
  apply/stableP => u v; rewrite !inE => /orP [/eqP -> | uS] /orP [/eqP -> | vS].
  - by rewrite sg_irrefl.
  - exact: NS.
  - by rewrite sgP; exact: NS.
  - exact: (stableP _ stS).
have := @stabset_bound G (w |: S) [set: G]; rewrite cardsU1 wS add1n; apply.
by apply/stabsetsP; split; [exact: subsetT | exact: st].
Qed.

(** K_(d+1,d+1) is (d+1)-regular, and colouring the edge {inl i, inr j} by (i + j) mod (d+1) is proper. *)
Lemma g267_kb_regular (d : nat) : regular ('K_d,d) d.
Proof. by case=> [x|y]; [exact: deg_Knm_l | exact: deg_Knm_r]. Qed.

Definition g267_idx (n : nat) (z : 'I_n + 'I_n) : nat := match z with inl i => i | inr j => j end.

Definition g267_kb_col (d : nat) (A : {set 'K_d.+1,d.+1}) : 'I_d.+1 :=
  Ordinal (ltn_pmod (\sum_(z in A) g267_idx z) (ltn0Sn d)).

Lemma g267_kb_col2 (d : nat) (x y : 'K_d.+1,d.+1) :
  x != y -> val (g267_kb_col [set x; y]) = (g267_idx x + g267_idx y) %% d.+1.
Proof. by move=> xy; rewrite /= big_setU1 ?inE //= big_set1. Qed.

Lemma g267_kb_proper (d : nat) : proper_edge_colouring (@g267_kb_col d).
Proof.
move=> x y z xy xz yz.
have xy' : x != y by apply: contraTneq xy => ->; rewrite sg_irrefl.
have xz' : x != z by apply: contraTneq xz => ->; rewrite sg_irrefl.
apply/negP => /eqP /(congr1 val); rewrite !g267_kb_col2 // => /eqP; rewrite eqn_modDl.
have lt (w : 'K_d.+1,d.+1) : g267_idx w < d.+1 by case: w => w; exact: ltn_ord.
rewrite !modn_small //; clear xy' xz'; move: xy xz yz; case: x => i; case: y => j; case: z => k //= _ _.
- by move=> jk /eqP /val_inj eq; move: jk; rewrite eq eqxx.
- by move=> jk /eqP /val_inj eq; move: jk; rewrite eq eqxx.
Qed.

(** #00, hyp_inhabited: K_(3,3) is cubic, 3-edge-colourable and has an edge; a graph the statement supplies has
    an edge, so the alpha condition is not vacuous there. *)
Definition g267_cubic_hyp_claim : Prop :=
  [/\ 6 <= #|'K_3,3|, regular ('K_3,3) 3, (exists col : {set 'K_3,3} -> 'I_3, proper_edge_colouring col),
      (inl ord0 : 'K_3,3) -- inr ord0 &
      (cubic_alpha_stable_statement ->
         forall N : nat, exists G : sgraph, N <= #|G| /\ exists u v : G, u -- v)].

Theorem g267_cubic_hyp_inhabited : g267_cubic_hyp_claim.
Proof.
split; [by rewrite card_sum !card_ord | exact: g267_kb_regular | | by [] |].
- by exists (@g267_kb_col 2); exact: g267_kb_proper.
- move=> h N; have [G [hN reg _ _]] := h N.+1; exists G; split; first exact: ltnW.
  have [w _] := card_gt0P (leq_ltn_trans (leq0n N) hN).
  have : 0 < #|N(w)| by rewrite reg.
  by case/card_gt0P => a; rewrite in_opn => wa; exists w, a.
Qed.

(** #00, not_trivially_true: without "x -- y" the statement is false (delete a vertex and its three neighbours). *)
Definition g267_cubic_no_xy : Prop :=
  forall N : nat, exists G : sgraph,
    [/\ N <= #|G|, regular G 3, (exists col : {set G} -> 'I_3, proper_edge_colouring col) &
      forall u v x y : G, u -- v -> α([set: G]) = α([set: G] :\: [set u; v; x; y])].

Definition g267_cubic_ntt_claim : Prop :=
  ~ g267_cubic_no_xy /\ (g267_cubic_no_xy -> cubic_alpha_stable_statement).

Theorem g267_cubic_not_trivially_true : g267_cubic_ntt_claim.
Proof.
split.
- move=> h; have [G [G1 reg _ st]] := h 1.
  have [w _] := card_gt0P G1.
  have : size (enum N(w)) = 3 by rewrite -cardE reg.
  case e : (enum N(w)) => [|a [|b [|c [|? ?]]]] //= _.
  have wa : w -- a by rewrite -in_opn -mem_enum e inE eqxx.
  have := @g267_closed_nbhd_drop G w [set w; a; b; c]; rewrite -(st w a b c wa) ltnn => h0.
  have : false; last by [].
  apply: h0; first by rewrite !inE eqxx.
  apply/subsetP => z; rewrite -mem_enum e !inE; case/or3P => /eqP ->; by rewrite eqxx !(orbT, orTb).
- move=> h N; have [G [hN reg col st]] := h N; exists G; split=> // u v x y uv _; exact: st.
Qed.

(** #01, hyp_inhabited: K_(4,4) is 4-regular, 4-edge-colourable and has an edge; a graph the statement supplies
    has an edge, so the alpha condition is not vacuous there. *)
Definition g267_regular_hyp_claim : Prop :=
  [/\ 0 < #|'K_4,4|, regular ('K_4,4) 4, (exists col : {set 'K_4,4} -> 'I_4, proper_edge_colouring col),
      (exists u v : 'I_4.-1 -> 'K_4,4, forall i, u i -- v i) &
      (regular_alpha_stable_statement ->
         exists (d : nat) (G : sgraph), 4 <= d /\ exists u v : 'I_d.-1 -> G, forall i, u i -- v i)].

Theorem g267_regular_hyp_inhabited : g267_regular_hyp_claim.
Proof.
split; [by rewrite card_sum !card_ord | exact: g267_kb_regular | | |].
- by exists (@g267_kb_col 3); exact: g267_kb_proper.
- by exists (fun _ => inl ord0), (fun _ => inr ord0).
- move=> [d [G [d4 G0 reg _ _]]]; exists d, G; split=> //.
  have [w _] := card_gt0P G0.
  have : 0 < #|N(w)| by rewrite reg (leq_trans _ d4).
  by case/card_gt0P => a; rewrite in_opn => wa; exists (fun _ => w), (fun _ => a).
Qed.

(** #01, not_trivially_true: without "u i -- v i" the statement is false (the 2(d - 1) >= d + 1 deleted vertices
    can cover a vertex and its d neighbours). *)
Definition g267_regular_no_edge : Prop :=
  exists (d : nat) (G : sgraph),
    [/\ 4 <= d, 0 < #|G|, regular G d, (exists col : {set G} -> 'I_d, proper_edge_colouring col) &
      forall u v : 'I_d.-1 -> G,
        α([set: G]) = α([set: G] :\: ([set u i | i in 'I_d.-1] :|: [set v i | i in 'I_d.-1]))].

Definition g267_regular_ntt_claim : Prop :=
  ~ g267_regular_no_edge /\ (g267_regular_no_edge -> regular_alpha_stable_statement).

Theorem g267_regular_not_trivially_true : g267_regular_ntt_claim.
Proof.
split.
- move=> [d [G [d4 G0 reg _ st]]].
  have [w _] := card_gt0P G0.
  pose L := w :: enum N(w).
  have sL : size L = d.+1 by rewrite /= -cardE reg.
  pose u (i : 'I_d.-1) := nth w L i.
  pose v (i : 'I_d.-1) := nth w L (i + 2).
  have cover (k : nat) : k < d.+1 -> nth w L k \in [set u i | i in 'I_d.-1] :|: [set v i | i in 'I_d.-1].
    move=> kd; rewrite inE; case: (ltnP k d.-1) => kd1.
    + by apply/orP; left; apply/imsetP; exists (Ordinal kd1).
    + have k2 : 2 <= k by apply: leq_trans kd1; rewrite -subn1 leq_subRL ?(leq_trans _ d4).
      have k2d : k - 2 < d.-1 by rewrite -(ltn_add2r 2) subnK // addn2 prednK ?(leq_trans _ d4).
      by apply/orP; right; apply/imsetP; exists (Ordinal k2d) => //; rewrite /v /= subnK.
  have wC := cover 0 (ltn0Sn d).
  have NC : N(w) \subset [set u i | i in 'I_d.-1] :|: [set v i | i in 'I_d.-1].
    apply/subsetP => z zN; have zL : z \in L by rewrite inE mem_enum zN orbT.
    by have := cover (index z L); rewrite nth_index //; apply; rewrite -sL index_mem.
  have := g267_closed_nbhd_drop wC NC; rewrite -(st u v) ltnn => h0; by [].
- move=> [d [G [d4 G0 reg col st]]]; exists d, G; split=> // u v _; exact: st.
Qed.

(** * Chromatic.conjectures.grounding_X264 -- grounding certificates for wave X264 (2026-10-30)

    For each of the three rows: hyp_inhabited (the hypotheses hold at a small instance, and the statement then gives
    its conclusion there) and not_trivially_true (a variant without one hypothesis or coupling is false and implies
    the statement); helper_sanity for the three helper groups (strong product, defective colourability, rainbow
    stackings), listed in every row.  Value lemmas: the strong product's two adjacency forms; chi(G) <= k iff G has a
    proper colouring by 'I_k; defect 0 is a proper colouring; defective colourability is upward closed in k; lifting
    a proper colouring of G to G boxtimes K_(d+1); X210's single-conflict colourability at p = 1, q = k is the
    exactly-one form for k > 0 and is upward closed in k; the guard 0 < k is load-bearing; the first permutation of
    a rainbow stacking may be the identity; x + y mod 3 is a proper edge-colouring of K_3. *)

From GTBase Require Import base common edge_colourings.
From mathcomp Require Import fingroup perm.
From Chromatic.conjectures Require Import X210 X264.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Small graphs ************************************************************* *)

(** Every vertex of a graph has at most #|G| - 1 neighbours; in K_n exactly n - 1. *)
Lemma g264_N_card (G : sgraph) (v : G) : #|N(v)| <= #|G|.-1.
Proof.
have : N(v) \subset [set~ v].
  by apply/subsetP => u; rewrite in_opn !inE; apply: contraTneq => ->; rewrite sg_irrefl.
by move/subset_leq_card; rewrite cardsC1.
Qed.

Lemma g264_K_N (n : nat) (v : 'K_n) : N(v) = [set~ v].
Proof. by apply/setP => u; rewrite in_opn !inE /edge_rel /= eq_sym. Qed.

(** chi(K_n) = n. *)
Lemma g264_chi_K (n : nat) : χ([set: 'K_n]) = n.
Proof.
have cl : clique [set: 'K_n] by move=> x y _ _ xy; rewrite /edge_rel /= xy.
by rewrite chi_clique // cardsT card_ord.
Qed.

(** K_(d+1) is d-degenerate. *)
Lemma g264_K_degenerate (d : nat) : k_degenerate ('K_d.+1) d.
Proof.
move=> S _ /set0Pn [x xS]; exists x; split=> //.
apply: leq_trans (subset_leq_card (subsetIl _ _)) _.
by apply: leq_trans (g264_N_card x) _; rewrite card_ord.
Qed.

(** ** The strong product *)

(** The GKZ footnote's three cases: distinct, and in each coordinate equal or adjacent. *)
Lemma g264_strong_relE (G H : sgraph) (x y : G * H) :
  x264_strong_rel x y = (x != y) && ((x.1 == y.1) || x.1 -- y.1) && ((x.2 == y.2) || x.2 -- y.2).
Proof.
case: x y => [a b] [c e]; rewrite /x264_strong_rel /box_rel /tensor_rel /= xpair_eqE.
case: (eqVneq a c) => [<-|ac]; case: (eqVneq b e) => [<-|be]; rewrite ?sg_irrefl ?eqxx /=;
  by case: (a -- _); case: (b -- _).
Qed.

(** Norin and Steiner's form for H = K_t (2504.01548v1 l.114): (u,i) ~ (v,j) iff u = v and i <> j, or uv is an
    edge. *)
Lemma g264_strong_KE (G : sgraph) (t : nat) (x y : x264_strong_product G ('K_t)) :
  x -- y = ((x.1 == y.1) && (x.2 != y.2)) || x.1 -- y.1.
Proof.
rewrite /edge_rel /= g264_strong_relE; case: x y => [a b] [c e] /=; rewrite xpair_eqE.
have -> : b -- e = (b != e) by [].
case: (eqVneq b e) => [be|be].
all: rewrite ?andbT ?andbF ?orbT ?orbF /=; case: (eqVneq a c) => [->|ac] /=; rewrite ?sg_irrefl ?andbF ?orbF //.
Qed.

(** ** Colourings and the chromatic number *)

(** chi(G) <= k gives a proper colouring by 'I_k (each vertex coloured by the index of its class). *)
Lemma g264_chi_colouring (G : sgraph) (k : nat) :
  χ([set: G]) <= k -> exists col : G -> 'I_k, forall x y : G, x -- y -> col x != col y.
Proof.
case: chiP => P /andP[hp /forall_inP hs] _ hk.
have hb x : pblock P x \in P by apply: pblock_mem; rewrite (cover_partition hp) inE.
pose c x := index (pblock P x) (enum P).
have hc x : c x < k by apply: leq_trans hk; rewrite cardE index_mem mem_enum hb.
exists (fun x => Ordinal (hc x)) => x y xy; apply/negP => /eqP /(congr1 val) /= e.
have epb : pblock P x = pblock P y.
  by have := congr1 (nth (pblock P x) (enum P)) e; rewrite !nth_index ?mem_enum.
have hx : x \in pblock P x by rewrite mem_pblock (cover_partition hp) inE.
have hy : y \in pblock P x by rewrite epb mem_pblock (cover_partition hp) inE.
by have /stableP/(_ x y hx hy) := hs _ (hb x); rewrite xy.
Qed.

(** A proper colouring by 'I_k gives chi(G) <= k. *)
Lemma g264_colouring_chi (G : sgraph) (k : nat) (col : G -> 'I_k) :
  (forall x y : G, x -- y -> col x != col y) -> χ([set: G]) <= k.
Proof.
move=> hf; pose P := preim_partition col [set: G].
have hp : coloring P [set: G].
  apply/andP; split; first exact: preim_partitionP.
  apply/forall_inP=> A /imsetP[x _ ->]; apply/stableP.
  move=> y z; rewrite !inE /= => /eqP hy /eqP hz.
  by apply/negP=> hyz; have := hf y z hyz; rewrite -hy -hz eqxx.
apply: leq_trans (color_bound hp) _.
pose fiber c := [set x : G | c == col x].
have hsub : P \subset [set fiber c | c in [set: 'I_k]].
  apply/subsetP=> A /imsetP[x _ ->]; apply/imsetP.
  by exists (col x); [rewrite inE | apply/setP=> y; rewrite /fiber !inE].
apply: leq_trans (subset_leq_card hsub) _.
by have := leq_imset_card fiber [set: 'I_k]; rewrite cardsT card_ord.
Qed.

(** Defect 0 is a proper colouring: x264_defective_colourable G 0 k iff chi(G) <= k. *)
Lemma g264_defective0 (G : sgraph) (k : nat) : x264_defective_colourable G 0 k <-> χ([set: G]) <= k.
Proof.
split=> [[col h]|/g264_chi_colouring [col h]].
  apply: (g264_colouring_chi (col := col)) => x y xy; apply/negP => /eqP e.
  have := h x; rewrite leqn0 cards_eq0 => /eqP /setP /(_ y).
  by rewrite !inE xy e eqxx.
exists col => v; rewrite leqn0 cards_eq0; apply/eqP/setP => u; rewrite !inE.
by apply/negP => /andP[vu /eqP e]; have := h v u vu; rewrite e eqxx.
Qed.

(** More colours never hurt: x264_defective_colourable is upward closed in k, so its least k is chi^d. *)
Lemma g264_defective_mono (G : sgraph) (d k k' : nat) :
  k <= k' -> x264_defective_colourable G d k -> x264_defective_colourable G d k'.
Proof.
move=> kk [col h]; exists (fun v => widen_ord kk (col v)) => v.
(* widen_ord keeps the value, so the two colour classes are the same set by conversion. *)
by rewrite (_ : [set u | widen_ord kk (col u) == widen_ord kk (col v)] = [set u | col u == col v]) ?h.
Qed.

(** Lifting (GKZ l.132, Norin-Steiner l.120): chi(G) <= k gives a d-defective k-colouring of G x K_(d+1). *)
Lemma g264_lift (G : sgraph) (d k : nat) :
  χ([set: G]) <= k -> x264_defective_colourable (x264_strong_product G ('K_d.+1)) d k.
Proof.
move=> /g264_chi_colouring [col hcol]; exists (fun p => col p.1) => v.
have sub : N(v) :&: [set u : x264_strong_product G ('K_d.+1) | col u.1 == col v.1]
    \subset [set (v.1, j) | j in [set~ v.2]].
  apply/subsetP => u; rewrite !inE g264_strong_KE => /andP[/orP[/andP[/eqP e1 e2]|uv] /eqP ec].
    apply/imsetP; exists u.2; first by rewrite !inE eq_sym.
    by rewrite e1; case: u {e1 e2 ec}.
  by have := hcol _ _ uv; rewrite ec eqxx.
apply: leq_trans (subset_leq_card sub) _; apply: leq_trans (leq_imset_card _ _) _.
by rewrite cardsC1 card_ord.
Qed.

(** ** Single-conflict colourings *)

(** For positive k, X210's helper at p = 1, q = k (at most one forbidden pair per edge) is single-conflict
    k-colourability with exactly one pair per edge (1803.10962v2, dp1.tex l.85-90): kap u v is the pair of local
    colours of u and v on the edge uv, kap v u its transpose. *)
Lemma g264_single_conflictE (G : sgraph) (k : nat) : 0 < k ->
  x210_conflict_k_colourable_under_rat_bound G k 1 k <->
  forall kap : G -> G -> 'I_k * 'I_k,
    (forall u v : G, u -- v -> kap v u = ((kap u v).2, (kap u v).1)) ->
    exists col : G -> 'I_k, forall u v : G, u -- v -> (col u, col v) != kap u v.
Proof.
move=> k0; split=> [h kap ksym|h F [Fsym Fcard]].
  have [|col hcol] := h (fun u v a b => (u -- v) && ((a, b) == kap u v)).
    split=> [u v uv a b|u v uv].
      rewrite uv sg_sym uv /= (ksym u v uv); case: (kap u v) => p q /=.
      by rewrite !xpair_eqE andbC.
    rewrite mul1n -[X in _ <= X]muln1 leq_mul2l; apply/orP; right.
    apply: leq_trans (subset_leq_card (_ : _ \subset [set kap u v])) _; last by rewrite cards1.
    by apply/subsetP => ab; rewrite !inE => /andP[_ /eqP <-]; case: ab.
  by exists col => u v uv; have := hcol u v uv; rewrite uv.
have le1 u v : u -- v -> #|[set ab : 'I_k * 'I_k | F u v ab.1 ab.2]| <= 1.
  by move=> uv; have := Fcard u v uv; rewrite mul1n -[X in _ <= X]muln1 leq_pmul2l.
pose a0 : 'I_k := Ordinal k0.
pose kap u v := odflt (a0, a0) [pick ab | F u v ab.1 ab.2].
have kapP u v ab : u -- v -> F u v ab.1 ab.2 -> kap u v = ab.
  move=> uv Fab; rewrite /kap; case: pickP => [ab' Fab'|/(_ ab)]; last by rewrite Fab.
  by apply: (card_le1_eqP (le1 u v uv)); rewrite inE.
have [|col hcol] := h kap.
  move=> u v uv; have vu : v -- u by rewrite sg_sym.
  case: (pickP (fun ab : 'I_k * 'I_k => F u v ab.1 ab.2)) => [[a b] /= Fab|none].
    by rewrite (kapP u v (a, b) uv Fab) /=; apply: kapP => //=; rewrite -(Fsym u v uv).
  have ku : kap u v = (a0, a0) by rewrite /kap; case: pickP => [ab Fab|//]; rewrite none in Fab.
  have kv : kap v u = (a0, a0).
    rewrite /kap; case: pickP => [[a b] /= Fba|//].
    by have := none (b, a); rewrite /= (Fsym u v uv) Fba.
  by rewrite ku kv.
exists col => u v uv; apply/negP => Fuv.
by have := hcol u v uv; rewrite (kapP u v (col u, col v)) ?eqxx.
Qed.

(** Single-conflict k-colourability is upward closed in k > 0: a pair of colours outside 'I_k is never met by a
    colouring into 'I_k. *)
Lemma g264_single_conflict_mono (G : sgraph) (k k' : nat) : 0 < k -> k <= k' ->
  x210_conflict_k_colourable_under_rat_bound G k 1 k -> x210_conflict_k_colourable_under_rat_bound G k' 1 k'.
Proof.
move=> k0 kk h F' [Fsym Fcard].
have k'0 : 0 < k' := leq_trans k0 kk.
pose w := widen_ord kk.
have [|col hcol] := h (fun u v a b => F' u v (w a) (w b)).
  split=> [u v uv a b|u v uv]; first exact: Fsym.
  have le1 : #|[set ab : 'I_k' * 'I_k' | F' u v ab.1 ab.2]| <= 1.
    by have := Fcard u v uv; rewrite mul1n -[X in _ <= X]muln1 leq_pmul2l.
  rewrite mul1n -[X in _ <= X]muln1 leq_pmul2l //; apply: leq_trans le1.
  have winj : injective (fun ab : 'I_k * 'I_k => (w ab.1, w ab.2)).
    move=> [a b] [c e] /= [/eqP ac /eqP be]; congr pair; apply/eqP; [move: ac | move: be];
    by rewrite -val_eqE /= val_eqE.
  rewrite -(card_imset _ winj); apply: subset_leq_card; apply/subsetP => ab /imsetP [[a b]].
  by rewrite !inE /= => Fab ->.
by exists (fun v => w (col v)) => u v uv; exact: hcol.
Qed.

(** ** Rainbow stackings *)

(** For two colourings the first permutation may be the identity (2405.14795v1 l.106: a common relabelling of
    the vertices; it is not a colour permutation). *)
Lemma g264_rainbow_stacking_id (n r : nat) (chi1 chi2 : {set 'K_n} -> 'I_r) :
  (exists s1 s2 : {perm 'I_n}, x264_rainbow_stacking chi1 chi2 s1 s2) <->
  exists s : {perm 'I_n}, x264_rainbow_stacking chi1 chi2 1%g s.
Proof.
split=> [[s1 [s2 h]]|[s h]]; last by exists 1%g, s.
exists (s1 * s2^-1)^-1%g => i j ij; rewrite invg1 !perm1 invgK !permM.
have := h (s1 i) (s1 j); rewrite !permK; apply.
by rewrite /edge_rel /= (inj_eq perm_inj).
Qed.

(** The colouring {x, y} |-> x + y mod 3 of K_3 (proper: x + y = x + z mod 3 forces y = z). *)
Definition g264_K3_col (e : {set 'K_3}) : 'I_3 := inord ((\sum_(v in e) (v : nat)) %% 3).

Lemma g264_K3_col2 (x y : 'K_3) : x != y -> g264_K3_col [set x; y] = inord ((x + y) %% 3).
Proof. by move=> xy; rewrite /g264_K3_col big_setU1 /= ?big_set1 // inE. Qed.

Lemma g264_K3_col_proper : proper_edge_colouring g264_K3_col.
Proof.
move=> x y z xy xz yz; rewrite !g264_K3_col2 //.
apply: contra yz => /eqP /(congr1 val); rewrite /= !inordK ?ltn_pmod // => /eqP.
by rewrite eqn_modDl !modn_small ?ltn_ord // => /eqP e; apply/eqP/val_inj.
Qed.

(** ** Certificates *)

(** studies:std_guo_kang_zwaneveld_conjecture *)
Definition g264_gkz_hyp_claim : Prop :=
  x264_defective_colourable (x264_strong_product ('K_2) ('K_2)) 1 2 /\
  (guo_kang_zwaneveld_defective_strong_product_statement ->
     forall k : nat, x264_defective_colourable (x264_strong_product ('K_2) ('K_2)) 1 k -> 2 <= k).

Theorem g264_gkz_hyp_inhabited : g264_gkz_hyp_claim.
Proof.
split; first by apply: g264_lift; rewrite g264_chi_K.
by move=> h k /(h ('K_2) 1 k).2; rewrite g264_chi_K.
Qed.

Definition g264_gkz_any_blowup : Prop :=
  forall (G : sgraph) (d t k : nat),
    χ([set: G]) <= k <-> x264_defective_colourable (x264_strong_product G ('K_t)) d k.

Definition g264_gkz_ntt_claim : Prop :=
  ~ g264_gkz_any_blowup /\ (g264_gkz_any_blowup -> guo_kang_zwaneveld_defective_strong_product_statement).

Theorem g264_gkz_not_trivially_true : g264_gkz_ntt_claim.
Proof.
split; last by move=> h G d k; exact: h.
move=> h; have := (h ('K_2) 1 1 1).2; rewrite g264_chi_K.
suff hP : x264_defective_colourable (x264_strong_product ('K_2) ('K_1)) 1 1 by move/(_ hP).
exists (fun _ => ord0) => v; apply: leq_trans (subset_leq_card (subsetIl _ _)) _.
by apply: leq_trans (g264_N_card v) _; rewrite /= card_prod !card_ord.
Qed.

(** arxiv:1803.10962#01 *)
Definition g264_sc_hyp_claim : Prop :=
  k_degenerate ('K_2) 1 /\
  (degenerate_single_conflict_sqrt_log_statement ->
     exists k : nat, 0 < k /\ x210_conflict_k_colourable_under_rat_bound ('K_2) k 1 k).

Theorem g264_sc_hyp_inhabited : g264_sc_hyp_claim.
Proof.
split; first exact: g264_K_degenerate.
move=> [C hC]; exists C.+1; split=> //; apply: hC => //; first exact: g264_K_degenerate.
by rewrite card_ord (trunc_expnK 1 (isT : 1 < 2)) !muln1 leq_exp2r // leqnSn.
Qed.

Definition g264_sc_no_degeneracy : Prop :=
  exists C : nat,
    forall (G : sgraph) (d k : nat), 0 < k ->
      C ^ 2 * d * trunc_log 2 #|G| ^ 2 <= k ^ 2 ->
      x210_conflict_k_colourable_under_rat_bound G k 1 k.

Definition g264_sc_ntt_claim : Prop :=
  ~ g264_sc_no_degeneracy /\ (g264_sc_no_degeneracy -> degenerate_single_conflict_sqrt_log_statement).

Theorem g264_sc_not_trivially_true : g264_sc_ntt_claim.
Proof.
split; last by move=> [C hC]; exists C => G d k k0 _; exact: hC.
move=> [C hC]; apply: x210_conflict_bound_teeth; apply: (hC ('K_2) 0 1) => //.
by rewrite muln0 mul0n.
Qed.

(** The guard 0 < k is load-bearing: without it, K_1 (0-degenerate, trunc_log 2 1 = 0) would need a colouring by
    no colour. *)
Lemma g264_sc_guard_teeth (C : nat) :
  ~ (forall (G : sgraph) (d k : nat), k_degenerate G d ->
       C ^ 2 * d * trunc_log 2 #|G| ^ 2 <= k ^ 2 ->
       x210_conflict_k_colourable_under_rat_bound G k 1 k).
Proof.
move=> h; have [] := h ('K_1) 0 0 (@g264_K_degenerate 0) _ (fun _ _ _ _ => false).
- by rewrite muln0 mul0n.
- by split=> // u v _; rewrite !mul0n.
by move=> col _; case: (col ord0).
Qed.

(** arxiv:2405.14795#01 *)
Definition g264_rs_hyp_claim : Prop :=
  [/\ odd 3, proper_edge_colouring g264_K3_col &
      (odd_complete_proper_edge_colourings_rainbow_stacking_statement ->
         exists s1 s2 : {perm 'I_3}, x264_rainbow_stacking g264_K3_col g264_K3_col s1 s2)].

Theorem g264_rs_hyp_inhabited : g264_rs_hyp_claim.
Proof.
split=> //; first exact: g264_K3_col_proper.
by move=> h; apply: h => //; exact: g264_K3_col_proper.
Qed.

Definition g264_rs_any_order : Prop :=
  forall (n r : nat) (chi1 chi2 : {set 'K_n} -> 'I_r),
    proper_edge_colouring chi1 -> proper_edge_colouring chi2 ->
    exists s1 s2 : {perm 'I_n}, x264_rainbow_stacking chi1 chi2 s1 s2.

Definition g264_rs_ntt_claim : Prop :=
  ~ g264_rs_any_order /\ (g264_rs_any_order -> odd_complete_proper_edge_colourings_rainbow_stacking_statement).

Theorem g264_rs_not_trivially_true : g264_rs_ntt_claim.
Proof.
split; last by move=> h n r c1 c2 _; exact: h.
move=> h; have [s1 [s2 hs]] := h 2 1 (fun _ => ord0) (fun _ => ord0)
  (proper_edge_colouring_K2 ord0) (proper_edge_colouring_K2 ord0).
by have := hs ord0 ord_max isT; rewrite eqxx.
Qed.

(** ** Helper sanity (the same three groups in every row) *)

(** The strong product: the GKZ footnote's three cases, and Norin and Steiner's form for H = K_t. *)
Definition g264_sp_helper_claim : Prop :=
  (forall (G H : sgraph) (x y : G * H),
     x264_strong_rel x y = (x != y) && ((x.1 == y.1) || x.1 -- y.1) && ((x.2 == y.2) || x.2 -- y.2)) /\
  (forall (G : sgraph) (t : nat) (x y : x264_strong_product G ('K_t)),
     x -- y = ((x.1 == y.1) && (x.2 != y.2)) || x.1 -- y.1).

Theorem g264_sp_helper_sanity : g264_sp_helper_claim.
Proof. by split; [exact: g264_strong_relE | exact: g264_strong_KE]. Qed.

(** Defective colourings: defect 0 is a proper colouring; K_3 is 2-defective but not 1-defective with one colour. *)
Definition g264_dc_helper_claim : Prop :=
  [/\ forall (G : sgraph) (k : nat), x264_defective_colourable G 0 k <-> χ([set: G]) <= k,
      x264_defective_colourable ('K_3) 2 1 & ~ x264_defective_colourable ('K_3) 1 1].

Theorem g264_dc_helper_sanity : g264_dc_helper_claim.
Proof.
split; first exact: g264_defective0.
  exists (fun _ => ord0) => v; apply: leq_trans (subset_leq_card (subsetIl _ _)) _.
  by apply: leq_trans (g264_N_card v) _; rewrite card_ord.
move=> [col h]; have := h ord0.
have -> : N(ord0 : 'K_3) :&: [set u | col u == col ord0] = [set~ ord0].
  by rewrite g264_K_N; apply/setP => u; rewrite !inE !ord1 eqxx andbT.
by rewrite cardsC1 card_ord.
Qed.

(** Rainbow stackings on K_2: two constant colourings stack rainbow iff their colours differ. *)
Definition g264_rs_helper_claim : Prop :=
  x264_rainbow_stacking (fun _ : {set 'K_2} => (ord0 : 'I_2)) (fun _ => ord_max) 1%g 1%g /\
  forall s1 s2 : {perm 'I_2},
    ~ x264_rainbow_stacking (fun _ : {set 'K_2} => (ord0 : 'I_1)) (fun _ => ord0) s1 s2.

Theorem g264_rs_helper_sanity : g264_rs_helper_claim.
Proof.
split=> // s1 s2 hs.
by have := hs ord0 ord_max isT; rewrite eqxx.
Qed.


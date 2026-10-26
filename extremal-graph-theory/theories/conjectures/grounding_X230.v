(** * Extremal.conjectures.grounding_X230 -- grounding certificates of the X230 pilot wave.

    Each row of X230.v gets a [*_hyp_inhabited] certificate (the hypotheses hold on a small
    witness, and the row has content there) and a [*_not_trivially_true] certificate (dropping
    a load-bearing hypothesis gives a stronger statement, which is false). Six helper-sanity
    certificates pin every x230 helper to a textbook value on small instances: the book number
    of K_n is n - 2; the complement of C_6 is the 3-prism S_{1,6}; K_n contains C(n, m) copies
    of K_m; r(K_1) = 1 and r(K_2) = 2; Ramsey numbers and threshold multiplicities are unique.

    The witnesses are the 3-prism [compl (cycle_graph 6)] (S_{1,6}, n = 6, b = 1) and K_{3,3},
    the excluded balanced complete bipartite graph. Facts about these concrete graphs on ['I_6]
    are checked by [vm_compute] after [enum 'I_6] is rewritten to an explicit list (the library
    enumeration goes through [insub] and does not evaluate). Everything is closed by [Qed]; see
    the [Print Assumptions] audit at the end. *)

From GTBase Require Import base common clique_counts path_graphs.
From Extremal.conjectures Require Import X230.
(* MathComp last: X230 re-exports GTBase.base, whose GraphTheory notations would otherwise shadow
   the ring notations (the 1 of the rat window in [g230_growth_hyp_claim]). *)
From mathcomp Require Import all_algebra zify.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

(** ** Finite checks on ['I_6] *)
Definition g230_I6 : seq 'I_6 :=
  [:: @Ordinal 6 0 isT; @Ordinal 6 1 isT; @Ordinal 6 2 isT;
      @Ordinal 6 3 isT; @Ordinal 6 4 isT; @Ordinal 6 5 isT].

Lemma g230_enum6 : enum 'I_6 = g230_I6.
Proof. by apply: (inj_map val_inj); rewrite val_enum_ord. Qed.

Lemma g230_all6 (P : pred 'I_6) : all P g230_I6 -> forall x, P x.
Proof. by move=> /allP h x; apply: h; rewrite -g230_enum6 mem_enum. Qed.

Lemma g230_all66 (P : 'I_6 -> 'I_6 -> bool) :
  all (fun x => all (P x) g230_I6) g230_I6 -> forall x y, P x y.
Proof.
move=> h x; apply: g230_all6; move: x.
exact: (g230_all6 (P := fun x => all (P x) g230_I6)).
Qed.

Lemma g230_card6 (P : pred 'I_6) : #|P| = count P g230_I6.
Proof. by rewrite cardE /enum_mem -enumT g230_enum6 size_filter. Qed.

Lemma g230_cards6 (P : pred 'I_6) : #|[set x | P x]| = count P g230_I6.
Proof. by rewrite cardsE g230_card6. Qed.

(** ** The 3-prism S_{1,6} as the complement of C_6 *)

Definition g230_P : sgraph := compl (cycle_graph 6).

Lemma g230_P_card : #|g230_P| = 6.
Proof. exact: card_ord. Qed.

Lemma g230_P_deg (x : g230_P) : #|N(x)| = 3.
Proof.
rewrite (g230_cards6 (fun y => @edge_rel g230_P x y)); apply/eqP; move: x.
apply: (g230_all6 (P := fun x : 'I_6 => count (fun y => @edge_rel g230_P x y) g230_I6 == 3)).
by vm_compute.
Qed.

Lemma g230_P_edges : #|E(g230_P)| = 9.
Proof.
apply/eqP; rewrite -(eqn_pmul2l (isT : 0 < 2)) edges_sum_degrees.
rewrite (eq_bigr (fun _ => 3)); first by move=> x _; exact: g230_P_deg.
by rewrite sum_nat_const card_ord.
Qed.

Lemma g230_P_book : x230_book_at_most g230_P 1.
Proof.
have h : forall x y : 'I_6, (@edge_rel g230_P x y) ==>
    (count (fun z => (@edge_rel g230_P x z) && (@edge_rel g230_P y z)) g230_I6 <= 1).
  apply: (g230_all66 (P := fun x y : 'I_6 => (@edge_rel g230_P x y) ==>
    (count (fun z => (@edge_rel g230_P x z) && (@edge_rel g230_P y z)) g230_I6 <= 1))).
  by vm_compute.
move=> x y xy.
rewrite (g230_cards6 (fun z => (@edge_rel g230_P x z) && (@edge_rel g230_P y z))).
exact: (implyP (h x y) xy).
Qed.

Lemma g230_KB_no_triangle3 (m n : nat) (a b c : 'K_m,n) : a -- b -> b -- c -> a -- c -> False.
Proof. by rewrite /edge_rel /= /kb_rel; case: a => ?; case: b => ?; case: c => ?. Qed.

Lemma g230_P_not_K33 : ~ inhabited (diso g230_P 'K_3,3).
Proof.
case=> i.
have h (u v : g230_P) : u -- v -> bij.bij_fwd i u -- bij.bij_fwd i v by rewrite edge_diso.
apply: (@g230_KB_no_triangle3 3 3 (bij.bij_fwd i (@Ordinal 6 0 isT))
  (bij.bij_fwd i (@Ordinal 6 2 isT)) (bij.bij_fwd i (@Ordinal 6 4 isT))); apply: h; by vm_compute.
Qed.

Definition g230_lab (v : 'I_6) : 'I_6 :=
  nth ord0 [:: @Ordinal 6 0 isT; @Ordinal 6 5 isT; @Ordinal 6 1 isT;
               @Ordinal 6 3 isT; @Ordinal 6 2 isT; @Ordinal 6 4 isT] v.

Lemma g230_P_blowup : x230_prism_blowup 1 6 g230_P.
Proof.
exists g230_lab; split.
- move=> x y; apply/eqP; move: x y.
  apply: (g230_all66 (P := fun x y : 'I_6 =>
    (@edge_rel g230_P x y) == x230_prism_rel (g230_lab x) (g230_lab y))).
  by vm_compute.
- move=> i; rewrite (g230_cards6 (fun x => g230_lab x == i)); apply/eqP; move: i.
  apply: (g230_all6 (P := fun i : 'I_6 => count (fun x => g230_lab x == i) g230_I6 ==
    nth 0 [:: 1; 1; (6 - 4 * 1) %/ 2; 1; 1; (6 - 4 * 1) - (6 - 4 * 1) %/ 2] i)).
  by vm_compute.
Qed.

(** ** The complete bipartite graph K_{m,l} *)

Lemma g230_KB_card (m n : nat) : #|'K_m,n| = m + n.
Proof. by rewrite card_sum !card_ord. Qed.

Lemma g230_KB_deg (m n : nat) (x : 'K_m,n) : #|N(x)| = if x is inl _ then n else m.
Proof.
case: x => i.
- have -> : N(inl i : 'K_m,n) = inr @: [set: 'I_n].
    apply/setP => -[j|j]; rewrite !inE /edge_rel /= /kb_rel /=.
    + by apply/esym/imsetP => -[k _].
    + by rewrite imset_f // inE.
  by rewrite card_imset ?cardsT ?card_ord //; exact: inr_inj.
- have -> : N(inr i : 'K_m,n) = inl @: [set: 'I_m].
    apply/setP => -[j|j]; rewrite !inE /edge_rel /= /kb_rel /=.
    + by rewrite imset_f // inE.
    + by apply/esym/imsetP => -[k _].
  by rewrite card_imset ?cardsT ?card_ord //; exact: inl_inj.
Qed.

Lemma g230_KB_edges (m n : nat) : #|E('K_m,n)| = m * n.
Proof.
apply/eqP; rewrite -(eqn_pmul2l (isT : 0 < 2)) edges_sum_degrees.
rewrite (eq_bigr (fun x : 'K_m,n => if x is inl _ then n else m)); first by move=> x _; exact: g230_KB_deg.
rewrite big_sumType /= !sum_nat_const.
rewrite (eq_card (B := 'I_m)) // (eq_card (B := 'I_n)) // !card_ord.
by rewrite mulnC mul2n addnn.
Qed.

Lemma g230_KB_book (m n b : nat) : x230_book_at_most 'K_m,n b.
Proof.
move=> x y xy; apply: leq_trans (_ : _ <= 0) _ => //; rewrite leqn0 cards_eq0.
apply/eqP/setP => z; rewrite !inE; move: xy; rewrite /edge_rel /= /kb_rel.
by case: x => ?; case: y => ?; case: z => ?.
Qed.

Lemma g230_KB_no_triangle (m n : nat) : clique_count_size 'K_m,n 3 = 0.
Proof.
apply/eqP; rewrite cards_eq0; apply/eqP/setP => S; rewrite !inE.
apply/negbTE/negP => /andP[/andP[_ Scl] /eqP S3].
have inj : {in S &, injective (fun x : 'K_m,n => is_inl x)}.
  move=> x y xS yS /= exy; apply/eqP; apply/negPn/negP => nxy.
  move/forall_inP: Scl => /(_ x xS) /forall_inP /(_ y yS) /implyP /(_ nxy).
  by rewrite /edge_rel /= /kb_rel exy addbb.
have := max_card [set (fun x : 'K_m,n => is_inl x) x | x in S].
by rewrite card_in_imset // S3 card_bool.
Qed.

(** ** One-vertex patterns: one copy per host vertex, r = 1, m = 2 *)

Lemma g230_card_compl (G : sgraph) : #|compl G| = #|G|.
Proof. by []. Qed.

Lemma g230_one_eq (H : sgraph) : #|H| = 1 -> forall x y : H, x = y.
Proof.
move=> H1 x y; apply/eqP; apply: contraT => nxy.
have : 1 < #|H| by apply/card_gt1P; exists x, y.
by rewrite H1.
Qed.

Lemma g230_one_noedge (H : sgraph) : #|H| = 1 -> forall x y : H, (x -- y) = false.
Proof. by move=> H1 x y; rewrite (g230_one_eq H1 x y) sg_irrefl. Qed.

Lemma g230_emb_one (H G : sgraph) : #|H| = 1 -> x230_embeddings H G = setT.
Proof.
move=> H1; apply/setP => f; rewrite !inE; apply/andP; split.
- by apply/injectiveP => x y _; exact: g230_one_eq.
- by apply/forallP => x; apply/forallP => y; rewrite g230_one_noedge.
Qed.

Lemma g230_aut_one (H : sgraph) : #|H| = 1 -> x230_automorphisms H = setT.
Proof.
move=> H1; apply/setP => f; rewrite /x230_automorphisms g230_emb_one // !inE.
by apply/forallP => x; apply/forallP => y; rewrite g230_one_noedge.
Qed.

Lemma g230_copies_one (H G : sgraph) : #|H| = 1 -> x230_copies H G = #|G|.
Proof.
move=> H1; rewrite /x230_copies g230_emb_one // g230_aut_one //.
by rewrite !cardsT !card_ffun H1 !expn1 divn1.
Qed.

Lemma g230_mono_one (H G : sgraph) : #|H| = 1 -> x230_mono_copies H G = 2 * #|G|.
Proof. by move=> H1; rewrite /x230_mono_copies !g230_copies_one // mul2n -addnn. Qed.

Lemma g230_arrows_card (H : sgraph) (R : nat) : x230_arrows R H -> #|H| <= R.
Proof.
move=> /(_ 'K_R (card_ord R)) [] /has_subgraph_card; by rewrite ?g230_card_compl card_ord.
Qed.

Lemma g230_ramsey_card (H : sgraph) (R : nat) : x230_ramsey_number H R -> #|H| <= R.
Proof. by case=> /g230_arrows_card. Qed.

Lemma g230_arrows_one (H : sgraph) (R : nat) : #|H| = 1 -> x230_arrows R H <-> 0 < R.
Proof.
move=> H1; split; first by move/g230_arrows_card; rewrite H1.
move=> R0 G GR; left; apply/has_subgraphP.
have /card_gt0P [v _] : 0 < #|G| by rewrite GR.
exists (fun _ => v); split; first by move=> x y _; exact: g230_one_eq.
by move=> x y; rewrite g230_one_noedge.
Qed.

Lemma g230_ramsey_one (H : sgraph) : #|H| = 1 -> x230_ramsey_number H 1.
Proof.
move=> H1; split; first exact/(g230_arrows_one 1 H1).
by move=> R' /(g230_arrows_one R' H1).
Qed.

Lemma g230_ramsey_unique (H : sgraph) (R R' : nat) :
  x230_ramsey_number H R -> x230_ramsey_number H R' -> R = R'.
Proof. by case=> a ma [a' ma']; apply/eqP; rewrite eqn_leq ma // ma'. Qed.

Lemma g230_threshold_unique (H : sgraph) (m m' : nat) :
  x230_threshold_multiplicity H m -> x230_threshold_multiplicity H m' -> m = m'.
Proof.
case=> R [rR low [G GR Gm]] [R' [rR' low' [G' GR' Gm']]].
have eR := g230_ramsey_unique rR rR'.
have h1 : m <= m' by rewrite -Gm'; apply: low; rewrite GR' -eR.
have h2 : m' <= m by rewrite -Gm; apply: low'; rewrite GR eR.
by apply/eqP; rewrite eqn_leq h1 h2.
Qed.

Lemma g230_threshold_one (H : sgraph) : #|H| = 1 -> x230_threshold_multiplicity H 2.
Proof.
move=> H1; exists 1; split; first exact: g230_ramsey_one.
- by move=> G G1; rewrite g230_mono_one // G1.
- by exists 'K_1; [exact: card_ord | rewrite g230_mono_one // card_ord].
Qed.

(** ** Copies of K_m in K_n *)

Lemma g230_emb_KK (m n : nat) :
  x230_embeddings 'K_m 'K_n = [set f : {ffun 'K_m -> 'K_n} | injectiveb f].
Proof.
apply/setP => f; rewrite !inE; case: (injectiveP f) => //= inj.
apply/forallP => x; apply/forallP => y; apply/implyP.
by rewrite /edge_rel /= (inj_eq inj).
Qed.

Lemma g230_aut_K (m : nat) :
  x230_automorphisms 'K_m = [set f : {ffun 'K_m -> 'K_m} | injectiveb f].
Proof.
apply/setP => f; rewrite /x230_automorphisms g230_emb_KK !inE.
case: (injectiveP f) => //= inj.
apply/forallP => x; apply/forallP => y; apply/implyP.
by rewrite /edge_rel /= (inj_eq inj).
Qed.

Lemma g230_emb_card_KK (m n : nat) : #|x230_embeddings 'K_m 'K_n| = n ^_ m.
Proof. by rewrite g230_emb_KK card_inj_ffuns !card_ord. Qed.

Lemma g230_aut_card_K (m : nat) : #|x230_automorphisms 'K_m| = m`!.
Proof. by rewrite g230_aut_K card_inj_ffuns card_ord ffactnn. Qed.

Lemma g230_copies_KK (m n : nat) : x230_copies 'K_m 'K_n = 'C(n, m).
Proof.
rewrite /x230_copies g230_emb_card_KK g230_aut_card_K.
by rewrite -bin_ffact mulnK // fact_gt0.
Qed.

Lemma g230_emb_K2_compl_K (n : nat) : x230_embeddings 'K_2 (compl 'K_n) = set0.
Proof.
apply/setP => f; rewrite !inE; apply/negbTE; rewrite negb_and; apply/orP; right.
rewrite negb_forall; apply/existsP; exists ord0; rewrite negb_forall; apply/existsP; exists ord_max.
by rewrite negb_imply compl_Kn_edgeless andbT.
Qed.

Lemma g230_mono_K2_Kn (n : nat) : x230_mono_copies 'K_2 'K_n = 'C(n, 2).
Proof.
rewrite /x230_mono_copies g230_copies_KK /x230_copies g230_emb_K2_compl_K cards0 div0n.
by rewrite addn0.
Qed.

(** ** r(K_2) = 2 *)

Lemma g230_K2_ord (i : 'K_2) : i != ord0 -> i = ord_max.
Proof. by case: i => [[|[|?]] ?] // _; apply/val_inj. Qed.

Lemma g230_K2_edge (i j : 'K_2) : i -- j -> (i = ord0 /\ j = ord_max) \/ (i = ord_max /\ j = ord0).
Proof.
rewrite /edge_rel /=.
case: (eqVneq i ord0) => [->|/g230_K2_ord ->]; case: (eqVneq j ord0) => [->|/g230_K2_ord ->] //.
- by left.
- by right.
Qed.

Lemma g230_arrows_K2 (R : nat) : x230_arrows R 'K_2 <-> 2 <= R.
Proof.
split; first by move/g230_arrows_card; rewrite card_ord.
move=> R2 G GR.
have /card_gt1P [x [y [_ _ xy]]] : 1 < #|G| by rewrite GR.
pose f (i : 'K_2) : G := if i == ord0 then x else y.
have fx : f ord0 = x by rewrite /f eqxx.
have fy : f ord_max = y by [].
have finj : injective f.
  move=> i j.
  case: (eqVneq i ord0) => [->|/g230_K2_ord ->]; case: (eqVneq j ord0) => [->|/g230_K2_ord ->] //;
    rewrite fx fy => exy; by move: xy; rewrite exy eqxx.
case xyE : (x -- y); [left | right]; apply/has_subgraphP; exists f; split => // i j;
  case/g230_K2_edge => -[-> ->]; rewrite fx fy.
- by rewrite xyE.
- by rewrite sgP xyE.
- by rewrite /edge_rel /= xy xyE.
- by rewrite /edge_rel /= eq_sym xy sgP xyE.
Qed.

Lemma g230_ramsey_K2 : x230_ramsey_number 'K_2 2.
Proof. split; first exact/g230_arrows_K2. by move=> R' /g230_arrows_K2. Qed.

(** ** The book number of K_n is n - 2 *)

Lemma g230_book_Kn_common (n : nat) (x y : 'K_n) : x != y ->
  #|[set z | x -- z & y -- z]| = n - 2.
Proof.
move=> xy; have -> : [set z | x -- z & y -- z] = ~: [set x; y].
  by apply/setP => z; rewrite !inE /edge_rel /= negb_or [z == x]eq_sym [z == y]eq_sym.
by rewrite cardsCs setCK cards2 xy card_ord.
Qed.

Lemma g230_book_Kn (n : nat) : 3 <= n ->
  x230_book_at_most 'K_n (n - 2) /\ ~ x230_book_at_most 'K_n (n - 3).
Proof.
move=> n3; split; first by move=> x y xy; rewrite g230_book_Kn_common.
move=> h.
have h0 : 0 < n by lia.
have h1 : 1 < n by lia.
have := h (Ordinal h0) (Ordinal h1) isT.
rewrite g230_book_Kn_common //; lia.
Qed.

(** ** Certificates: row arxiv:1905.05312#00 *)
Definition g230_books_hyp_claim : Prop :=
  (exists (n b : nat) (G : sgraph),
     [/\ n <= 6 * b /\ 4 * b < n, #|G| = n, n ^ 2 %/ 4 <= #|E(G)|, x230_book_at_most G b
       & ~ inhabited (diso G 'K_(n %/ 2),(n - n %/ 2))]) /\
  (books_versus_triangles_extremal_density_statement ->
     2 <= clique_count_size (compl (cycle_graph 6)) 3).

Theorem g230_books_hyp_inhabited : g230_books_hyp_claim.
Proof.
have hP : [/\ 6 <= 6 * 1 /\ 4 * 1 < 6, #|g230_P| = 6, 6 ^ 2 %/ 4 <= #|E(g230_P)|,
    x230_book_at_most g230_P 1 & ~ inhabited (diso g230_P 'K_(6 %/ 2),(6 - 6 %/ 2))].
  split; [by [] | exact: g230_P_card | by rewrite g230_P_edges | exact: g230_P_book
    | exact: g230_P_not_K33].
split; first by exists 6, 1, g230_P.
move=> stmt; case: hP => -[h1 h2] h3 h4 h5 h6.
by case: (stmt 6 1 g230_P h1 h2 h3 h4 h5 h6) => le _.
Qed.

Definition g230_books_unguarded : Prop :=
  forall (n b : nat) (G : sgraph),
    n <= 6 * b -> 4 * b < n -> #|G| = n ->
    n ^ 2 %/ 4 <= #|E(G)| -> x230_book_at_most G b ->
    b ^ 2 * (n - 4 * b) <= clique_count_size G 3 /\
    (clique_count_size G 3 = b ^ 2 * (n - 4 * b) <-> x230_prism_blowup b n G).

Definition g230_books_ntt_claim : Prop :=
  ~ g230_books_unguarded /\
  (g230_books_unguarded -> books_versus_triangles_extremal_density_statement).

Theorem g230_books_not_trivially_true : g230_books_ntt_claim.
Proof.
split; last by move=> h n b G h1 h2 h3 h4 h5 _; exact: h.
move=> h.
have e : 6 ^ 2 %/ 4 <= #|E('K_3,3)| by rewrite g230_KB_edges.
have [le _] := h 6 1 'K_3,3 isT isT (@g230_KB_card 3 3) e (@g230_KB_book 3 3 1).
by rewrite g230_KB_no_triangle in le.
Qed.

(** ** Certificates: row arxiv:2108.00987#00 *)
Definition g230_odd_cycles_hyp_claim : Prop :=
  (forall K : nat, exists2 k : nat, K <= k & odd k) /\
  (threshold_ramsey_multiplicity_odd_cycles_statement ->
     exists k m : nat,
       [/\ odd k, x230_threshold_multiplicity (cycle_graph k) m & 2 * m = (k.-1)`!]).

Theorem g230_odd_cycles_hyp_inhabited : g230_odd_cycles_hyp_claim.
Proof.
have hk (K : nat) : exists2 k : nat, K <= k & odd k.
  case oK : (odd K); first by exists K.
  by exists K.+1; rewrite ?leqnSn //= oK.
split=> // -[K hK]; have [k Kk ok] := hk K.
by have [m hm em] := hK k Kk ok; exists k, m.
Qed.

Definition g230_odd_cycles_unthresholded : Prop :=
  forall k : nat, odd k ->
    exists2 m : nat, x230_threshold_multiplicity (cycle_graph k) m & 2 * m = (k.-1)`!.

Definition g230_odd_cycles_ntt_claim : Prop :=
  [/\ ~ g230_odd_cycles_unthresholded,
      g230_odd_cycles_unthresholded -> threshold_ramsey_multiplicity_odd_cycles_statement
    & x230_threshold_multiplicity (cycle_graph 1) 2].

Theorem g230_odd_cycles_not_trivially_true : g230_odd_cycles_ntt_claim.
Proof.
split.
- move=> h; have [m _ em] := h 1 isT.
  by move/(congr1 odd): em; rewrite oddM.
- by move=> h; exists 0 => k _; exact: h.
- by apply: g230_threshold_one; exact: card_ord.
Qed.

(** ** Certificates: row arxiv:2108.00991#00 *)
Definition g230_paths_hyp_claim : Prop :=
  (forall K : nat, exists k : nat, K <= k) /\
  (threshold_ramsey_multiplicity_paths_statement ->
     exists k m : nat, x230_threshold_multiplicity (ordinal_path k) m /\
       (if odd k then 4 * m = k.-1 * (k.-1)`! else 2 * m = k`!)).

Theorem g230_paths_hyp_inhabited : g230_paths_hyp_claim.
Proof.
split; first by move=> K; exists K.
by case=> K hK; have [m hm em] := hK K (leqnn K); exists K, m.
Qed.

Definition g230_paths_unthresholded : Prop :=
  forall k : nat, exists2 m : nat, x230_threshold_multiplicity (ordinal_path k) m &
    (if odd k then 4 * m = k.-1 * (k.-1)`! else 2 * m = k`!).

Definition g230_paths_ntt_claim : Prop :=
  [/\ ~ g230_paths_unthresholded,
      g230_paths_unthresholded -> threshold_ramsey_multiplicity_paths_statement
    & x230_threshold_multiplicity (ordinal_path 1) 2].

Theorem g230_paths_not_trivially_true : g230_paths_ntt_claim.
Proof.
have t1 : x230_threshold_multiplicity (ordinal_path 1) 2.
  by apply: g230_threshold_one; exact: card_ord.
split=> //; last by move=> h; exists 0 => k _; exact: h.
move=> h; have [m hm em] := h 1.
by rewrite (g230_threshold_unique hm t1) /= in em.
Qed.

(** ** Certificates: row arxiv:2311.01887#00 *)
Definition g230_growth_hyp_claim : Prop :=
  (forall n R : nat, x230_ramsey_number 'K_n R -> n <= n <= R) /\
  (ramsey_numbers_of_arbitrary_growth_statement ->
     forall eps : rat, (0 < eps)%R ->
       exists2 Gs : nat -> sgraph, (forall n : nat, #|Gs n| = n) &
         exists N : nat, forall n : nat, N <= n ->
           exists2 R : nat, x230_ramsey_number (Gs n) R &
             ((1 - eps) * n%:R <= R%:R)%R /\ (R%:R <= (1 + eps) * n%:R)%R).

Theorem g230_growth_hyp_inhabited : g230_growth_hyp_claim.
Proof.
have hid : forall n R : nat, x230_ramsey_number 'K_n R -> n <= n <= R.
  by move=> n R /g230_ramsey_card; rewrite card_ord leqnn.
split=> // stmt; exact: (stmt id hid).
Qed.

Definition g230_growth_without_lower : Prop :=
  forall f : nat -> nat,
    (forall n R : nat, x230_ramsey_number 'K_n R -> f n <= R) ->
    forall eps : rat, (0 < eps)%R ->
      exists2 Gs : nat -> sgraph, (forall n : nat, #|Gs n| = n) &
        exists N : nat, forall n : nat, N <= n ->
          exists2 R : nat, x230_ramsey_number (Gs n) R &
            ((1 - eps) * (f n)%:R <= R%:R)%R /\ (R%:R <= (1 + eps) * (f n)%:R)%R.

Definition g230_growth_ntt_claim : Prop :=
  ~ g230_growth_without_lower /\
  (g230_growth_without_lower -> ramsey_numbers_of_arbitrary_growth_statement).

Theorem g230_growth_not_trivially_true : g230_growth_ntt_claim.
Proof.
split; last first.
  by move=> h f hf; apply: h => n R hR; case/andP: (hf n R hR).
move=> h; have [Gs Gsn [N hN]] := h (fun _ => 0) (fun _ _ _ => leq0n _) 1%R ltr01.
have [R hR [_ up]] := hN N.+1 (leqnSn N).
have R0 : R = 0 by apply/eqP; move: up; rewrite /= mulr0n mulr0 lern0.
by have := g230_ramsey_card hR; rewrite Gsn R0.
Qed.

(** ** Certificates: helper sanity *)
Definition g230_book_sanity_claim : Prop :=
  forall n : nat, 3 <= n ->
    x230_book_at_most 'K_n (n - 2) /\ ~ x230_book_at_most 'K_n (n - 3).

Theorem g230_book_sanity : g230_book_sanity_claim.
Proof. exact: g230_book_Kn. Qed.

Definition g230_prism_sanity_claim : Prop :=
  [/\ x230_prism_blowup 1 6 (compl (cycle_graph 6)),
      forall i : nat, i < 6 -> count (x230_prism_rel i) (iota 0 6) = 3
    & ~~ x230_prism_rel 0 4].

Theorem g230_prism_sanity : g230_prism_sanity_claim.
Proof.
split; [exact: g230_P_blowup | | by []].
have h : all (fun i => count (x230_prism_rel i) (iota 0 6) == 3) (iota 0 6) by vm_compute.
by move=> i i6; apply/eqP; apply: (allP h); rewrite mem_iota.
Qed.

Definition g230_copies_sanity_claim : Prop :=
  forall m n : nat,
    [/\ #|x230_embeddings 'K_m 'K_n| = n ^_ m, #|x230_automorphisms 'K_m| = m`!
      & x230_copies 'K_m 'K_n = 'C(n, m)].

Theorem g230_copies_sanity : g230_copies_sanity_claim.
Proof.
by move=> m n; split; [exact: g230_emb_card_KK | exact: g230_aut_card_K | exact: g230_copies_KK].
Qed.

Definition g230_mono_sanity_claim : Prop :=
  (forall n : nat, x230_mono_copies 'K_2 'K_n = 'C(n, 2)) /\
  (forall G : sgraph, x230_mono_copies 'K_1 G = 2 * #|G|).

Theorem g230_mono_sanity : g230_mono_sanity_claim.
Proof.
split; first exact: g230_mono_K2_Kn.
by move=> G; apply: g230_mono_one; exact: card_ord.
Qed.

Definition g230_ramsey_sanity_claim : Prop :=
  [/\ forall R : nat, x230_arrows R 'K_2 <-> 2 <= R,
      x230_ramsey_number 'K_2 2, x230_ramsey_number 'K_1 1
    & forall (H : sgraph) (R R' : nat),
        x230_ramsey_number H R -> x230_ramsey_number H R' -> R = R'].

Theorem g230_ramsey_sanity : g230_ramsey_sanity_claim.
Proof.
split; [exact: g230_arrows_K2 | exact: g230_ramsey_K2 | | exact: g230_ramsey_unique].
by apply: g230_ramsey_one; exact: card_ord.
Qed.

Definition g230_threshold_sanity_claim : Prop :=
  x230_threshold_multiplicity 'K_1 2 /\
  forall (H : sgraph) (m m' : nat),
    x230_threshold_multiplicity H m -> x230_threshold_multiplicity H m' -> m = m'.

Theorem g230_threshold_sanity : g230_threshold_sanity_claim.
Proof.
split; last exact: g230_threshold_unique.
by apply: g230_threshold_one; exact: card_ord.
Qed.

(** ** Axiom audit *)
Print Assumptions g230_books_hyp_inhabited.
Print Assumptions g230_books_not_trivially_true.
Print Assumptions g230_odd_cycles_hyp_inhabited.
Print Assumptions g230_odd_cycles_not_trivially_true.
Print Assumptions g230_paths_hyp_inhabited.
Print Assumptions g230_paths_not_trivially_true.
Print Assumptions g230_growth_hyp_inhabited.
Print Assumptions g230_growth_not_trivially_true.
Print Assumptions g230_book_sanity.
Print Assumptions g230_prism_sanity.
Print Assumptions g230_copies_sanity.
Print Assumptions g230_mono_sanity.
Print Assumptions g230_ramsey_sanity.
Print Assumptions g230_threshold_sanity.

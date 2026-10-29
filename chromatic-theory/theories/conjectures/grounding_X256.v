(** * Chromatic.conjectures.grounding_X256 -- grounding certificates of wave X256.
    For each of the six rows: hyp_inhabited (the hypotheses hold on a concrete instance: K_2 coloured with two colours,
    K_{3,3} (3-regular, not complete) with its side colourings, K_2's constant edge colourings; the statement then
    yields its conclusion there) and not_trivially_true in the contract form of meta/EXPANSION_PLAN.md 4.4 (a variant
    obtained from the body by deleting one hypothesis is false and implies the row).  Three vertex rows drop the
    properness of the source colouring: a Kempe change keeps a monochromatic edge monochromatic (g256_change_mono,
    g256_reach_mono), so a constant colouring never reaches a proper one.  The Las Vergnas-Meyniel row drops its minor
    hypothesis: on K_1 with t = 1 every colouring uses its one colour.  The Mohar edge row drops the properness of
    the source colouring: an X213 Kempe change keeps an asymmetric edge asymmetric (g256_x213_step_asym).  The Vizing
    synonym drops the colourability hypothesis: K_2 has an edge, so no colouring uses no colour on the edges.
    helper_sanity: a singleton of K_2 is a (0, 2)-chain but not a (0, 1)-chain (closure, which X162's step lacks);
    moving one end of K_2 to a free colour is a Kempe change and the identity is not; one change, not zero,
    reaches it. *)

From GTBase Require Export base.
From GTBase Require Import colourings.
From Chromatic.conjectures Require Import X213 X256.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Kempe invariants *)

(** A Kempe change keeps a monochromatic edge monochromatic: by closure both ends are in the chain or neither. *)
Lemma g256_change_mono (G : sgraph) (k : nat) (col col' : G -> 'I_k) (u v : G) :
  x256_kempe_change col col' -> u -- v -> col u = col v -> col' u = col' v.
Proof.
move=> [a [b [S [_ [_ _ two closed] def]]]] uv cuv.
rewrite !def; case uS: (u \in S); case vS: (v \in S); rewrite ?cuv //.
- by move: (closed u v uS uv); rewrite -cuv (two u uS) vS => /(_ isT).
- by move: (closed v u vS); rewrite sg_sym cuv (two v vS) uS => /(_ uv isT).
Qed.

Lemma g256_reach_mono (G : sgraph) (k n : nat) (col col' : G -> 'I_k) (u v : G) :
  x256_kempe_reach_le n col col' -> u -- v -> col u = col v -> col' u = col' v.
Proof.
elim: n col => [|n IH] col /=.
- by move=> e _; rewrite -!e.
- move=> [e|[c [ch r]]] uv cuv; first by rewrite -!e.
  exact: (IH c r uv (g256_change_mono ch uv cuv)).
Qed.

(** ** Small graphs: K_1, K_2 and K_{3,3} *)

Lemma g256_K2_adj (x y : 'K_2) : x -- y = (x != y).
Proof. by []. Qed.

Definition g256_v0 : 'K_2 := @Ordinal 2 0 isT.
Definition g256_v1 : 'K_2 := @Ordinal 2 1 isT.

Lemma g256_K2_edge : g256_v0 -- g256_v1.
Proof. by []. Qed.

(** The colouring of K_2 by two distinct colours of 'I_k (k >= 2). *)
Definition g256_K2_col (k : nat) (k2 : 1 < k) : 'K_2 -> 'I_k :=
  fun v => @Ordinal k v (leq_trans (ltn_ord v) k2).

Lemma g256_K2_col_proper (k : nat) (k2 : 1 < k) : proper_colouring (g256_K2_col k2).
Proof.
apply/proper_colouringP => x y; rewrite g256_K2_adj => xy.
by apply: contraNneq xy => /(congr1 val) /= /val_inj ->.
Qed.

Lemma g256_K2_not_K3_minor : ~ minor 'K_2 'K_3.
Proof. by move/minor_card; rewrite !card_ord. Qed.

Lemma g256_K2_degenerate : k_degenerate 'K_2 1.
Proof.
move=> S _ /set0Pn [x xS]; exists x; split => //.
apply: leq_trans (subset_leq_card (subsetIl _ _)) _.
have sub : N(x) \subset [set~ x].
  by apply/subsetP => y; rewrite !inE; apply: contraTneq => ->; rewrite sg_irrefl.
by move: (subset_leq_card sub); rewrite cardsC1 card_ord.
Qed.

Definition g256_kb_l0 : KB 3 3 := inl (@Ordinal 3 0 isT).
Definition g256_kb_l1 : KB 3 3 := inl (@Ordinal 3 1 isT).
Definition g256_kb_r0 : KB 3 3 := inr (@Ordinal 3 0 isT).

Lemma g256_kb_edge : g256_kb_l0 -- g256_kb_r0.
Proof. by []. Qed.

Lemma g256_KB33_regular : regular (KB 3 3) 3.
Proof.
case=> i.
- have -> : N(inl i : KB 3 3) = [set (inr j : KB 3 3) | j in [set: 'I_3]].
    apply/setP => -[j|j]; rewrite !inE /=.
    + by apply/esym/imsetP => -[x _].
    + by apply/esym/imsetP; exists j; rewrite ?inE.
  by rewrite card_imset ?cardsT ?card_ord // => x y [].
- have -> : N(inr i : KB 3 3) = [set (inl j : KB 3 3) | j in [set: 'I_3]].
    apply/setP => -[j|j]; rewrite !inE /=.
    + by apply/esym/imsetP; exists j; rewrite ?inE.
    + by apply/esym/imsetP => -[x _].
  by rewrite card_imset ?cardsT ?card_ord // => x y [].
Qed.

Lemma g256_KB33_not_clique : ~ clique [set: KB 3 3].
Proof. by move/(_ g256_kb_l0 g256_kb_l1 (in_setT _) (in_setT _) isT). Qed.

(** The side colouring of K_{3,3} by the first two colours of 'I_3. *)
Definition g256_kb_col : KB 3 3 -> 'I_3 :=
  fun v => if v is inl _ then @Ordinal 3 0 isT else @Ordinal 3 1 isT.

Lemma g256_kb_col_proper : proper_colouring g256_kb_col.
Proof. by apply/proper_colouringP => -[x|x] [y|y]. Qed.

(** ** helper_sanity *)

Definition g256_o0 : 'I_3 := @Ordinal 3 0 isT.
Definition g256_o1 : 'I_3 := @Ordinal 3 1 isT.
Definition g256_o2 : 'I_3 := @Ordinal 3 2 isT.

(** K_2 coloured 0 and 1 out of three colours, and the colouring that moves v0 to colour 2. *)
Definition g256_c3 : 'K_2 -> 'I_3 := g256_K2_col (isT : 1 < 3).
Definition g256_c3' : 'K_2 -> 'I_3 := fun v => if v == g256_v0 then g256_o2 else g256_c3 v.

Lemma g256_K2_cases (v : 'K_2) : v = g256_v0 \/ v = g256_v1.
Proof. by case: v => -[|[|m]] Hm; [left|right|]; rewrite ?(eq_irrelevance Hm isT). Qed.

Definition g256_chain_helper_claim : Prop :=
  x256_kempe_chain g256_c3 g256_o0 g256_o2 [set g256_v0] /\
  ~ x256_kempe_chain g256_c3 g256_o0 g256_o1 [set g256_v0].

Theorem g256_chain_helper_sanity : g256_chain_helper_claim.
Proof.
split.
- split; first by apply/set0Pn; exists g256_v0; rewrite inE.
  + exact: connected1.
  + by move=> v; rewrite inE => /eqP ->.
  + move=> u v; rewrite inE => /eqP -> uv; have [->|->] := g256_K2_cases v.
    * by rewrite inE.
    * by [].
- by case=> _ _ _ /(_ g256_v0 g256_v1); rewrite !inE => /(_ isT isT isT).
Qed.

Definition g256_change_helper_claim : Prop :=
  x256_kempe_change g256_c3 g256_c3' /\ ~ x256_kempe_change g256_c3 g256_c3.

Theorem g256_change_helper_sanity : g256_change_helper_claim.
Proof.
split.
- exists g256_o0, g256_o2, [set g256_v0]; split=> //; first by case: g256_chain_helper_sanity.
  by move=> v; rewrite inE /g256_c3'; have [->|->] := g256_K2_cases v.
- move=> [a [b [S [ab [/set0Pn [v vS] _ two _] def]]]].
  move: (def v) (two v vS); rewrite vS; case: eqP => [->|ne] e.
  + by rewrite e eqxx in ab.
  + by [].
Qed.

Definition g256_reach_helper_claim : Prop :=
  x256_kempe_reach_le 1 g256_c3 g256_c3' /\ ~ x256_kempe_reach_le 0 g256_c3 g256_c3'.

Theorem g256_reach_helper_sanity : g256_reach_helper_claim.
Proof.
split; first by right; exists g256_c3'; split=> //; case: g256_change_helper_sanity.
by move/(_ g256_v0).
Qed.

(** The colouring of K_2 by the same two colours in the other order. *)
Definition g256_K2_col' (k : nat) (k2 : 1 < k) : 'K_2 -> 'I_k :=
  fun v => if v == g256_v0 then g256_K2_col k2 g256_v1 else g256_K2_col k2 g256_v0.

Lemma g256_K2_col'_proper (k : nat) (k2 : 1 < k) : proper_colouring (g256_K2_col' k2).
Proof.
apply/proper_colouringP => x y; rewrite /g256_K2_col'.
by have [->|->] := g256_K2_cases x; have [->|->] := g256_K2_cases y.
Qed.

(** ** arxiv:2112.02313#00 *)

Definition g256_poly_hyp_claim : Prop :=
  [/\ k_degenerate 'K_2 (2 - 1), proper_colouring (g256_K2_col (isT : 1 < 2)),
      proper_colouring (g256_K2_col' (isT : 1 < 2)) &
      (degenerate_kempe_polynomial_length_statement ->
         exists c d : nat,
           x256_kempe_reach_le (c * #|'K_2| ^ d) (g256_K2_col (isT : 1 < 2)) (g256_K2_col' (isT : 1 < 2)))].

Theorem g256_poly_hyp_inhabited : g256_poly_hyp_claim.
Proof.
split; [exact: g256_K2_degenerate | exact: g256_K2_col_proper | exact: g256_K2_col'_proper |].
move=> h; have [c [d hd]] := h 2; exists c, d.
exact: hd g256_K2_degenerate (g256_K2_col_proper _) (g256_K2_col'_proper _).
Qed.

Definition g256_poly_no_proper_source : Prop :=
  forall k : nat, exists c d : nat, forall (G : sgraph) (col1 col2 : G -> 'I_k),
    k_degenerate G (k - 1) -> proper_colouring col2 ->
    x256_kempe_reach_le (c * #|G| ^ d) col1 col2.

Definition g256_poly_ntt_claim : Prop :=
  ~ g256_poly_no_proper_source /\ (g256_poly_no_proper_source -> degenerate_kempe_polynomial_length_statement).

Theorem g256_poly_not_trivially_true : g256_poly_ntt_claim.
Proof.
split; last by move=> h k; have [c [d hd]] := h k; exists c, d => G col1 col2 hdg _; exact: hd.
move=> h; have [c [d hd]] := h 2.
have r := hd 'K_2 (fun _ => g256_K2_col (isT : 1 < 2) g256_v0) (g256_K2_col (isT : 1 < 2))
  g256_K2_degenerate (g256_K2_col_proper _).
by move/(congr1 val): (g256_reach_mono r g256_K2_edge erefl).
Qed.

(** ** studies:std_las_vergnas_meyniel_conjecture_a_kempe_equivalen *)

Definition g256_lvm_hyp_claim : Prop :=
  [/\ ~ minor 'K_2 ('K_3), proper_colouring (g256_K2_col (isT : 1 < 3)) &
      (las_vergnas_meyniel_kempe_class_fewer_colours_statement ->
         exists (n : nat) (col' : 'K_2 -> 'I_3),
           [/\ x256_kempe_reach_le n (g256_K2_col (isT : 1 < 3)) col', proper_colouring col' &
               #|[set col' v | v in 'K_2]| < 3])].

Theorem g256_lvm_hyp_inhabited : g256_lvm_hyp_claim.
Proof.
split; [exact: g256_K2_not_K3_minor | exact: g256_K2_col_proper |].
by move=> h; exact: h _ _ _ g256_K2_not_K3_minor (g256_K2_col_proper _).
Qed.

Definition g256_lvm_no_minor_clause : Prop :=
  forall (t : nat) (G : sgraph) (col : G -> 'I_t),
    proper_colouring col ->
    exists (n : nat) (col' : G -> 'I_t),
      [/\ x256_kempe_reach_le n col col', proper_colouring col' & #|[set col' v | v in G]| < t].

Definition g256_lvm_ntt_claim : Prop :=
  ~ g256_lvm_no_minor_clause /\
  (g256_lvm_no_minor_clause -> las_vergnas_meyniel_kempe_class_fewer_colours_statement).

Theorem g256_lvm_not_trivially_true : g256_lvm_ntt_claim.
Proof.
split; last by move=> h t G col _; exact: h.
move=> h; have [|n [col' [_ _]]] := h 1 'K_1 (fun _ => ord0).
  by apply/proper_colouringP => x y; rewrite (ord1 x) (ord1 y) sg_irrefl.
by apply/negP; rewrite -leqNgt; apply/card_gt0P; exists (col' ord0); exact: imset_f.
Qed.

(** ** arxiv:2103.10684#01 *)

Lemma g256_c3_gt1 (c : nat) : 0 < c -> 1 < c * 3.
Proof. by move=> c0; apply: leq_trans (leq_pmull 3 c0). Qed.

Definition g256_lin_hyp_claim : Prop :=
  (forall c : nat, 0 < c -> exists (t : nat) (G : sgraph) (col1 col2 : G -> 'I_(c * t)),
     [/\ ~ minor G ('K_t), proper_colouring col1 & proper_colouring col2]) /\
  (minor_free_linear_palette_kempe_class_statement ->
     exists c : nat, 0 < c /\ forall col1 col2 : 'K_2 -> 'I_(c * 3),
       proper_colouring col1 -> proper_colouring col2 -> exists n : nat, x256_kempe_reach_le n col1 col2).

Theorem g256_lin_hyp_inhabited : g256_lin_hyp_claim.
Proof.
split.
- move=> c c0; exists 3, ('K_2), (g256_K2_col (g256_c3_gt1 c0)), (g256_K2_col' (g256_c3_gt1 c0)).
  by split; [exact: g256_K2_not_K3_minor | exact: g256_K2_col_proper | exact: g256_K2_col'_proper].
- by move=> [c [c0 h]]; exists c; split=> // col1 col2; exact: h _ _ _ _ g256_K2_not_K3_minor.
Qed.

Definition g256_lin_no_proper_source : Prop :=
  exists c : nat, 0 < c /\
    forall (t : nat) (G : sgraph) (col1 col2 : G -> 'I_(c * t)),
      ~ minor G ('K_t) -> proper_colouring col2 ->
      exists n : nat, x256_kempe_reach_le n col1 col2.

Definition g256_lin_ntt_claim : Prop :=
  ~ g256_lin_no_proper_source /\ (g256_lin_no_proper_source -> minor_free_linear_palette_kempe_class_statement).

Theorem g256_lin_not_trivially_true : g256_lin_ntt_claim.
Proof.
split; last by move=> [c [c0 h]]; exists c; split=> // t G col1 col2 hm _; exact: h.
move=> [c [c0 h]]; have k2 := g256_c3_gt1 c0.
have [n r] := h 3 'K_2 (fun _ => g256_K2_col k2 g256_v0) (g256_K2_col k2) g256_K2_not_K3_minor
  (g256_K2_col_proper k2).
by move/(congr1 val): (g256_reach_mono r g256_K2_edge erefl).
Qed.

(** ** studies:std_mohar_s_conjecture_kempe_equivalence_of_k_colour *)

Definition g256_kb_col' : KB 3 3 -> 'I_3 :=
  fun v => if v is inl _ then @Ordinal 3 1 isT else @Ordinal 3 0 isT.

Lemma g256_kb_col'_proper : proper_colouring g256_kb_col'.
Proof. by apply/proper_colouringP => -[x|x] [y|y]. Qed.

Definition g256_mreg_hyp_claim : Prop :=
  [/\ 3 <= 3, regular (KB 3 3) 3, ~ clique [set: KB 3 3],
      proper_colouring g256_kb_col /\ proper_colouring g256_kb_col' &
      (mohar_regular_kempe_class_statement -> exists n : nat, x256_kempe_reach_le n g256_kb_col g256_kb_col')].

Theorem g256_mreg_hyp_inhabited : g256_mreg_hyp_claim.
Proof.
split=> //; [exact: g256_KB33_regular | exact: g256_KB33_not_clique | |].
  by split; [exact: g256_kb_col_proper | exact: g256_kb_col'_proper].
move=> h; exact: (h 3 (KB 3 3) g256_kb_col g256_kb_col' isT g256_KB33_regular g256_KB33_not_clique
  g256_kb_col_proper g256_kb_col'_proper).
Qed.

Definition g256_mreg_no_proper_source : Prop :=
  forall (k : nat) (G : sgraph) (col1 col2 : G -> 'I_k),
    3 <= k -> regular G k -> ~ clique [set: G] ->
    proper_colouring col2 ->
    exists n : nat, x256_kempe_reach_le n col1 col2.

Definition g256_mreg_ntt_claim : Prop :=
  ~ g256_mreg_no_proper_source /\ (g256_mreg_no_proper_source -> mohar_regular_kempe_class_statement).

Theorem g256_mreg_not_trivially_true : g256_mreg_ntt_claim.
Proof.
split; last by move=> h k G col1 col2 k3 hr hc _; exact: h.
move=> h; have [n r] := h 3 (KB 3 3) (fun _ => g256_kb_col g256_kb_l0) g256_kb_col isT g256_KB33_regular
  g256_KB33_not_clique g256_kb_col_proper.
by move/(congr1 val): (g256_reach_mono r g256_kb_edge erefl).
Qed.

(** ** Edge colourings (X213's vocabulary) *)

(** An edge on which a colouring is asymmetric stays asymmetric: a closed set holds both orientations or neither. *)
Lemma g256_x213_step_asym (G : sgraph) (k : nat) (col col' : G -> G -> 'I_k) (u v : G) :
  x213_kempe_step col col' -> col u v != col v u -> col' u v != col' v u.
Proof.
move=> [a [b [K [sym two _ def]]]] ne; rewrite !def -(sym u v).
case uvK: ((u, v) \in K) => //.
have [_ huv] := two u v uvK; have [_ hvu] : v -- u /\ (col v u == a) || (col v u == b).
  by apply: two; rewrite -sym.
move: ne huv hvu; case: (col u v =P a) => [->|na] /=; case: (col v u =P a) => [->|nb] //=.
- by rewrite eqxx.
- by move=> _ _ /eqP e; rewrite -e; apply/eqP => e'; apply: nb; rewrite e -e'.
- by move=> _ /eqP e _; rewrite -e; apply/eqP => e'; apply: na; rewrite e e'.
- by move=> ne /eqP e1 /eqP e2; rewrite e1 e2 eqxx in ne.
Qed.

Lemma g256_x213_reach_asym (G : sgraph) (k n : nat) (col col' : G -> G -> 'I_k) (u v : G) :
  x213_kempe_reach n col col' -> col u v != col v u -> col' u v != col' v u.
Proof.
elim: n col => [|n IH] col /=; first by move=> ->.
move=> [->|[c [st r]]] // ne; exact: IH c r (g256_x213_step_asym st ne).
Qed.

Lemma g256_K2_const_edge_proper (k : nat) (c : 'I_k) : x213_proper_edge_colouring (fun _ _ : 'K_2 => c).
Proof.
split=> // u v w; rewrite !g256_K2_adj.
have [->|->] := g256_K2_cases u; have [->|->] := g256_K2_cases v; have [->|->] := g256_K2_cases w;
  by rewrite ?eqxx.
Qed.

Definition g256_e0 (G : sgraph) : 'I_(Delta G + 2) := @Ordinal _ 0 (ltn_addl (Delta G) (isT : 0 < 2)).
Definition g256_e1 (G : sgraph) : 'I_(Delta G + 2) := @Ordinal _ 1 (ltn_addl (Delta G) (isT : 1 < 2)).

(** ** studies:std_mohar_s_conjecture_kempe_equivalence_of_2_edge_c *)

Definition g256_medge_hyp_claim : Prop :=
  [/\ x213_proper_edge_colouring (fun _ _ : 'K_2 => g256_e0 'K_2),
      x213_proper_edge_colouring (fun _ _ : 'K_2 => g256_e1 'K_2), g256_v0 -- g256_v1 &
      (mohar_max_degree_plus_two_edge_kempe_statement ->
         exists (n : nat) (col : 'K_2 -> 'K_2 -> 'I_(Delta 'K_2 + 2)),
           x213_kempe_reach n (fun _ _ => g256_e0 'K_2) col /\
           forall u v : ('K_2), u -- v -> col u v = g256_e1 'K_2)].

Theorem g256_medge_hyp_inhabited : g256_medge_hyp_claim.
Proof.
split; [exact: g256_K2_const_edge_proper | exact: g256_K2_const_edge_proper | exact: g256_K2_edge |].
by move=> h; exact: h _ _ _ (g256_K2_const_edge_proper _) (g256_K2_const_edge_proper _).
Qed.

Definition g256_medge_no_proper_source : Prop :=
  forall (G : sgraph) (col1 col2 : G -> G -> 'I_(Delta G + 2)),
    x213_proper_edge_colouring col2 ->
    exists (n : nat) (col : G -> G -> 'I_(Delta G + 2)),
      x213_kempe_reach n col1 col /\ forall u v : G, u -- v -> col u v = col2 u v.

Definition g256_medge_ntt_claim : Prop :=
  ~ g256_medge_no_proper_source /\
  (g256_medge_no_proper_source -> mohar_max_degree_plus_two_edge_kempe_statement).

(** On K_2, the colouring 0 on (v0, v1) and 1 on (v1, v0): asymmetric, so not proper. *)
Definition g256_easym : 'K_2 -> 'K_2 -> 'I_(Delta 'K_2 + 2) :=
  fun u _ => if u == g256_v0 then g256_e0 'K_2 else g256_e1 'K_2.

Theorem g256_medge_not_trivially_true : g256_medge_ntt_claim.
Proof.
split; last by move=> h G col1 col2 _; exact: h.
move=> h; have [n [col [r agree]]] := h 'K_2 g256_easym _ (g256_K2_const_edge_proper (g256_e0 'K_2)).
have := g256_x213_reach_asym (u := g256_v0) (v := g256_v1) r isT.
by rewrite (agree _ _ g256_K2_edge) (agree g256_v1 g256_v0 isT) eqxx.
Qed.

(** ** studies:std_vizing_s_edge_colouring_kempe_equivalence_questi (synonym of X213's bm-060 statement) *)

Definition g256_viz_hyp_claim : Prop :=
  [/\ x213_proper_edge_colouring (fun _ _ : 'K_2 => (ord0 : 'I_2)), 1 <= 2, x213_edge_colourable 'K_2 1 &
      (vizing_kempe_optimal_colouring_question_statement ->
         exists (n : nat) (col' : 'K_2 -> 'K_2 -> 'I_2),
           [/\ x213_kempe_reach n (fun _ _ => ord0) col', x213_proper_edge_colouring col' &
               #|x213_used_colours col'| <= 1])].

Theorem g256_viz_hyp_inhabited : g256_viz_hyp_claim.
Proof.
have ec : x213_edge_colourable 'K_2 1 by exists (fun _ _ => ord0); exact: g256_K2_const_edge_proper.
split=> //; first exact: g256_K2_const_edge_proper.
by move=> h; exact: (h ('K_2) 2 1 (fun _ _ => ord0) (g256_K2_const_edge_proper _) isT ec).
Qed.

Definition g256_viz_no_colourable_clause : Prop :=
  forall (G : sgraph) (k m : nat) (col : G -> G -> 'I_k),
    x213_proper_edge_colouring col ->
    m <= k ->
    exists (n : nat) (col' : G -> G -> 'I_k),
      [/\ x213_kempe_reach n col col',
          x213_proper_edge_colouring col' &
          #|x213_used_colours col'| <= m].

Definition g256_viz_ntt_claim : Prop :=
  ~ g256_viz_no_colourable_clause /\
  (g256_viz_no_colourable_clause -> vizing_kempe_optimal_colouring_question_statement).

Theorem g256_viz_not_trivially_true : g256_viz_ntt_claim.
Proof.
split; last by move=> h G k m col p mk _; exact: h.
move=> h; have [n [col' [_ _]]] := h 'K_2 1 0 (fun _ _ => ord0) (g256_K2_const_edge_proper _) isT.
apply/negP; rewrite -ltnNge; apply/card_gt0P; exists (col' g256_v0 g256_v1).
by rewrite inE; apply/existsP; exists g256_v0; apply/existsP; exists g256_v1; rewrite g256_K2_edge eqxx.
Qed.


Print Assumptions g256_chain_helper_sanity.
Print Assumptions g256_change_helper_sanity.
Print Assumptions g256_reach_helper_sanity.
Print Assumptions g256_poly_hyp_inhabited.
Print Assumptions g256_poly_not_trivially_true.
Print Assumptions g256_lvm_hyp_inhabited.
Print Assumptions g256_lvm_not_trivially_true.
Print Assumptions g256_lin_hyp_inhabited.
Print Assumptions g256_lin_not_trivially_true.
Print Assumptions g256_mreg_hyp_inhabited.
Print Assumptions g256_mreg_not_trivially_true.
Print Assumptions g256_medge_hyp_inhabited.
Print Assumptions g256_medge_not_trivially_true.
Print Assumptions g256_viz_hyp_inhabited.
Print Assumptions g256_viz_not_trivially_true.

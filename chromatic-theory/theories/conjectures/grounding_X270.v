(** * Chromatic.conjectures.grounding_X270 -- grounding certificates for wave X270 (2026-10-31)

    For each of the three rows: hyp_inhabited (the hypotheses hold at a small graph, and the statement then gives its
    conclusion there) and not_trivially_true (a variant without one hypothesis is false and implies the statement).
    The wave has no local helper, so there is no helper_sanity certificate.
    - studies:std_steinberg_s_conjecture: K_3 is planar with no 4- or 5-cycle (a cycle has at most #|G| vertices)
      and chromatic number 3; without "no 4-cycles" the row is false at K_4 (planar, no 5-cycle, chi = 4).
    - studies:std_krekovski_conjecture_separation_choosability_of: K_2 is planar and separation 3-choosable;
      without planarity the row is false at K_12 with the twelve lines of the affine plane AG(2, 3) on its nine
      points as lists (three points each, two lines meet in at most one point): a proper colouring of K_12 from
      them would be injective into nine colours.
    - studies:std_heckman_thomas_conjecture: K_2 is planar, subcubic and triangle-free, with an (2:1)-fold
      colouring (2 / 1 <= 8 / 3); without triangle-freeness the row is false at K_4 (planar and subcubic; an
      (a:b)-fold colouring of K_n has n b <= a, so chi_f(K_4) = 4 > 8 / 3). *)

From GTBase Require Import base bfold_colourings.
From Chromatic.conjectures Require Import X130 X203 X270.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Small graphs ************************************************************ *)

(** Every graph on at most 4 vertices is planar: a K_5 minor needs 5 vertices, a K_(3,3) minor 6. *)
Lemma g270_planar_small (G : sgraph) : #|G| <= 4 -> wagner_planar G.
Proof.
move=> le4; split=> m; move: (leq_trans (minor_card m) le4).
- by rewrite card_ord.
- by rewrite card_sum !card_ord.
Qed.

(** A cycle is duplicate-free, so it has at most #|G| vertices. *)
Lemma g270_no_cycle_length_gt (G : sgraph) (n : nat) : #|G| < n -> no_cycle_length (@edge_rel G) n.
Proof.
move=> lt c /andP [_ u] _; apply: contraTneq lt => <-.
by rewrite -leqNgt -(card_uniqP u) max_card.
Qed.

Lemma g270_chi_K (n : nat) : χ([set: 'K_n]) = n.
Proof.
have cl : clique [set: 'K_n] by move=> x y _ _ xy; rewrite /edge_rel /= xy.
by rewrite chi_clique // cardsT card_ord.
Qed.

(** An (a:b)-fold colouring of K_n uses n pairwise disjoint b-sets of 'I_a, so n b <= a (grounding_X262's
    argument). *)
Lemma g270_bfold_K_le (n a b : nat) (f : 'K_n -> {set 'I_a}) : bfold_colouring b f -> n * b <= a.
Proof.
move=> [card disj].
have -> : n * b = \sum_(v : 'K_n) #|f v| by rewrite (eq_bigr (fun _ => b)) // sum_nat_const card_ord.
rewrite (eq_bigr (fun v => \sum_(c : 'I_a) (c \in f v))); first by move=> v _;
  rewrite -sum1_card big_mkcond /=; apply: eq_bigr => c _; case: (c \in f v).
rewrite exchange_big /= -[X in _ <= X]card_ord -sum1_card; apply: leq_sum => c _.
case: (pickP (fun i => c \in f i)) => [i0 ci0|none]; last by rewrite big1 // => i _; rewrite none.
rewrite (bigD1 i0) //= ci0 big1 // => j ji0; have := disj j i0 ji0.
by rewrite -setI_eq0 => /eqP/setP/(_ c); rewrite !inE ci0 andbT => ->.
Qed.

(** chi_f(K_n) >= n: x130_frac_chi_le ('K_n) p q forces n q <= p. *)
Lemma g270_frac_chi_K (n p q : nat) : x130_frac_chi_le ('K_n) p q -> n * q <= p.
Proof.
case=> a [b] [f] [bpos col le].
have nb : n * b <= a := g270_bfold_K_le col.
by rewrite -(leq_pmul2r bpos) mulnAC (leq_trans (leq_mul nb (leqnn q))) // mulnC (mulnC p).
Qed.

Lemma g270_triangle_free_K2 : triangle_free ('K_2).
Proof.
move=> x y z; rewrite /edge_rel /=.
by case: x => [[|[|//]] ?]; case: y => [[|[|//]] ?]; case: z => [[|[|//]] ?].
Qed.

(** K_2 is separation 3-choosable: a colour from the first list, then one of the at least two other colours of the
    second. *)
Lemma g270_sep_choosable_K2 : x203_separation_choosable ('K_2) 3.
Proof.
move=> C L [card _].
pose v0 : ('K_2) := @Ordinal 2 0 isT; pose v1 : ('K_2) := @Ordinal 2 1 isT.
have K2 (v : ('K_2)) : v = v0 \/ v = v1.
  by case: v => [[|[|m]] p]; [left; exact: val_inj | right; exact: val_inj | by []].
have /card_gt0P [c0 c0L] : 0 < #|L v0| by rewrite card.
have /card_gt0P [c1 c1L] : 0 < #|L v1 :\ c0|.
  have := cardsD1 c0 (L v1); rewrite card.
  by case: #|L v1 :\ c0| => [|n] //; rewrite addn0; case: (c0 \in L v1).
move: c1L; rewrite !inE => /andP [c10 c1L].
exists (fun v => if v == v0 then c0 else c1); split=> [v | x y]; first by case: (K2 v) => ->.
by case: (K2 x) => ->; case: (K2 y) => -> //= _; rewrite // eq_sym.
Qed.

(** The twelve lines of AG(2, 3) on the points 'I_9 (the point (x, y) of Z_3^2 is 3 x + y): four parallel
    classes of three lines each, the directions x = c, y = c, y = x + c and y = 2 x + c, each line with three
    points. *)
Definition g270_ag_lines : seq (seq nat) :=
  [:: [:: 0; 3; 6]; [:: 1; 4; 7]; [:: 2; 5; 8]; [:: 0; 1; 2]; [:: 3; 4; 5]; [:: 6; 7; 8];
      [:: 0; 4; 8]; [:: 1; 5; 6]; [:: 2; 3; 7]; [:: 0; 5; 7]; [:: 1; 3; 8]; [:: 2; 4; 6]].

Definition g270_ag_list (v : ('K_12)) : {set 'I_9} := [set p : 'I_9 | val p \in nth [::] g270_ag_lines v].

(** Set cardinalities over 'I_n as counts over iota 0 n, so that the list checks below compute (the finset and
    card operations are locked). *)
Lemma g270_card_set_nat (n : nat) (P : pred nat) : #|[set p : 'I_n | P (val p)]| = count P (iota 0 n).
Proof. by rewrite cardsE -sum1_card -(big_mkord P (fun _ => 1)) sum1_count /index_iota subn0. Qed.

(** Every line has three points and two distinct lines share at most one point, by computation on the lists. *)
Lemma g270_ag_separated : x203_separated_k_list_assignment g270_ag_list 3.
Proof.
have hc : all (fun i => count (fun k => k \in nth [::] g270_ag_lines i) (iota 0 9) == 3) (iota 0 12).
  by vm_compute.
have hs : all (fun i => all (fun j => (i == j) ||
            (count (fun k => (k \in nth [::] g270_ag_lines i) && (k \in nth [::] g270_ag_lines j)) (iota 0 9)
             <= 1)) (iota 0 12)) (iota 0 12).
  by vm_compute.
split=> [v | u v].
  rewrite /g270_ag_list g270_card_set_nat.
  by move/allP: hc => /(_ (val v)); rewrite mem_iota ltn_ord => /(_ isT)/eqP.
rewrite /edge_rel /= => uv.
have -> : g270_ag_list u :&: g270_ag_list v =
          [set p : 'I_9 | (val p \in nth [::] g270_ag_lines u) && (val p \in nth [::] g270_ag_lines v)].
  by apply/setP => p; rewrite !inE.
rewrite (g270_card_set_nat 9 (fun k => (k \in nth [::] g270_ag_lines u) && (k \in nth [::] g270_ag_lines v))).
move/allP: hs => /(_ (val u)); rewrite mem_iota ltn_ord => /(_ isT) /allP /(_ (val v)).
rewrite mem_iota ltn_ord => /(_ isT) /orP [/eqP/val_inj e | //].
by rewrite e eqxx in uv.
Qed.

(** K_12 is not separation 3-choosable: from the AG(2, 3) lists a proper colouring would be injective. *)
Lemma g270_not_sep_choosable_K12 : ~ x203_separation_choosable ('K_12) 3.
Proof.
move=> /(_ _ g270_ag_list g270_ag_separated) [f [_ fadj]].
have inj : injective f.
  by move=> x y; apply: contra_eq => xy; apply: fadj; rewrite /edge_rel /= xy.
by have := leq_card f inj; rewrite !card_ord.
Qed.

(** K_2 has an (2:1)-fold colouring: each vertex gets itself. *)
Lemma g270_frac_K2 : x130_frac_chi_le ('K_2) 8 3.
Proof.
exists 2, 1, (fun v : ('K_2) => [set (v : 'I_2)]); split=> //.
split=> [v | x y]; first by rewrite cards1.
by rewrite /edge_rel /= disjoints1 in_set1.
Qed.

(** ** studies:std_steinberg_s_conjecture *************************************** *)

(** hyp_inhabited: K_3 is planar, without 4- and 5-cycles, of chromatic number 3; the statement at K_3. *)
Definition g270_st_hyp_claim : Prop :=
  [/\ wagner_planar ('K_3), no_cycle_length (@edge_rel ('K_3)) 4, no_cycle_length (@edge_rel ('K_3)) 5,
      χ([set: ('K_3)]) = 3 &
      (steinberg_planar_no_4_5_cycles_three_colourable_statement -> χ([set: ('K_3)]) <= 3)].

Theorem g270_st_hyp_inhabited : g270_st_hyp_claim.
Proof.
have pl : wagner_planar ('K_3) by apply: g270_planar_small; rewrite card_ord.
have c4 : no_cycle_length (@edge_rel ('K_3)) 4 by apply: g270_no_cycle_length_gt; rewrite card_ord.
have c5 : no_cycle_length (@edge_rel ('K_3)) 5 by apply: g270_no_cycle_length_gt; rewrite card_ord.
by split=> //; [exact: g270_chi_K | move=> h; exact: h].
Qed.

(** not_trivially_true: without "no 4-cycles", K_4 is planar with no 5-cycle and chromatic number 4. *)
Definition g270_st_no_4_cycle_hypothesis : Prop :=
  forall G : sgraph, wagner_planar G -> no_cycle_length (@edge_rel G) 5 -> χ([set: G]) <= 3.

Definition g270_st_ntt_claim : Prop :=
  ~ g270_st_no_4_cycle_hypothesis /\
  (g270_st_no_4_cycle_hypothesis -> steinberg_planar_no_4_5_cycles_three_colourable_statement).

Theorem g270_st_not_trivially_true : g270_st_ntt_claim.
Proof.
split; last by move=> h G pl _ c5; exact: h.
move=> h; have pl : wagner_planar ('K_4) by apply: g270_planar_small; rewrite card_ord.
have c5 : no_cycle_length (@edge_rel ('K_4)) 5 by apply: g270_no_cycle_length_gt; rewrite card_ord.
by have := h _ pl c5; rewrite g270_chi_K.
Qed.

(** ** studies:std_krekovski_conjecture_separation_choosability_of ******************* *)

(** hyp_inhabited: K_2 is planar and separation 3-choosable; the statement at K_2. *)
Definition g270_sk_hyp_claim : Prop :=
  [/\ wagner_planar ('K_2), x203_separation_choosable ('K_2) 3 &
      (skrekovski_planar_separation_three_choosable_statement -> x203_separation_choosable ('K_2) 3)].

Theorem g270_sk_hyp_inhabited : g270_sk_hyp_claim.
Proof.
have pl : wagner_planar ('K_2) by apply: g270_planar_small; rewrite card_ord.
by split=> //; [exact: g270_sep_choosable_K2 | move=> h; exact: h].
Qed.

(** not_trivially_true: without planarity, K_12 with the AG(2, 3) lists. *)
Definition g270_sk_no_planarity : Prop := forall G : sgraph, x203_separation_choosable G 3.

Definition g270_sk_ntt_claim : Prop :=
  ~ g270_sk_no_planarity /\ (g270_sk_no_planarity -> skrekovski_planar_separation_three_choosable_statement).

Theorem g270_sk_not_trivially_true : g270_sk_ntt_claim.
Proof.
split; last by move=> h G _; exact: h.
by move=> h; apply: g270_not_sep_choosable_K12; exact: h.
Qed.

(** ** studies:std_heckman_thomas_conjecture ************************************* *)

(** hyp_inhabited: K_2 is planar, subcubic and triangle-free, with chi_f(K_2) <= 2 <= 8 / 3; the statement at K_2. *)
Definition g270_ht_hyp_claim : Prop :=
  [/\ wagner_planar ('K_2), subcubic ('K_2), triangle_free ('K_2), x130_frac_chi_le ('K_2) 8 3 &
      (heckman_thomas_planar_subcubic_triangle_free_fractional_statement -> x130_frac_chi_le ('K_2) 8 3)].

Theorem g270_ht_hyp_inhabited : g270_ht_hyp_claim.
Proof.
have pl : wagner_planar ('K_2) by apply: g270_planar_small; rewrite card_ord.
have sc : subcubic ('K_2) by exact: subcubic_Kn.
have tf := g270_triangle_free_K2.
by split=> //; [exact: g270_frac_K2 | move=> h; exact: h].
Qed.

(** not_trivially_true: without triangle-freeness, K_4 is planar and subcubic with chi_f(K_4) = 4 > 8 / 3. *)
Definition g270_ht_no_triangle_free : Prop :=
  forall G : sgraph, wagner_planar G -> subcubic G -> x130_frac_chi_le G 8 3.

Definition g270_ht_ntt_claim : Prop :=
  ~ g270_ht_no_triangle_free /\
  (g270_ht_no_triangle_free -> heckman_thomas_planar_subcubic_triangle_free_fractional_statement).

Theorem g270_ht_not_trivially_true : g270_ht_ntt_claim.
Proof.
split; last by move=> h G pl sc _; exact: h.
move=> h; have pl : wagner_planar ('K_4) by apply: g270_planar_small; rewrite card_ord.
by have := g270_frac_chi_K (h _ pl (subcubic_Kn (leqnn 3))).
Qed.

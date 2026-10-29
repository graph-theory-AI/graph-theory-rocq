(** * Extremal.conjectures.grounding_X259 -- grounding certificates of wave X259.

    For each of the two rows: hyp_inhabited (the hypotheses hold with concrete values of the relational hypotheses,
    and the statement then gives its conclusion at a concrete parameter) and not_trivially_true in the contract form
    of meta/EXPANSION_PLAN.md 4.4 (a variant obtained from the body is false and implies the row): each row without
    its relational hypotheses (erdos:1105 without AR(n,F) = a: a = 0 breaks the path formula at n = k = 5; erdos:809
    without chi_S(n,e,F) = s: s = 0 breaks the lower half at k = 3, q = 1).  The concrete values: AR(3,C_3) = 2 (two
    colours on K_3 have no rainbow triangle, three do) and chi_S(3,3,C_7) = 1.  The latter holds vacuously in its
    copies: the only graph with 3 vertices and 3 edges is K_3, which has no copy of C_7, so one colour suffices.
    helper_sanity, group 1 (rainbow copies, AR): a rainbow and a non-rainbow triangle on K_3, no rainbow-free
    3-colouring of K_3, AR(3,C_3) = 2 and not 3.  Group 2 (chi_S): chi_S(3,3,C_3) = 3, NON-VACUOUS (K_3 coloured by
    the missing vertex makes its triangle rainbow; two colours cannot) and not 2, and chi_S(3,3,C_7) = 1. *)

From Extremal.conjectures Require Import X259.
From GTBase Require Import base common path_graphs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The triangle on 'I_3: rainbow copies and AR(3, C_3) ******************************** *)

Local Notation o0 := (@Ordinal 3 0 isT).
Local Notation o1 := (@Ordinal 3 1 isT).
Local Notation o2 := (@Ordinal 3 2 isT).

Lemma g259_I3_cases (x : 'I_3) : [\/ x = o0, x = o1 | x = o2].
Proof.
case: x => [[|[|[|m]]] hm] //; [apply: Or31 | apply: Or32 | apply: Or33]; exact: val_inj.
Qed.

Lemma g259_C3_adj (x y : cycle_graph 3) : (x -- y) = (x != y).
Proof.
by case: (g259_I3_cases x) => ->; case: (g259_I3_cases y) => ->.
Qed.

Lemma g259_K3_adj (x y : 'K_3) : (x -- y) = (x != y).
Proof. by []. Qed.

Lemma g259_set01_12 : [set o0; o1] != [set o1; o2] :> {set 'I_3}.
Proof. by apply/eqP => /setP /(_ o0); rewrite !in_set2. Qed.

(** A rainbow triangle: K_3 coloured injectively (each set its rank). *)
Lemma g259_rainbow_K3 : x259_rainbow_copy (cycle_graph 3) (fun e : {set 'K_3} => val (enum_rank e)).
Proof.
exists (fun x : cycle_graph 3 => (x : 'K_3)); split => //.
- by move=> x y; rewrite g259_C3_adj.
- move=> x y u v _ _; apply: contra => /eqP /val_inj /enum_rank_inj h; apply/eqP; exact: h.
Qed.

(** No rainbow triangle: K_3 in one colour. *)
Lemma g259_not_rainbow_K3 : ~ x259_rainbow_copy (cycle_graph 3) (fun _ : {set 'K_3} => 0).
Proof.
case=> emb [_ _ h]; have := h o0 o1 o1 o2 isT isT g259_set01_12.
by rewrite eqxx.
Qed.

(** The three 2-sets of 'I_3. *)
Lemma g259_pair_cases (x y : 'I_3) : x != y ->
  [\/ [set x; y] = [set o0; o1], [set x; y] = [set o1; o2] | [set x; y] = [set o0; o2]].
Proof.
case: (g259_I3_cases x) => ->; case: (g259_I3_cases y) => -> // _;
  by [apply: Or31 | apply: Or32 | apply: Or33 | apply: Or31; rewrite setUC | apply: Or32; rewrite setUC
     | apply: Or33; rewrite setUC].
Qed.

Lemma g259_set01_02 : [set o0; o1] != [set o0; o2] :> {set 'I_3}.
Proof. by apply/eqP => /setP /(_ o1); rewrite !in_set2. Qed.

Lemma g259_set12_02 : [set o1; o2] != [set o0; o2] :> {set 'I_3}.
Proof. by apply/eqP => /setP /(_ o1); rewrite !in_set2. Qed.

Lemma g259_bool3 (b1 b2 b3 : bool) : (b1 : nat) != b2 -> (b2 : nat) != b3 -> (b1 : nat) != b3 -> False.
Proof. by case: b1; case: b2; case: b3. Qed.

(** AR(3, C_3) >= 2: the edge {0, 1} in colour 1, the two others in colour 0. *)
Lemma g259_free_2 : x259_rainbow_free_colours 3 (cycle_graph 3) 2.
Proof.
pose col := fun e : {set 'K_3} => nat_of_bool (e == [set o0; o1]).
exists col; split.
- have hmem : undup [seq col e | e <- enum E('K_3)] =i [:: 0; 1].
    move=> c; rewrite mem_undup; apply/mapP/idP.
    + by case=> e _ ->; rewrite /col; case: (e == _).
    + rewrite !inE => /orP [] /eqP ->.
      * exists [set o0; o2]; first by rewrite mem_enum in_edges.
        by rewrite /col eq_sym (negbTE g259_set01_02).
      * by exists [set o0; o1]; [rewrite mem_enum in_edges | rewrite /col eqxx].
  by rewrite (perm_size (uniq_perm (undup_uniq _) _ hmem)).
- case=> emb [_ _ h].
  exact: (g259_bool3 (h o0 o1 o1 o2 isT isT g259_set01_12) (h o1 o2 o0 o2 isT isT g259_set12_02)
    (h o0 o1 o0 o2 isT isT g259_set01_02)).
Qed.

(** AR(3, C_3) <= 2: three colours on the three edges of K_3 make the triangle itself rainbow. *)
Lemma g259_free_le2 (r : nat) : x259_rainbow_free_colours 3 (cycle_graph 3) r -> r <= 2.
Proof.
case=> col [<- hno].
set c1 := col [set o0; o1]; set c2 := col [set o1; o2]; set c3 := col [set o0; o2].
have hsub : {subset undup [seq col e | e <- enum E('K_3)] <= [:: c1; c2; c3]}.
  move=> c; rewrite mem_undup => /mapP [e]; rewrite mem_enum => /edgesP [x [y [-> xy]]] ->.
  by case: (g259_pair_cases xy) => ->; rewrite !inE eqxx ?orbT.
case: (boolP [&& c1 != c2, c2 != c3 & c1 != c3]) => [/and3P [h12 h23 h13] | ].
- exfalso; apply: hno; exists (fun x : cycle_graph 3 => (x : 'K_3)); split => //.
  + by move=> x y; rewrite g259_C3_adj.
  + move=> x y u v; rewrite !g259_C3_adj => xy uv.
    case: (g259_pair_cases xy) => ->; case: (g259_pair_cases uv) => -> //; rewrite ?eqxx // => _;
      by rewrite ?h12 ?h23 ?h13 // eq_sym ?h12 ?h23 ?h13.
- rewrite !negb_and !negbK => /or3P [] /eqP e.
  + apply: (@uniq_leq_size _ _ [:: c2; c3] (undup_uniq _)) => c /hsub.
    by rewrite !inE e => /or3P [] ->; rewrite ?orbT.
  + apply: (@uniq_leq_size _ _ [:: c1; c3] (undup_uniq _)) => c /hsub.
    by rewrite !inE e => /or3P [] ->; rewrite ?orbT.
  + apply: (@uniq_leq_size _ _ [:: c1; c2] (undup_uniq _)) => c /hsub.
    by rewrite !inE e => /or3P [] ->; rewrite ?orbT.
Qed.

Lemma g259_AR_3_C3 : x259_anti_ramsey_number 3 (cycle_graph 3) 2.
Proof. by split; [exact: g259_free_2 | exact: g259_free_le2]. Qed.

Lemma g259_not_AR_3_C3_3 : ~ x259_anti_ramsey_number 3 (cycle_graph 3) 3.
Proof. by case=> /g259_free_le2. Qed.

(** ** chi_S on three vertices ******************************************************** *)

(** No r = 0: a map into 'I_0 has no value at set0. *)
Lemma g259_forcing_pos (n e r : nat) (F : sgraph) : x259_rainbow_forcing_colouring n e F r -> 0 < r.
Proof. by case=> H [_ _ [col _]]; exact: leq_ltn_trans (leq0n _) (ltn_ord (col set0)). Qed.

(** chi_S(3, 3, C_7) = 1, vacuously in F: K_3 has no copy of C_7 (seven vertices into three). *)
Lemma g259_chiS_3_3_C7 : x259_strong_chromatic_number 3 3 (cycle_graph 7) 1.
Proof.
split; last by move=> r /g259_forcing_pos.
exists 'K_3; split; [exact: card_ord | exact: edge_count_K3 |].
exists (fun _ => ord0) => emb inj; have := leq_card emb inj; by rewrite !card_ord.
Qed.

(** Colour a 2-set of 'I_3 by its missing vertex. *)
Definition g259_missing (e : {set 'K_3}) : 'I_3 := if o0 \notin e then o0 else if o1 \notin e then o1 else o2.

Lemma g259_missing_inj (x y u v : 'I_3) : x != y -> u != v -> [set x; y] != [set u; v] ->
  g259_missing [set x; y] != g259_missing [set u; v].
Proof.
move=> xy uv; case: (g259_pair_cases xy) => ->; case: (g259_pair_cases uv) => -> //; rewrite ?eqxx //;
  by rewrite /g259_missing !in_set2.
Qed.

(** chi_S(3, 3, C_3) <= 3: K_3 coloured by the missing vertex makes every triangle rainbow. *)
Lemma g259_forcing_C3_3 : x259_rainbow_forcing_colouring 3 3 (cycle_graph 3) 3.
Proof.
exists 'K_3; split; [exact: card_ord | exact: edge_count_K3 |].
exists g259_missing => emb inj hadj x y u v xy uv ne.
apply: g259_missing_inj; [by rewrite (inj_eq inj) -g259_C3_adj | by rewrite (inj_eq inj) -g259_C3_adj |].
apply: contra ne => /eqP h; apply/eqP; apply: (imset_inj inj); by rewrite !imsetU1 !imset_set1.
Qed.

(** A graph on three vertices with three edges is complete: its edges are all the 2-sets. *)
Lemma g259_complete_3_3 (H : sgraph) : #|H| = 3 -> edge_count H = 3 -> forall x y : H, x != y -> x -- y.
Proof.
move=> hH hE.
have hsub : E(H) \subset [set A : {set H} | #|A| == 2].
  apply/subsetP => e /edgesP [x [y [-> xy]]]; by rewrite inE cards2 (sg_edgeNeq xy).
have heq : E(H) = [set A : {set H} | #|A| == 2].
  apply/eqP; rewrite eqEcard hsub card_draws hH.
  by move: hE; rewrite /edge_count => ->.
move=> x y xy; rewrite -in_edges heq inE cards2 xy.
done.
Qed.

(** chi_S(3, 3, C_3) >= 3: the only such graph is K_3, and its triangle needs three colours. *)
Lemma g259_forcing_C3_ge3 (r : nat) : x259_rainbow_forcing_colouring 3 3 (cycle_graph 3) r -> 3 <= r.
Proof.
case=> H [hH hE [col hcol]].
have hc := g259_complete_3_3 hH hE.
pose emb := fun x : cycle_graph 3 => (enum_val (cast_ord (esym hH) x) : H).
have inj : injective emb by move=> x y /enum_val_inj /cast_ord_inj.
have hadj : forall x y : cycle_graph 3, x -- y -> emb x -- emb y.
  by move=> x y; rewrite g259_C3_adj => xy; apply: hc; rewrite (inj_eq inj).
have h12 := hcol emb inj hadj o0 o1 o1 o2 isT isT g259_set01_12.
have h23 := hcol emb inj hadj o1 o2 o0 o2 isT isT g259_set12_02.
have h13 := hcol emb inj hadj o0 o1 o0 o2 isT isT g259_set01_02.
have hu : uniq [:: col [set emb o0; emb o1]; col [set emb o1; emb o2]; col [set emb o0; emb o2]].
  by rewrite /= !inE !negb_or h12 h13 h23.
have := uniq_leq_size hu (fun z _ => mem_enum _ z); by rewrite size_enum_ord.
Qed.

Lemma g259_chiS_3_3_C3 : x259_strong_chromatic_number 3 3 (cycle_graph 3) 3.
Proof. by split; [exact: g259_forcing_C3_3 | exact: g259_forcing_C3_ge3]. Qed.

(** ** helper_sanity ************************************************************* *)
Definition g259_ar_helper_claim : Prop :=
  [/\ x259_rainbow_copy (cycle_graph 3) (fun e : {set 'K_3} => val (enum_rank e)),
      ~ x259_rainbow_copy (cycle_graph 3) (fun _ : {set 'K_3} => 0),
      ~ x259_rainbow_free_colours 3 (cycle_graph 3) 3,
      x259_anti_ramsey_number 3 (cycle_graph 3) 2 &
      ~ x259_anti_ramsey_number 3 (cycle_graph 3) 3].

Theorem g259_ar_helper_sanity : g259_ar_helper_claim.
Proof.
split; [exact: g259_rainbow_K3 | exact: g259_not_rainbow_K3 | by move/g259_free_le2 | exact: g259_AR_3_C3
       | exact: g259_not_AR_3_C3_3].
Qed.

Definition g259_cs_helper_claim : Prop :=
  [/\ x259_rainbow_forcing_colouring 3 3 (cycle_graph 3) 3,
      ~ x259_rainbow_forcing_colouring 3 3 (cycle_graph 3) 2,
      x259_strong_chromatic_number 3 3 (cycle_graph 3) 3,
      ~ x259_strong_chromatic_number 3 3 (cycle_graph 3) 2 &
      x259_strong_chromatic_number 3 3 (cycle_graph 7) 1].

Theorem g259_cs_helper_sanity : g259_cs_helper_claim.
Proof.
split; [exact: g259_forcing_C3_3 | by move/g259_forcing_C3_ge3 | exact: g259_chiS_3_3_C3
       | by case=> /g259_forcing_C3_ge3 | exact: g259_chiS_3_3_C7].
Qed.

(** ** erdos:1105 ***************************************************************** *)
Definition g259_ar_hyp_claim : Prop :=
  [/\ 3 <= 3, x259_anti_ramsey_number 3 (cycle_graph 3) 2 &
      (anti_ramsey_cycles_paths_statement ->
         exists C N : nat, forall n a : nat, N <= n -> x259_anti_ramsey_number n (cycle_graph 3) a ->
           4 * a <= 4 * n + C /\ 4 * n <= 4 * a + C)].

Theorem g259_ar_hyp_inhabited : g259_ar_hyp_claim.
Proof. by split=> //; [exact: g259_AR_3_C3 | move=> h; exact: (proj1 h 3 (leqnn 3))]. Qed.

Definition g259_ar_no_number : Prop :=
  (forall k : nat, 3 <= k -> exists C N : nat, forall n a : nat, N <= n ->
     2 * (k - 1) * a <= ((k - 2) * (k - 1) + 2) * n + C /\
     ((k - 2) * (k - 1) + 2) * n <= 2 * (k - 1) * a + C) /\
  (forall n k a : nat, 5 <= k -> k <= n ->
     a = maxn ('C(k - 2, 2) + 1) ('C((k - 1) %/ 2 - 1, 2) + ((k - 1) %/ 2 - 1) * (n - (k - 1) %/ 2 + 1)
                                  + (if odd k then 1 else 2))).

Definition g259_ar_ntt_claim : Prop :=
  ~ g259_ar_no_number /\ (g259_ar_no_number -> anti_ramsey_cycles_paths_statement).

Theorem g259_ar_not_trivially_true : g259_ar_ntt_claim.
Proof.
split.
- by case=> _ h; have := h 5 5 0 isT isT.
- case=> h1 h2; split.
  + move=> k hk; have [C [N hN]] := h1 k hk; exists C, N => n a hn _; exact: hN.
  + move=> n k a hk hkn _; exact: h2.
Qed.

(** ** erdos:809 ****************************************************************** *)
Definition g259_cs_hyp_claim : Prop :=
  [/\ 3 <= 3, x259_strong_chromatic_number 3 (3 ^ 2 %/ 4 + 1) (cycle_graph (2 * 3 + 1)) 1 &
      (strong_chromatic_odd_cycles_statement ->
         exists N : nat, forall n s : nat, N <= n ->
           x259_strong_chromatic_number n (n ^ 2 %/ 4 + 1) (cycle_graph 7) s ->
           8 * s <= 2 * n ^ 2 /\ n ^ 2 <= 2 * (8 * s))].

Theorem g259_cs_hyp_inhabited : g259_cs_hyp_claim.
Proof.
split=> //; first exact: g259_chiS_3_3_C7.
move=> h; have [N hN] := h 3 1 (leqnn 3) (leqnn 1); exists N => n s hn hs.
by have := hN n s hn hs; rewrite !mul1n.
Qed.

Definition g259_cs_no_number : Prop :=
  forall k q : nat, 3 <= k -> 1 <= q -> exists N : nat, forall n s : nat, N <= n ->
    q * (8 * s) <= (q + 1) * n ^ 2 /\ q * n ^ 2 <= (q + 1) * (8 * s).

Definition g259_cs_ntt_claim : Prop :=
  ~ g259_cs_no_number /\ (g259_cs_no_number -> strong_chromatic_odd_cycles_statement).

Theorem g259_cs_not_trivially_true : g259_cs_ntt_claim.
Proof.
split.
- move=> h; have [N hN] := h 3 1 (leqnn 3) (leqnn 1).
  have [_] := hN N.+1 0 (leqnSn N); by rewrite !muln0 mul1n leqn0 expn_eq0.
- move=> h k q hk hq; have [N hN] := h k q hk hq; exists N => n s hn _; exact: hN.
Qed.

Print Assumptions g259_ar_helper_sanity.
Print Assumptions g259_cs_helper_sanity.
Print Assumptions g259_ar_hyp_inhabited.
Print Assumptions g259_ar_not_trivially_true.
Print Assumptions g259_cs_hyp_inhabited.
Print Assumptions g259_cs_not_trivially_true.

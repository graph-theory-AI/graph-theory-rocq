(** * GTMisc.conjectures.grounding_X288 -- grounding certificates of wave X288.

    hyp_inhabited and not_trivially_true for the six rows (the wave has no helper).  Each not_trivially_true is in
    the contract form: a variant of the body with one hypothesis or guard deleted is false and implies the row.
    - Pure pairs for forests: H = the edgeless graph on three vertices (a forest) and G = K_2, which is H-free and
      H-bar-free by order; the row then gives a pure pair of K_2.  Without |G| > 1 the row fails at K_1: a pure
      pair with both sides of linear size needs two disjoint nonempty sides.
    - Le's induced paths / cycles (and the O_2-free synonym): K_3 is 2O-free (two anticomplete cycles need six
      vertices); {0} is the vertex set of an induced path and the triangle that of an induced cycle.  Without the
      condition on the members of P the row fails on the edgeless graph with 2^(4c) vertices and P its power set:
      (2^(4c))^c < 2^(2^(4c)).
    - Coarse Menger (X116's statement) and the weak form: on K_1 with S = T = V and k = c = 1 the one-vertex path
      is an S-T path, and the row then gives its alternative there.  Without the path condition on p the row fails
      on K_1 with S = T empty: there is no S-T path, and the empty sequence has no vertex. *)

From GTBase Require Import base set_pairs induced_paths induced_cycles walks_paths balls distant_paths matching_graphs.
From GTMisc.conjectures Require Import X116 X288.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Small graphs *)

(** The edgeless graph on n vertices. *)
Definition g288_edgeless (n : nat) : sgraph :=
  @SGraph 'I_n (fun _ _ => false) (fun _ _ => erefl) (fun _ => erefl).

Lemma g288_edgeless_forest (n : nat) : is_forest [set: g288_edgeless n].
Proof.
apply: deg_le1_forest => x; rewrite (_ : N(x) = set0) ?cards0 //.
Qed.

Lemma g288_edgeless_no_cycle (n : nat) (c : seq (g288_edgeless n)) : ~ seq_cycle (--) c.
Proof.
case: c => [|x [|y q]] [uc s] //.
Qed.

(** ** Row studies:std_liebenau_pilipczuk_conjecture *)

Definition g288_pp_hyp_claim : Prop :=
  [/\ is_forest [set: g288_edgeless 3], 1 < #|'K_2|, induced_free ('K_2) (g288_edgeless 3),
      induced_free ('K_2) (compl (g288_edgeless 3)) &
      (liebenau_pilipczuk_forest_pure_pair_statement -> exists m : nat, 0 < m /\
         exists A B : {set 'K_2},
           (anticomplete A B || [disjoint A & B] && complete_between A B) /\
           #|'K_2| <= m * #|A| /\ #|'K_2| <= m * #|B|)].

Theorem g288_pp_hyp_inhabited : g288_pp_hyp_claim.
Proof.
have f3 := @g288_edgeless_forest 3.
have c2 : 1 < #|'K_2| by rewrite card_ord.
have fr : induced_free ('K_2) (g288_edgeless 3) by apply: induced_free_card; rewrite !card_ord.
have frc : induced_free ('K_2) (compl (g288_edgeless 3)) by apply: induced_free_card; rewrite /= !card_ord.
split=> //.
move=> /(_ _ f3) [m [m0 h]]; exists m; split=> //.
exact: h c2 fr frc.
Qed.

(** The body without [1 < #|G|]. *)
Definition g288_pp_no_guard : Prop :=
  forall H : sgraph, is_forest [set: H] ->
    exists m : nat, 0 < m /\
      forall G : sgraph, induced_free G H -> induced_free G (compl H) ->
        exists A B : {set G},
          (anticomplete A B || [disjoint A & B] && complete_between A B) /\
          #|G| <= m * #|A| /\ #|G| <= m * #|B|.

Definition g288_pp_ntt_claim : Prop :=
  ~ g288_pp_no_guard /\ (g288_pp_no_guard -> liebenau_pilipczuk_forest_pure_pair_statement).

Theorem g288_pp_not_trivially_true : g288_pp_ntt_claim.
Proof.
split; last by move=> h H f; have [m [m0 hm]] := h H f; exists m; split=> // G _; exact: hm.
move=> /(_ _ (@g288_edgeless_forest 3)) [m [m0 h]].
have fr : induced_free ('K_1) (g288_edgeless 3) by apply: induced_free_card; rewrite !card_ord.
have frc : induced_free ('K_1) (compl (g288_edgeless 3)) by apply: induced_free_card; rewrite /= !card_ord.
have [A [B [pp [hA hB]]]] := h _ fr frc.
have A0 : A != set0 by apply/eqP => A0; move: hA; rewrite A0 cards0 muln0 card_ord.
have B0 : B != set0 by apply/eqP => B0; move: hB; rewrite B0 cards0 muln0 card_ord.
have dj : [disjoint A & B] by case/orP: pp => [/andP [] | /andP []].
have /set0Pn [a aA] := A0; have /set0Pn [b bB] := B0.
by move: dj; rewrite disjoint_subset => /subsetP /(_ a aA); rewrite inE (ord1 a) -(ord1 b) bB.
Qed.

(** ** Rows studies:std_le_s_induced_paths_conjecture and
       studies:std_le_s_conjecture_on_induced_cycles_in_2o_free_gra *)

(** 4 c^2 < 16^c, so (2^(4c))^c < 2^(2^(4c)). *)
Lemma g288_poly_lt_exp (c : nat) : 0 < c -> (2 ^ (4 * c)) ^ c < 2 ^ (2 ^ (4 * c)).
Proof.
move=> c0; rewrite -expnM ltn_exp2l //.
have h1 : c < 2 ^ c := ltn_expl c (ltnSn 1).
have h2 : c * c < 2 ^ c * 2 ^ c := ltn_mul h1 h1.
have h3 : 2 <= 2 ^ c by rewrite -{1}(expn1 2) leq_exp2l.
have h4 : 4 <= 2 ^ c * 2 ^ c := leq_mul h3 h3.
rewrite -mulnA (mulnC 4 c) expnM.
have -> : (2 ^ c) ^ 4 = (2 ^ c * 2 ^ c) * (2 ^ c * 2 ^ c) by rewrite !expnS expn0 muln1 !mulnA.
rewrite mulnC.
apply: (@leq_trans (4 * (2 ^ c * 2 ^ c))); first by rewrite (mulnC (c * c)) ltn_pmul2l.
by rewrite leq_mul2r h4 orbT.
Qed.

(** The common body of the two rows without the condition on the members of [P]. *)
Definition g288_le_any_family : Prop :=
  exists c : nat, 0 < c /\
    forall G : sgraph,
      ~ (exists c1 c2 : seq G,
           [/\ seq_cycle (--) c1, seq_cycle (--) c2 & anticomplete (seq_vertices c1) (seq_vertices c2)]) ->
      forall P : {set {set G}}, #|P| <= #|G| ^ c.

Lemma g288_le_any_family_false : ~ g288_le_any_family.
Proof.
move=> [c [c0 h]].
have nc : ~ (exists c1 c2 : seq (g288_edgeless (2 ^ (4 * c))),
            [/\ seq_cycle (--) c1, seq_cycle (--) c2 & anticomplete (seq_vertices c1) (seq_vertices c2)]).
  by move=> [c1 [c2 [h1 _ _]]]; exact: g288_edgeless_no_cycle h1.
have := h _ nc (powerset [set: g288_edgeless (2 ^ (4 * c))]).
rewrite card_powerset cardsT card_ord => le.
by move: (leq_ltn_trans le (g288_poly_lt_exp c0)); rewrite ltnn.
Qed.

(** A cycle has at least three distinct vertices, so two anticomplete cycles need six. *)
Lemma g288_cycle_card (G : sgraph) (c : seq G) : seq_cycle (--) c -> 3 <= #|seq_vertices c|.
Proof.
move=> [/andP [_ uc] sz]; rewrite /seq_vertices cardsE.
by rewrite (card_uniqP uc).
Qed.

Lemma g288_small_2O_free (G : sgraph) : #|G| < 6 ->
  ~ (exists c1 c2 : seq G,
       [/\ seq_cycle (--) c1, seq_cycle (--) c2 & anticomplete (seq_vertices c1) (seq_vertices c2)]).
Proof.
move=> lt [c1 [c2 [h1 h2 /andP [dj _]]]].
have := cardsU (seq_vertices c1) (seq_vertices c2); rewrite (disjoint_setI0 dj) cards0 subn0 => e.
have : 6 <= #|seq_vertices c1 :|: seq_vertices c2|.
  by rewrite e (@leq_add 3 3) // g288_cycle_card.
by move=> h6; move: (leq_trans h6 (max_card _)); rewrite leqNgt lt.
Qed.

(** Induced paths: on K_3, {0} is the vertex set of an induced path. *)
Definition g288_ip_family : {set {set 'K_3}} := [set [set (ord0 : 'K_3)]].

Definition g288_ip_hyp_claim : Prop :=
  [/\ ~ (exists c1 c2 : seq ('K_3),
           [/\ seq_cycle (--) c1, seq_cycle (--) c2 & anticomplete (seq_vertices c1) (seq_vertices c2)]),
      (forall S, S \in g288_ip_family -> exists p : seq ('K_3), nonempty_induced_path p /\ seq_vertices p = S) &
      (le_induced_paths_polynomial_statement -> exists c : nat, #|g288_ip_family| <= #|'K_3| ^ c)].

Theorem g288_ip_hyp_inhabited : g288_ip_hyp_claim.
Proof.
have nc := @g288_small_2O_free 'K_3 (ltac:(by rewrite card_ord)).
have fam : forall S, S \in g288_ip_family -> exists p : seq ('K_3), nonempty_induced_path p /\ seq_vertices p = S.
  move=> S; rewrite inE => /eqP ->; exists [:: ord0]; split.
    split=> //; split=> // u v; rewrite !inE => /eqP -> /eqP ->; by rewrite sg_irrefl.
  by apply/setP => x; rewrite !inE.
split=> // -[c [c0 h]]; exists c; exact: h nc _ fam.
Qed.

Definition g288_ip_ntt_claim : Prop :=
  ~ g288_le_any_family /\ (g288_le_any_family -> le_induced_paths_polynomial_statement).

Theorem g288_ip_not_trivially_true : g288_ip_ntt_claim.
Proof.
split; first exact: g288_le_any_family_false.
by move=> [c [c0 h]]; exists c; split=> // G nc P _; exact: h.
Qed.

(** Induced cycles: the triangle of K_3 is an induced cycle. *)
Definition g288_ic_family : {set {set 'K_3}} := [set [set: 'K_3]].

Definition g288_ic_hyp_claim : Prop :=
  [/\ ~ (exists c1 c2 : seq ('K_3),
           [/\ seq_cycle (--) c1, seq_cycle (--) c2 & anticomplete (seq_vertices c1) (seq_vertices c2)]),
      (forall S, S \in g288_ic_family -> exists p : seq ('K_3), chordless_cycle p /\ seq_vertices p = S) &
      (le_induced_cycles_polynomial_statement -> exists c : nat, #|g288_ic_family| <= #|'K_3| ^ c)].

Theorem g288_ic_hyp_inhabited : g288_ic_hyp_claim.
Proof.
have tri : chordless_cycle [:: (@Ordinal 3 0 isT : 'K_3); @Ordinal 3 1 isT; @Ordinal 3 2 isT].
  by apply/chordless_cycleP; vm_compute.
have nc := @g288_small_2O_free 'K_3 (ltac:(by rewrite card_ord)).
have fam : forall S, S \in g288_ic_family -> exists p : seq ('K_3), chordless_cycle p /\ seq_vertices p = S.
  move=> S; rewrite inE => /eqP ->.
  exists [:: (@Ordinal 3 0 isT : 'K_3); @Ordinal 3 1 isT; @Ordinal 3 2 isT]; split=> //.
  by apply/setP => x; rewrite !inE; case: x => -[|[|[|n]]] Hx //=.
split=> // -[c [c0 h]]; exists c; exact: h nc _ fam.
Qed.

Definition g288_ic_ntt_claim : Prop :=
  ~ g288_le_any_family /\ (g288_le_any_family -> le_induced_cycles_polynomial_statement).

Theorem g288_ic_not_trivially_true : g288_ic_ntt_claim.
Proof.
split; first exact: g288_le_any_family_false.
by move=> [c [c0 h]]; exists c; split=> // G nc P _; exact: h.
Qed.

(** ** Row studies:std_le_s_conjecture_on_induced_paths_in_o_free_graph (the synonym of the induced-paths row) *)

Definition g288_o2_hyp_claim : Prop :=
  [/\ ~ (exists c1 c2 : seq ('K_3),
           [/\ seq_cycle (--) c1, seq_cycle (--) c2 & anticomplete (seq_vertices c1) (seq_vertices c2)]),
      (forall S, S \in g288_ip_family -> exists p : seq ('K_3), nonempty_induced_path p /\ seq_vertices p = S) &
      (le_induced_paths_o2_free_duplicate_statement -> exists c : nat, #|g288_ip_family| <= #|'K_3| ^ c)].

Theorem g288_o2_hyp_inhabited : g288_o2_hyp_claim.
Proof. exact: g288_ip_hyp_inhabited. Qed.

Definition g288_o2_ntt_claim : Prop :=
  ~ g288_le_any_family /\ (g288_le_any_family -> le_induced_paths_o2_free_duplicate_statement).

Theorem g288_o2_not_trivially_true : g288_o2_ntt_claim.
Proof. exact: g288_ip_not_trivially_true. Qed.

(** ** Rows studies:std_coarse_menger_conjecture_159 and studies:std_weak_coarse_menger_conjecture_nguyen_scott_seymo *)

(** No S-T path when S and T are empty. *)
Lemma g288_no_path_set0 (G : sgraph) (p : seq G) : ~ seq_set_path set0 set0 p.
Proof. by case: p => [|x q] //= [] ; rewrite inE. Qed.

(** K_1, S = T = V, k = c = 1: the one-vertex path. *)
Lemma g288_K1_one_path : has_k_distant_set_paths 1 1 [set: 'K_1] [set: 'K_1].
Proof.
exists [:: [:: ord0]]; split=> //; split=> //; split.
  by move=> p; rewrite inE => /eqP ->; rewrite /seq_set_path /= !inE.
by move=> p q; rewrite !inE => /eqP -> /eqP ->; rewrite eqxx.
Qed.

(** Coarse Menger, in the canonical vocabulary that X116's helpers alias (GTBase distant_paths, walks_paths, balls). *)
Definition g288_cm_hyp_claim : Prop :=
  [/\ 1 <= 1, has_k_distant_set_paths 1 1 [set: 'K_1] [set: 'K_1] &
      (coarse_menger_paths_bounded_separator_duplicate_statement -> exists l : nat,
         has_k_distant_set_paths 1 1 [set: 'K_1] [set: 'K_1] \/
         exists X : {set 'K_1}, #|X| <= 1 - 1 /\
           forall p : seq ('K_1), seq_set_path [set: 'K_1] [set: 'K_1] p ->
             exists v : ('K_1), v \in seq_vertices p /\ v \in set_ball l X)].

Theorem g288_cm_hyp_inhabited : g288_cm_hyp_claim.
Proof.
split=> //; first exact: g288_K1_one_path.
move=> /(_ 1 1 isT isT) [l [_ h]]; exists l; exact: h.
Qed.

(** X116's body, in the canonical vocabulary, without the path condition on p. *)
Definition g288_cm_any_seq : Prop :=
  forall (k d : nat), 1 <= k -> 1 <= d ->
    exists l : nat, 0 < l /\
      forall (G : sgraph) (S T : {set G}),
        has_k_distant_set_paths d k S T \/
        exists X : {set G}, #|X| <= k - 1 /\
          forall p : seq G, exists v : G, v \in seq_vertices p /\ v \in set_ball l X.

Lemma g288_cm_any_seq_false : ~ g288_cm_any_seq.
Proof.
move=> /(_ 1 1 isT isT) [l [_ /(_ ('K_1) set0 set0)]] [[ps [sz [_ [hp _]]]] | [X [_ hX]]].
  by case: ps sz hp => [|p ps'] //= _ /(_ p (mem_head _ _)) /g288_no_path_set0.
by have [v []] := hX [::]; rewrite /seq_vertices inE.
Qed.

Definition g288_cm_ntt_claim : Prop :=
  ~ g288_cm_any_seq /\ (g288_cm_any_seq -> coarse_menger_paths_bounded_separator_duplicate_statement).

Theorem g288_cm_not_trivially_true : g288_cm_ntt_claim.
Proof.
split; first exact: g288_cm_any_seq_false.
move=> h k d k1 d1; have [l [l0 hl]] := h k d k1 d1; exists l; split=> // G S T.
by case: (hl G S T) => [hk | [X [kX hX]]]; [left | right; exists X; split=> // p _; exact: hX].
Qed.

(** The weak form. *)
Definition g288_wcm_hyp_claim : Prop :=
  [/\ 1 <= 1, has_k_distant_set_paths 1 1 [set: 'K_1] [set: 'K_1] &
      (weak_coarse_menger_statement -> exists m l : nat,
         has_k_distant_set_paths 1 1 [set: 'K_1] [set: 'K_1] \/
         exists X : {set 'K_1}, #|X| <= m /\
           forall p : seq ('K_1), seq_set_path [set: 'K_1] [set: 'K_1] p ->
             exists2 v : ('K_1), v \in seq_vertices p & v \in set_ball l X)].

Theorem g288_wcm_hyp_inhabited : g288_wcm_hyp_claim.
Proof.
split=> //; first exact: g288_K1_one_path.
move=> /(_ 1 1 isT isT) [m [l [_ _ h]]]; exists m, l; exact: h.
Qed.

(** The weak body without the path condition on p. *)
Definition g288_wcm_any_seq : Prop :=
  forall k c : nat, 1 <= k -> 1 <= c ->
    exists m l : nat, [/\ 0 < m, 0 < l &
      forall (G : sgraph) (S T : {set G}),
        has_k_distant_set_paths c k S T \/
        exists X : {set G}, #|X| <= m /\
          forall p : seq G, exists2 v : G, v \in seq_vertices p & v \in set_ball l X].

Lemma g288_wcm_any_seq_false : ~ g288_wcm_any_seq.
Proof.
move=> /(_ 1 1 isT isT) [m [l [_ _ /(_ ('K_1) set0 set0)]]] [[ps [sz [_ [hp _]]]] | [X [_ hX]]].
  by case: ps sz hp => [|p ps'] //= _ /(_ p (mem_head _ _)) /g288_no_path_set0.
by have [v] := hX [::]; rewrite /seq_vertices inE.
Qed.

Definition g288_wcm_ntt_claim : Prop :=
  ~ g288_wcm_any_seq /\ (g288_wcm_any_seq -> weak_coarse_menger_statement).

Theorem g288_wcm_not_trivially_true : g288_wcm_ntt_claim.
Proof.
split; first exact: g288_wcm_any_seq_false.
move=> h k c k1 c1; have [m [l [m0 l0 hm]]] := h k c k1 c1; exists m, l; split=> // G S T.
by case: (hm G S T) => [hk | [X [mX hX]]]; [left | right; exists X; split=> // p _; exact: hX].
Qed.

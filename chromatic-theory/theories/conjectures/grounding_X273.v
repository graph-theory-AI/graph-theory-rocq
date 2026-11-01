(** * Chromatic.conjectures.grounding_X273 -- grounding certificates for wave X273 (2026-11-01)

    For each of the three rows: hyp_inhabited (the hypotheses hold at a small instance, and the statement then gives
    its conclusion there) and not_trivially_true (a variant without one hypothesis is false and implies the
    statement); and, in every row, the helper_sanity group of the X273.v helper.
    - arxiv:2108.12669#00: K_1 is planar and triangle-free with 3 proper 3-colourings, and the instance a = 0, b = 1,
      m = 1 asks 2 <= 3^k; without triangle-freeness the row is false at K_4 (no proper 3-colouring, 2 <= 0).
    - arxiv:2103.05998#00: m = 4 and t = 1 are admissible, and the statement bounds chi(G_(4,1)) between 1 / k and k;
      without 4 t^2 <= m the row is false at m = 2 (four vertices, chi <= 4, while t^2 grows).
    - arxiv:1809.05439#00: K_2 is planar and triangle-free, and the statement gives disjoint sets of five and at
      least three colours on its edge; without triangle-freeness the row is false at K_3 (5 + 3 + 3 > 9).
    - helper_sanity: G_(m,t) has 2^m vertices and its adjacency is the strict Hamming threshold; G_(4,1) has an
      edge and a proper colouring by the first two coordinates, so 1 <= chi <= 4 there. *)

From GTBase Require Import base common colourings.
From Chromatic.conjectures Require Import X273.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Small graphs ******************************************************************************* *)

Lemma g273_planar_small (G : sgraph) : #|G| <= 4 -> wagner_planar G.
Proof.
move=> le4; split=> m; move: (leq_trans (minor_card m) le4).
- by rewrite card_ord.
- by rewrite card_sum !card_ord.
Qed.

Lemma g273_triangle_free_K2 : triangle_free ('K_2).
Proof.
move=> x y z; rewrite /edge_rel /=.
by case: x => [[|[|//]] ?]; case: y => [[|[|//]] ?]; case: z => [[|[|//]] ?].
Qed.

(** The proper 3-colourings of K_1 are its three maps. *)
Lemma g273_col_K1 : #|[set f : {ffun ('K_1) -> 'I_3} | proper_colouring f]| = 3.
Proof.
have -> : [set f : {ffun ('K_1) -> 'I_3} | proper_colouring f] = [set: {ffun ('K_1) -> 'I_3}].
  apply/setP => f; rewrite !inE; apply/proper_colouringP => x y.
  by rewrite (ord1 x) (ord1 y) sg_irrefl.
by rewrite cardsT card_ffun !card_ord.
Qed.

(** K_4 has no proper 3-colouring: it would be injective into three colours. *)
Lemma g273_col_K4 : #|[set f : {ffun ('K_4) -> 'I_3} | proper_colouring f]| = 0.
Proof.
apply/eqP; rewrite cards_eq0; apply/eqP/setP => f; rewrite !inE; apply/negP => /proper_colouringP h.
have inj : injective f by move=> x y; apply: contra_eq => xy; apply: h; rewrite /edge_rel /= xy.
by have := leq_card f inj; rewrite !card_ord.
Qed.

(** Disjoint sets add their sizes. *)
Lemma g273_card_disjointU (T : finType) (A B : {set T}) : [disjoint A & B] -> #|A :|: B| = #|A| + #|B|.
Proof. by rewrite -setI_eq0 -cardsUI => /eqP ->; rewrite cards0 addn0. Qed.

(** ** Alon's graph ****************************************************************************** *)

Lemma g273_alon_card (m t : nat) : #|x273_alon m t| = 2 ^ m.
Proof. by rewrite card_ffun card_bool card_ord. Qed.

(** The closure taken by [fg_mk_sgraph] is the Hamming threshold itself. *)
Lemma g273_alon_edge (m t : nat) (u v : x273_alon m t) :
  u -- v = (m - 2 * t < #|[set i | (u : {ffun 'I_m -> bool}) i != v i]|).
Proof.
rewrite /edge_rel /= /fg_srel.
have sym : [set i | (v : {ffun 'I_m -> bool}) i != u i] = [set i | (u : {ffun 'I_m -> bool}) i != v i].
  by apply/setP => i; rewrite !inE eq_sym.
rewrite sym orbb; case: eqP => [<-|//].
have -> : [set i | (u : {ffun 'I_m -> bool}) i != u i] = set0 by apply/setP => i; rewrite !inE eqxx.
by rewrite cards0 ltn0.
Qed.

(** G_(4,1): two vectors that agree on the first two coordinates are at distance at most 2 = m - 2t. *)
Lemma g273_alon_4_1_chi : χ([set: x273_alon 4 1]) <= 4.
Proof.
pose col (u : x273_alon 4 1) : bool * bool := ((u : {ffun 'I_4 -> bool}) ord0, (u : {ffun 'I_4 -> bool}) (inord 1)).
pose A : {set 'I_4} := [set ord0; inord 1].
have n01 : (ord0 : 'I_4) != inord 1 by rewrite -val_eqE /= inordK.
have := cardsC A; rewrite cards2 card_ord n01 => /eqP; rewrite eqSS => /eqP cA.
have {}cA : #|~: A| = 2 by case: cA.
have : proper_colouring col.
  apply/proper_colouringP => u v; rewrite g273_alon_edge; apply: contraTneq => -[e0 e1].
  rewrite -leqNgt; apply: (@leq_trans #|~: A|); last by rewrite cA.
  apply: subset_leq_card; apply/subsetP => i; rewrite !inE.
  by apply: contraTN => /orP [] /eqP ->; rewrite negbK ?e0 ?e1.
by move/proper_colouring_chi; rewrite card_prod card_bool.
Qed.

(** ** helper_sanity ****************************************************************************** *)

(** [x273_alon]: G_(m,t) has 2^m vertices, its adjacency is the strict Hamming threshold, and G_(4,1) has an edge
    and chromatic number at most 4. *)
Definition g273_alon_helper_claim : Prop :=
  [/\ forall m t : nat, #|x273_alon m t| = 2 ^ m,
      forall (m t : nat) (u v : x273_alon m t),
        u -- v = (m - 2 * t < #|[set i | (u : {ffun 'I_m -> bool}) i != v i]|),
      exists u v : x273_alon 4 1, u -- v &
      χ([set: x273_alon 4 1]) <= 4].

Theorem g273_alon_helper_sanity : g273_alon_helper_claim.
Proof.
split; [exact: g273_alon_card | exact: g273_alon_edge | | exact: g273_alon_4_1_chi].
exists ([ffun _ => false] : {ffun 'I_4 -> bool}), ([ffun _ => true] : {ffun 'I_4 -> bool}).
rewrite g273_alon_edge.
have -> : [set i | ([ffun _ => false] : {ffun 'I_4 -> bool}) i != ([ffun _ => true] : {ffun 'I_4 -> bool}) i] =
          [set: 'I_4] by apply/setP => i; rewrite !inE !ffunE.
by rewrite cardsT card_ord.
Qed.

(** ** arxiv:2108.12669#00 *********************************************************************** *)

(** hyp_inhabited: K_1 is planar and triangle-free with 3 proper 3-colourings; at a = 0, b = 1, m = 1 the
    statement's constant then satisfies 2 <= 3^k. *)
Definition g273_dp_hyp_claim : Prop :=
  [/\ 0 < #|'K_1|, wagner_planar ('K_1), triangle_free ('K_1),
      #|[set f : {ffun ('K_1) -> 'I_3} | proper_colouring f]| = 3 &
      (dvorak_postle_triangle_free_planar_three_colourings_lower_bound_statement ->
         exists k : nat, 0 < k /\ 2 <= 3 ^ k)].

Theorem g273_dp_hyp_inhabited : g273_dp_hyp_claim.
Proof.
have pl : wagner_planar ('K_1) by apply: g273_planar_small; rewrite card_ord.
have tf : triangle_free ('K_1) by move=> x y z; rewrite (ord1 x) (ord1 y) sg_irrefl.
have n0 : 0 < #|'K_1| by rewrite card_ord.
split=> //; first exact: g273_col_K1.
move=> [k [k0 h]]; exists k; split=> //.
by have := h _ n0 pl tf 0 1 1 isT isT; rewrite g273_col_K1.
Qed.

(** not_trivially_true: without triangle-freeness, K_4 is planar with no proper 3-colouring, and a = 0, b = 1,
    m = 1 asks 2 <= 0. *)
Definition g273_dp_no_triangle_free : Prop :=
  exists k : nat, 0 < k /\
    forall G : sgraph, 0 < #|G| -> wagner_planar G ->
      forall a b m : nat, 9 ^ a < 3 ^ b * 2 ^ a -> m ^ b <= #|G| ^ a ->
        2 ^ m <= #|[set f : {ffun G -> 'I_3} | proper_colouring f]| ^ k.

Definition g273_dp_ntt_claim : Prop :=
  ~ g273_dp_no_triangle_free /\
  (g273_dp_no_triangle_free -> dvorak_postle_triangle_free_planar_three_colourings_lower_bound_statement).

Theorem g273_dp_not_trivially_true : g273_dp_ntt_claim.
Proof.
split; last by move=> [k [k0 h]]; exists k; split=> // G n0 pl _; exact: h.
move=> [k [k0 h]].
have pl : wagner_planar ('K_4) by apply: g273_planar_small; rewrite card_ord.
have n0 : 0 < #|'K_4| by rewrite card_ord.
by have := h _ n0 pl 0 1 1 isT isT; rewrite g273_col_K4 exp0n.
Qed.

(** ** arxiv:2103.05998#00 *********************************************************************** *)

(** hyp_inhabited: m = 4 and t = 1 are admissible, and the statement's constant k then bounds chi(G_(4,1)) between
    1 / k and k. *)
Definition g273_alon_hyp_claim : Prop :=
  [/\ 0 < 1, ~~ odd 4, 4 * 1 ^ 2 <= 4 &
      (alon_hamming_graph_chromatic_number_theta_t_squared_statement ->
         exists k : nat, [/\ 0 < k, 1 <= k * χ([set: x273_alon 4 1]) & χ([set: x273_alon 4 1]) <= k])].

Theorem g273_alon_hyp_inhabited : g273_alon_hyp_claim.
Proof.
split=> // -[k [k0 h]]; exists k.
by have [lo up] := h 4 1 isT isT isT; rewrite exp1n muln1 in up; rewrite exp1n in lo.
Qed.

(** not_trivially_true: without 4 t^2 <= m, m = 2 gives a graph on four vertices, so chi <= 4, while
    t = 4k + 1 asks t^2 <= 4k. *)
Definition g273_alon_no_size : Prop :=
  exists k : nat, 0 < k /\
    forall m t : nat, 0 < t -> ~~ odd m ->
      t ^ 2 <= k * χ([set: x273_alon m t]) /\ χ([set: x273_alon m t]) <= k * t ^ 2.

Definition g273_alon_ntt_claim : Prop :=
  ~ g273_alon_no_size /\ (g273_alon_no_size -> alon_hamming_graph_chromatic_number_theta_t_squared_statement).

Theorem g273_alon_not_trivially_true : g273_alon_ntt_claim.
Proof.
split; last by move=> [k [k0 h]]; exists k; split=> // m t t0 ev _; exact: h.
move=> [k [k0 h]].
have [lo _] := h 2 (k * 4).+1 (ltn0Sn _) isT.
have c4 : χ([set: x273_alon 2 (k * 4).+1]) <= 4.
  by apply: leq_trans (leq_chi _) _; rewrite cardsT g273_alon_card.
have sq : (k * 4).+1 <= (k * 4).+1 ^ 2 by rewrite expnS expn1 leq_pmulr.
by have := leq_trans sq (leq_trans lo (leq_mul (leqnn k) c4)); rewrite ltnn.
Qed.

(** ** arxiv:1809.05439#00 *********************************************************************** *)

(** hyp_inhabited: K_2 is planar and triangle-free, and the statement gives its edge disjoint sets of five and at
    least three colours. *)
Definition g273_dh_hyp_claim : Prop :=
  [/\ wagner_planar ('K_2), triangle_free ('K_2) &
      (dvorak_hu_triangle_free_planar_nine_colour_sets_statement ->
         exists phi : 'K_2 -> {set 'I_9},
           [/\ #|phi ord0| = 5, 3 <= #|phi ord_max| & [disjoint phi ord0 & phi ord_max]])].

Theorem g273_dh_hyp_inhabited : g273_dh_hyp_claim.
Proof.
have pl : wagner_planar ('K_2) by apply: g273_planar_small; rewrite card_ord.
split=> //; first exact: g273_triangle_free_K2.
move=> /(_ _ pl g273_triangle_free_K2 ord0) [phi [h3 h5 hd]].
by exists phi; split=> //; apply: hd.
Qed.

(** not_trivially_true: without triangle-freeness, K_3 is planar, and pairwise disjoint sets of five, three and
    three colours do not fit in nine. *)
Definition g273_dh_no_triangle_free : Prop :=
  forall G : sgraph, wagner_planar G -> forall x : G,
    exists phi : G -> {set 'I_9},
      [/\ forall v : G, 3 <= #|phi v|, #|phi x| = 5 & forall u v : G, u -- v -> [disjoint phi u & phi v]].

Definition g273_dh_ntt_claim : Prop :=
  ~ g273_dh_no_triangle_free /\
  (g273_dh_no_triangle_free -> dvorak_hu_triangle_free_planar_nine_colour_sets_statement).

Theorem g273_dh_not_trivially_true : g273_dh_ntt_claim.
Proof.
split; last by move=> h G pl _ x; exact: h.
move=> h.
have pl : wagner_planar ('K_3) by apply: g273_planar_small; rewrite card_ord.
have [phi [h3 h5 hd]] := h _ pl ord0.
pose o1 : 'K_3 := inord 1; pose o2 : 'K_3 := inord 2.
have e01 : (ord0 : 'K_3) -- o1 by rewrite /edge_rel /= -val_eqE /= inordK.
have e02 : (ord0 : 'K_3) -- o2 by rewrite /edge_rel /= -val_eqE /= inordK.
have e12 : o1 -- o2 by rewrite /edge_rel /= -val_eqE /= !inordK.
have d01 := hd _ _ e01; have d02 := hd _ _ e02; have d12 := hd _ _ e12.
have dU : [disjoint phi ord0 :|: phi o1 & phi o2].
  rewrite -setI_eq0 setIUl; move: d02 d12; rewrite -!setI_eq0 => /eqP -> /eqP ->.
  by rewrite setU0.
have := max_card (phi ord0 :|: phi o1 :|: phi o2).
rewrite card_ord (g273_card_disjointU dU) (g273_card_disjointU d01) h5 => le9.
by have := leq_trans (leq_add (leq_add (leqnn 5) (h3 o1)) (h3 o2)) le9.
Qed.

(** Every proof block above ends in Qed. *)

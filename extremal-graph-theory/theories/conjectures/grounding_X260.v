(** * Extremal.conjectures.grounding_X260 -- grounding certificates of wave X260.

    For each of the three rows: hyp_inhabited (the hypotheses hold with concrete values, and the statement then gives
    its conclusion at a concrete parameter) and not_trivially_true in the contract form of meta/EXPANSION_PLAN.md 4.4
    (a variant obtained from the body is false and implies the row): each row without its relational hypothesis
    (erdos:927 without g(n) = a: a = N + C + 1 breaks the upper half; arxiv:2301.13305 #00 and #01 without the code
    hypothesis: all 2^C(n,2) graphs on [n] at q = 2, H = K_4).  The concrete values: g(1) = 1 (a graph on one vertex
    has one maximal clique, its vertex set; no convention on empty cliques is involved) and the one-member family
    [set set0], a K_4-code on [4].  g260_number_0 records g(0) = 1 under the library's empty-clique convention
    (Er66b's nonempty cliques give 0; only n = 0 differs).
    helper_sanity, group 1 (clique sizes): a vertex beside an edge has two maximal-clique sizes (1 and 2), K_3 has one
    (3), g(1) = 1, log* 4 = 3 and log* 16 = 4 (computed).  Group 2 (copies and codes), on K_2: its one edge is a copy
    of K_2 and set0 is not; [set set0] is a K_2-code and [set set0; E(K_2)] is not; every K_2-code on [2] has at most
    one member. *)

From Extremal.conjectures Require Import X260.
From GTBase Require Import base common maximal_cliques.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** K_2: copies and codes on two vertices ********************************** *)

Local Notation p0 := (@Ordinal 2 0 isT).
Local Notation p1 := (@Ordinal 2 1 isT).

Lemma g260_EK2 : E('K_2) = [set [set p0; p1]].
Proof.
apply/setP => e; rewrite !inE.
apply/edgesP/eqP => [[x [y [-> xy]]]|->]; last by exists p0, p1.
move: x y xy; case=> [[|[|//]] hx] [[|[|//]] hy] //= _.
  by congr [set _; _]; apply: val_inj.
by rewrite setUC; congr [set _; _]; apply: val_inj.
Qed.

Lemma g260_copy_K2 : x260_copy 'K_2 E('K_2).
Proof.
exists id; split=> //.
by rewrite (eq_imset (g := id)) ?imset_id // => e; rewrite imset_id.
Qed.

Lemma g260_not_copy_K2 : ~ @x260_copy 2 'K_2 set0.
Proof.
case=> f [_ /esym/eqP]; rewrite imset_eq0 g260_EK2.
by apply/negP/set0Pn; exists [set p0; p1]; rewrite inE.
Qed.

Lemma g260_not_code_K2 : ~ x260_code 'K_2 [set set0; E('K_2)].
Proof.
case=> _ /(_ set0 E('K_2)); rewrite !inE eqxx.
rewrite eqxx orbT => /(_ isT isT); apply.
  by rewrite eq_sym g260_EK2; apply/set0Pn; exists [set p0; p1]; rewrite inE.
by rewrite set0D setD0 set0U; exact: g260_copy_K2.
Qed.

Lemma g260_code_K2 : @x260_code 2 'K_2 [set set0].
Proof.
split=> [A|A B]; rewrite !inE => /eqP->; first exact: sub0set.
by move=> /eqP->; rewrite eqxx.
Qed.

Lemma g260_code_K2_le (F : {set {set {set 'K_2}}}) : x260_code 'K_2 F -> 2 * #|F| <= 2 ^ 'C(2, 2).
Proof.
case=> sub code.
have -> : 2 ^ 'C(2, 2) = 2 * 1 by [].
rewrite leq_pmul2l // leqNgt; apply/negP.
case/card_gt1P => A [B [AF BF AB]]; apply: (code A B AF BF AB).
have := sub A AF; have := sub B BF; rewrite g260_EK2 !subset1.
case/orP => /eqP BE; case/orP => /eqP AE; subst A B; rewrite ?eqxx // in AB *.
  by rewrite set0D setD0 set0U -g260_EK2; exact: g260_copy_K2.
by rewrite set0D setD0 setU0 -g260_EK2; exact: g260_copy_K2.
Qed.

(** ** Clique sizes: g(0) = 1, K_n, and a vertex beside an edge ******************* *)

(** g(0) = 1 under the library's convention: in the graph with no vertex, set0 is the one maximal clique.  Er66b
    takes cliques nonempty, which gives g(0) = 0; only n = 0 differs, and every n >= 1 agrees (set0 is never maximal
    when there is a vertex). *)
Lemma g260_number_0 : x260_clique_size_number 0 1.
Proof.
split.
  exists 'K_0; split; first by rewrite card_ord.
  apply/eqP; rewrite eqn_leq; apply/andP; split.
    by apply: leq_trans (max_card _) _; rewrite !card_ord.
  rewrite card_gt0; apply/set0Pn; exists ord0; rewrite inE.
  apply/existsP; exists set0; rewrite cards0 eqxx andbT.
  apply/maximal_cliqueP; split; first by move=> x; rewrite inE.
  by move=> T /properP [_ [[x hx] _ _]].
move=> G hG; apply: leq_trans (max_card _) _; by rewrite card_ord hG.
Qed.

Lemma g260_Kn_clique n (S : {set 'K_n}) : clique S.
Proof. by move=> x y _ _ xy. Qed.

Lemma g260_Kn_maximal n (S : {set 'K_n}) : maximal_clique S = (S == setT).
Proof.
apply/maximal_cliqueP/eqP => [[_ h]|->].
  apply/eqP; apply: contraT => nT; case: (h setT); first by rewrite properT.
  exact: g260_Kn_clique.
split; first exact: g260_Kn_clique.
by move=> T /proper_sub_trans/(_ (subsetT T)); rewrite properE subxx.
Qed.

Lemma g260_count_Kn n : x260_clique_size_count 'K_n.+1 = 1.
Proof.
rewrite /x260_clique_size_count.
have -> : [set k : 'I_#|'K_n.+1|.+1 | [exists S : {set 'K_n.+1}, maximal_clique S && (#|S| == k)]] =
          [set inord n.+1].
  apply/setP => k; rewrite !inE; apply/existsP/eqP => [[S /andP [mS /eqP hk]]|->].
    move: mS; rewrite g260_Kn_maximal => /eqP SE; subst S.
    by apply: val_inj; rewrite /= -hk cardsT card_ord inordK // card_ord.
  by exists setT; rewrite g260_Kn_maximal eqxx /= cardsT card_ord inordK // card_ord.
by rewrite cards1.
Qed.

Lemma g260_count_K3 : x260_clique_size_count 'K_3 = 1.
Proof. exact: g260_count_Kn. Qed.

(** In a graph whose vertex set is a clique, the only maximal clique is the vertex set. *)
Lemma g260_clique_setT (G : sgraph) (S : {set G}) : clique [set: G] -> maximal_clique S -> S = setT.
Proof.
move=> cT /maximal_cliqueP [_ h]; apply/eqP; apply: contraT => nT.
by case: (h setT); first by rewrite properT.
Qed.

Lemma g260_clique_one (G : sgraph) : #|G| = 1 -> clique [set: G].
Proof. by move=> h x y _ _ xy; have := max_card [set x; y]; rewrite cards2 xy h. Qed.

(** g(1) = 1, with no convention on empty cliques: a graph on one vertex has the one maximal clique [set: G]. *)
Lemma g260_number_1 : x260_clique_size_number 1 1.
Proof.
split; first by exists 'K_1; split; [rewrite card_ord | exact: g260_count_Kn].
move=> G hG; rewrite /x260_clique_size_count.
apply: leq_trans (subset_leq_card (_ : _ \subset [set inord 1])) _; last by rewrite cards1.
apply/subsetP => k; rewrite !inE => /existsP [S /andP [mS /eqP hk]].
have SE : S = setT := g260_clique_setT (g260_clique_one hG) mS.
by apply/eqP/val_inj; rewrite /= -hk SE cardsT hG inordK // hG.
Qed.


Local Notation o0 := (@Ordinal 3 0 isT).
Local Notation o1 := (@Ordinal 3 1 isT).
Local Notation o2 := (@Ordinal 3 2 isT).

Lemma g260_I3_cases (x : 'I_3) : [\/ x = o0, x = o1 | x = o2].
Proof.
case: x => [[|[|[|//]]] hx]; [apply: Or31 | apply: Or32 | apply: Or33]; exact: val_inj.
Qed.

(** A vertex beside an edge: vertex 0 isolated, the edge 1 -- 2. *)
Definition g260_ve_rel (x y : 'I_3) : bool := [&& x != y, val x != 0 & val y != 0].

Lemma g260_ve_sym : symmetric g260_ve_rel.
Proof. by move=> x y; rewrite /g260_ve_rel eq_sym [(val x != 0) && _]andbC. Qed.

Lemma g260_ve_irrefl : irreflexive g260_ve_rel.
Proof. by move=> x; rewrite /g260_ve_rel eqxx. Qed.

Definition g260_ve : sgraph := SGraph g260_ve_sym g260_ve_irrefl.

Lemma g260_ve_adj (x y : g260_ve) : x -- y = [&& x != y, val x != 0 & val y != 0].
Proof. by []. Qed.

Lemma g260_ve_clique12 : clique ([set o1; o2] : {set g260_ve}).
Proof.
move=> x y; rewrite !inE g260_ve_adj => /orP [] /eqP -> /orP [] /eqP -> //.
Qed.

Lemma g260_ve_max0 : maximal_clique ([set o0] : {set g260_ve}).
Proof.
apply/maximal_cliqueP; split; first by move=> x y; rewrite !inE => /eqP -> /eqP ->; rewrite eqxx.
move=> T /properP [/subsetP sT [v vT]]; rewrite inE => nv cT.
have := cT o0 v (sT o0 (set11 _)) vT; rewrite eq_sym nv g260_ve_adj => /(_ isT).
by rewrite eq_sym nv.
Qed.

Lemma g260_ve_max12 : maximal_clique ([set o1; o2] : {set g260_ve}).
Proof.
apply/maximal_cliqueP; split; first exact: g260_ve_clique12.
move=> T /properP [/subsetP sT [v vT]]; rewrite !inE => nv cT.
have [v0|v1|v2] := g260_I3_cases v; last 2 first.
- by rewrite v1 eqxx in nv.
- by rewrite v2 eqxx orbT in nv.
have := cT o1 v (sT o1 (setU11 _ _)) vT; rewrite v0 g260_ve_adj => /(_ isT).
by [].
Qed.

Lemma g260_ve_maximal (S : {set g260_ve}) :
  maximal_clique S -> (S == [set o0]) || (S == [set o1; o2]).
Proof.
move=> mS; have [cS hS] := maximal_cliqueP _ mS.
case: (boolP (o0 \in S)) => [h0|n0].
  apply/orP; left; rewrite eqEsubset sub1set h0 andbT; apply/subsetP => v vS.
  rewrite inE; apply: contraT => nv.
  by have := cS o0 v h0 vS; rewrite eq_sym nv g260_ve_adj eq_sym nv => /(_ isT).
apply/orP; right; have sub : S \subset [set o1; o2].
  apply/subsetP => v vS; rewrite !inE.
  by have [v0|->|->] := g260_I3_cases v; rewrite ?eqxx ?orbT //; rewrite -v0 vS in n0.
rewrite eqEsubset sub /=; apply: contraT => nsub.
by case: (hS [set o1; o2]); [rewrite properE sub | exact: g260_ve_clique12].
Qed.

Lemma g260_count_ve : x260_clique_size_count g260_ve = 2.
Proof.
rewrite /x260_clique_size_count.
have c3 : #|g260_ve| = 3 by rewrite card_ord.
have -> : [set k : 'I_#|g260_ve|.+1 | [exists S : {set g260_ve}, maximal_clique S && (#|S| == k)]] =
          [set inord 1; inord 2].
  apply/setP => k; rewrite !inE; apply/existsP/idP => [[S /andP [mS /eqP hk]]|].
    have := g260_ve_maximal mS; case/orP => /eqP SE; subst S; rewrite ?cards1 ?cards2 in hk.
      by apply/orP; left; apply/eqP/val_inj; rewrite /= -hk inordK // c3.
    by apply/orP; right; apply/eqP/val_inj; rewrite /= -hk inordK // c3.
  case/orP => /eqP ->; [exists [set o0] | exists [set o1; o2]].
    by rewrite g260_ve_max0 cards1 inordK // c3.
  by rewrite g260_ve_max12 cards2 inordK // c3.
rewrite cards2; suff -> : (inord 1 != inord 2 :> 'I_#|g260_ve|.+1) by [].
by apply/negP => /eqP/(congr1 val); rewrite /= !inordK // c3.
Qed.


(** ** Facts used below ********************************************************* *)

Lemma g260_code_single n (H : sgraph) (A : {set {set 'K_n}}) : A \subset E('K_n) -> x260_code H [set A].
Proof.
move=> sA; split=> [B|B C]; rewrite !inE => /eqP->; first by [].
by move=> /eqP->; rewrite eqxx.
Qed.

Lemma g260_card_graphs n : #|powerset E('K_n)| = 2 ^ 'C(n, 2).
Proof. by rewrite card_powerset -edge_count_Kn. Qed.

Lemma g260_edge_count_K4 : edge_count 'K_4 = 6.
Proof. by rewrite edge_count_Kn. Qed.

(** ** helper_sanity ************************************************************* *)

Definition g260_cs_helper_claim : Prop :=
  [/\ x260_clique_size_count g260_ve = 2, x260_clique_size_count 'K_3 = 1, x260_clique_size_number 1 1,
      x260_log_star 4 = 3 & x260_log_star 16 = 4].

Theorem g260_cs_helper_sanity : g260_cs_helper_claim.
Proof.
split; [exact: g260_count_ve | exact: g260_count_K3 | exact: g260_number_1 | by vm_compute | by vm_compute].
Qed.

Definition g260_code_helper_claim : Prop :=
  [/\ x260_copy 'K_2 E('K_2), ~ @x260_copy 2 'K_2 set0, @x260_code 2 'K_2 [set set0],
      ~ x260_code 'K_2 [set set0; E('K_2)] &
      forall F : {set {set {set 'K_2}}}, x260_code 'K_2 F -> 2 * #|F| <= 2 ^ 'C(2, 2)].

Theorem g260_code_helper_sanity : g260_code_helper_claim.
Proof.
split; [exact: g260_copy_K2 | exact: g260_not_copy_K2 | exact: g260_code_K2 | exact: g260_not_code_K2 |].
exact: g260_code_K2_le.
Qed.

(** ** erdos:927 ****************************************************************** *)

(** hyp_inhabited: g(1) = 1, and the statement then gives the lower half of its clause. *)
Definition g260_cs_hyp_claim : Prop :=
  x260_clique_size_number 1 1 /\
  (maximal_clique_sizes_statement ->
     exists C N : nat, forall n a : nat, N <= n -> x260_clique_size_number n a ->
       n <= a + trunc_log 2 n + x260_log_star n + C).

Theorem g260_cs_hyp_inhabited : g260_cs_hyp_claim.
Proof.
split; first exact: g260_number_1.
by case=> C [N h]; exists C, N => n a hn ha; exact: (proj1 (h n a hn ha)).
Qed.

(** not_trivially_true: without g(n) = a, a = N + C + 1 breaks the upper half at n = N. *)
Definition g260_cs_no_number : Prop :=
  exists C N : nat, forall n a : nat, N <= n ->
    n <= a + trunc_log 2 n + x260_log_star n + C /\ a + trunc_log 2 n + x260_log_star n <= n + C.

Definition g260_cs_ntt_claim : Prop :=
  ~ g260_cs_no_number /\ (g260_cs_no_number -> maximal_clique_sizes_statement).

Theorem g260_cs_not_trivially_true : g260_cs_ntt_claim.
Proof.
split; last by case=> C [N h]; exists C, N => n a hn _; exact: h.
case=> C [N /(_ N (N + C + 1) (leqnn N))] [_].
by rewrite -!addnA leq_add2l -[X in _ <= X]addn0 leq_add2l.
Qed.

(** ** arxiv:2301.13305#00 ********************************************************* *)

(** hyp_inhabited: H = K_4 meets both guards (6 edges), [set set0] is a K_4-code on [4], and the statement then gives
    its conclusion at H = K_4, q = 2. *)
Definition g260_code_even_hyp_claim : Prop :=
  [/\ 0 < edge_count ('K_4), ~~ odd (edge_count ('K_4)), x260_code 'K_4 ([set set0] : {set {set {set 'K_4}}}) &
      (graph_codes_even_edges_statement ->
         exists N : nat, forall n : nat, N <= n ->
           forall F : {set {set {set 'K_n}}}, x260_code 'K_4 F -> 2 * #|F| <= 2 ^ 'C(n, 2))].

Theorem g260_code_even_hyp_inhabited : g260_code_even_hyp_claim.
Proof.
rewrite /g260_code_even_hyp_claim g260_edge_count_K4; split=> //; first exact/g260_code_single/sub0set.
by move=> h; apply: h; rewrite ?g260_edge_count_K4.
Qed.

(** not_trivially_true: without the code hypothesis, all 2^C(n,2) graphs on [n] break the bound at H = K_4, q = 2. *)
Definition g260_code_even_no_code : Prop :=
  forall H : sgraph, 0 < edge_count H -> ~~ odd (edge_count H) ->
    forall q : nat, 1 <= q -> exists N : nat, forall n : nat, N <= n ->
      forall F : {set {set {set 'K_n}}}, q * #|F| <= 2 ^ 'C(n, 2).

Definition g260_code_even_ntt_claim : Prop :=
  ~ g260_code_even_no_code /\ (g260_code_even_no_code -> graph_codes_even_edges_statement).

Theorem g260_code_even_not_trivially_true : g260_code_even_ntt_claim.
Proof.
split; last by move=> h H h0 h1 q hq; have [N hN] := h H h0 h1 q hq; exists N => n hn F _; exact: hN.
move=> /(_ 'K_4); rewrite g260_edge_count_K4 => /(_ isT isT 2 isT) [N /(_ N (leqnn N) (powerset E('K_N)))].
by rewrite g260_card_graphs -[X in _ <= X]mul1n leq_pmul2r ?expn_gt0.
Qed.

(** ** arxiv:2301.13305#01 ********************************************************* *)

(** hyp_inhabited: [set set0] is a K_4-code on [4], and the statement then gives its conclusion at q = 2. *)
Definition g260_code_K4_hyp_claim : Prop :=
  x260_code 'K_4 ([set set0] : {set {set {set 'K_4}}}) /\
  (graph_codes_K4_statement ->
     exists N : nat, forall n : nat, N <= n ->
       forall F : {set {set {set 'K_n}}}, x260_code 'K_4 F -> 2 * #|F| <= 2 ^ 'C(n, 2)).

Theorem g260_code_K4_hyp_inhabited : g260_code_K4_hyp_claim.
Proof. by split; [exact/g260_code_single/sub0set | move=> h; exact: h]. Qed.

(** not_trivially_true: without the code hypothesis, all 2^C(n,2) graphs on [n] break the bound at q = 2. *)
Definition g260_code_K4_no_code : Prop :=
  forall q : nat, 1 <= q -> exists N : nat, forall n : nat, N <= n ->
    forall F : {set {set {set 'K_n}}}, q * #|F| <= 2 ^ 'C(n, 2).

Definition g260_code_K4_ntt_claim : Prop :=
  ~ g260_code_K4_no_code /\ (g260_code_K4_no_code -> graph_codes_K4_statement).

Theorem g260_code_K4_not_trivially_true : g260_code_K4_ntt_claim.
Proof.
split; last by move=> h q hq; have [N hN] := h q hq; exists N => n hn F _; exact: hN.
move=> /(_ 2 isT) [N /(_ N (leqnn N) (powerset E('K_N)))].
by rewrite g260_card_graphs -[X in _ <= X]mul1n leq_pmul2r ?expn_gt0.
Qed.

Print Assumptions g260_number_0.
Print Assumptions g260_cs_helper_sanity.
Print Assumptions g260_code_helper_sanity.
Print Assumptions g260_cs_hyp_inhabited.
Print Assumptions g260_cs_not_trivially_true.
Print Assumptions g260_code_even_hyp_inhabited.
Print Assumptions g260_code_even_not_trivially_true.
Print Assumptions g260_code_K4_hyp_inhabited.
Print Assumptions g260_code_K4_not_trivially_true.

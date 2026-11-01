(** * Chromatic.conjectures.grounding_X275 -- grounding certificates for wave X275 (2026-11-01)

    For each of the two rows: hyp_inhabited (the hypotheses hold at a small instance, and the statement then gives
    its conclusion there) and not_trivially_true (a variant is false and implies the statement).  X275.v has no local
    helper, so there is no helper_sanity certificate.
    - arxiv:2507.04254#00: K_1 is a 0_k-graph for every k, and the statement at m = 1 colours it with at most 2k
      colours for every large k.  The variant with fewer than k colours (q < k in place of m q <= (m + 1) k) is
      strictly stronger and false: K_(k+1) is a 0_k-graph, and for k >= 2 a colour class at a vertex of degree k has
      one edge or more than k, so the k edges at a vertex take k distinct colours.  The variant strengthens the
      conclusion (as X274's linear arboricity certificate does): without the 0_k hypothesis the row would follow from
      the Botler-Colucci-Kohayakawa conjecture (the X100 row, open), so dropping it is not known to give a false row.
    - studies:std_yao_zhou_conjecture_on_the_edge_density_of_4_cri: K_4 is planar and 4-critical, and the statement
      gives 4-critical planar graphs of every large order with density at least 7/3 - eps.  The variant whose upper
      clause ranges over all graphs (planarity and criticality dropped there) is strictly stronger and false: K_n
      has 'C(n, 2) edges, so 3 |E| > 10 |V| (eps = 1) once n >= 8. *)

From GTBase Require Import base common colourings.
From Chromatic.conjectures Require Import X100 X258 X275.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Small graphs ******************************************************************************* *)

Lemma g275_planar_small (G : sgraph) : #|G| <= 4 -> wagner_planar G.
Proof.
move=> le4; split=> m; move: (leq_trans (minor_card m) le4).
- by rewrite card_ord.
- by rewrite card_sum !card_ord.
Qed.

Lemma g275_N_Kn (n : nat) (v : 'K_n.+1) : #|N(v)| = n.
Proof.
have -> : N(v) = [set~ v] by apply/setP => w; rewrite !inE /edge_rel /= eq_sym.
by rewrite cardsC1 card_ord.
Qed.

(** A non-adjacent pair of distinct vertices shares a colour: chi < #|G| (grounding_X258's argument). *)
Lemma g275_chi_lt_nonedge (G : sgraph) (x y : G) : x != y -> ~~ x -- y -> χ([set: G]) < #|G|.
Proof.
move=> xy nxy; have st : stable [set x; y].
  apply/stableP => u v; rewrite !inE => /orP[] /eqP-> /orP[] /eqP->;
  by rewrite ?sg_irrefl ?(negbTE nxy) // sg_sym (negbTE nxy).
apply: leq_ltn_trans (chiD1 [set: G] st) _.
have := leq_chi ([set: G] :\: [set x; y]); rewrite cardsDS ?subsetT // cards2 xy cardsT => h2.
have n2 : 2 <= #|G| by have := subset_leq_card (subsetT [set x; y]); rewrite cards2 xy cardsT.
apply: leq_ltn_trans (_ : (#|G| - 2).+1 < #|G|); first by rewrite ltnS.
by move: n2; case: #|G| => [|[|n]] // _; rewrite !subSS subn0 ltnS.
Qed.

Lemma g275_chi_K (n : nat) : χ([set: 'K_n]) = n.
Proof. by rewrite chi_clique ?cardsT ?card_ord // => x y _ _ xy. Qed.

(** Every graph is edge-critical at k = #|G|: deleting an edge leaves a non-adjacent pair. *)
Lemma g275_edge_critical_order (G : sgraph) : x258_edge_critical G #|G|.
Proof.
move=> u v uv; have uv' : u != v by rewrite (sg_edgeNeq uv).
apply: (@g275_chi_lt_nonedge (del_edges [set u; v]) u v uv').
by rewrite /edge_rel /= subxx andbF.
Qed.

(** ** arxiv:2507.04254#00 *********************************************************************** *)

(** The edges of K_(k+1) at a vertex take distinct colours in a mod k colouring (k >= 2): two of them sharing a
    colour c would give c a degree between 2 and k at that vertex, which is not 1 modulo k. *)
Lemma g275_Kn_modular (k q : nat) : 2 <= k -> x100_modular_edge_colourable 'K_k.+1 k q -> k <= q.
Proof.
move=> k2 [col hc].
pose v : 'K_k.+1 := ord0.
pose f (i : 'I_k) : 'I_q := col [set v; lift v i].
suff inj : injective f by have := leq_card f inj; rewrite !card_ord.
move=> i j fij; case: (eqVneq i j) => // nij; exfalso.
pose c := f i.
pose A := [set e in E('K_k.+1) | (v \in e) && (col e == c)].
have degA : x100_col_deg col v c = #|A| by rewrite /x100_col_deg /x100_edge_set sum1dep_card.
have inA : forall x : 'I_k, f x = c -> [set v; lift v x] \in A.
  move=> x fx; rewrite inE in_edges; apply/and3P; split; last by apply/eqP.
  - by rewrite /edge_rel /=.
  - by rewrite set21.
have neA : [set v; lift v i] != [set v; lift v j].
  apply/negP => /eqP eij.
  have : lift v i \in [set v; lift v j] by rewrite -eij set22.
  rewrite !inE (inj_eq (@lift_inj _ v)) (negbTE nij) orbF => /eqP liv.
  by have := neq_lift v i; rewrite liv eqxx.
have two : 1 < #|A|.
  apply/card_gt1P; exists [set v; lift v i], [set v; lift v j].
  by split; [exact: inA | apply: inA; rewrite -fij | exact: neA].
have sub : A \subset [set [set v; lift v x] | x : 'I_k].
  apply/subsetP => e; rewrite inE => /and3P [/edgesP [x [y [-> xy]]] ve _].
  have oth : forall u : ('K_k.+1), u != v -> [set v; u] \in [set [set v; lift v x0] | x0 : 'I_k].
    move=> u uv; have vu : v != u by rewrite eq_sym.
    have [x' lx _] := unlift_some vu.
    by apply/imsetP; exists x'; rewrite // lx.
  move: ve; rewrite !inE => /orP [/eqP vx | /eqP vy].
  - by rewrite -vx; apply: oth; rewrite vx eq_sym (sg_edgeNeq xy).
  - have -> : [set x; y] = [set y; x] by apply/setP => z; rewrite !inE orbC.
    by rewrite -vy; apply: oth; rewrite vy (sg_edgeNeq xy).
have le : #|A| <= k.
  apply: leq_trans (subset_leq_card sub) _.
  by apply: leq_trans (leq_imset_card _ _) _; rewrite card_ord.
have := hc v c; rewrite degA => -[A0 | Ak]; first by rewrite A0 in two.
move: le; rewrite leq_eqVlt => /orP [/eqP Aeq | Alt]; first by move: Ak; rewrite Aeq modnn.
by move: Ak; rewrite modn_small // => A1; rewrite A1 in two.
Qed.

(** hyp_inhabited: K_1 is a 0_k-graph for every k; at m = 1 the statement colours it with at most 2k colours for
    every large k. *)
Definition g275_mod_hyp_claim : Prop :=
  (forall (k : nat) (v : 'K_1), k %| #|N(v)|) /\
  (modular_edge_colouring_zero_mod_k_graphs_k_plus_little_o_statement ->
     exists k0 : nat, forall k : nat, k0 <= k ->
       exists q : nat, q <= 2 * k /\ x100_modular_edge_colourable 'K_1 k q).

Theorem g275_mod_hyp_inhabited : g275_mod_hyp_claim.
Proof.
have z : forall (k : nat) (v : 'K_1), k %| #|N(v)| by move=> k v; rewrite g275_N_Kn dvdn0.
split=> // /(_ 1 isT) [k0 h]; exists k0 => k kk.
by have [q [hq col]] := h k kk _ (z k); exists q; rewrite mul1n in hq.
Qed.

(** not_trivially_true: fewer than k colours is false at K_(k+1), a 0_k-graph, for every k >= 2. *)
Definition g275_mod_below_k : Prop :=
  forall m : nat, 0 < m ->
    exists k0 : nat, forall k : nat, k0 <= k ->
      forall G : sgraph, (forall v : G, k %| #|N(v)|) ->
        exists q : nat, q < k /\ x100_modular_edge_colourable G k q.

Definition g275_mod_ntt_claim : Prop :=
  ~ g275_mod_below_k /\
  (g275_mod_below_k -> modular_edge_colouring_zero_mod_k_graphs_k_plus_little_o_statement).

Theorem g275_mod_not_trivially_true : g275_mod_ntt_claim.
Proof.
split.
- move=> /(_ 1 isT) [k0 h].
  have kk : k0 <= k0 + 2 by rewrite leq_addr.
  pose k := k0 + 2.
  have zk : forall v : ('K_k.+1), k %| #|N(v)| by move=> v; rewrite g275_N_Kn dvdnn.
  have [q [qk col]] := h k kk ('K_k.+1) zk.
  have := g275_Kn_modular (leq_addl k0 2) col.
  by rewrite leqNgt qk.
- move=> h m m0; have [k0 hk] := h m m0; exists k0 => k kk G zk.
  have [q [qk col]] := hk k kk G zk; exists q; split=> //.
  apply: leq_trans (leq_mul (leqnn m) (ltnW qk)) _.
  by rewrite mulnDl mul1n leq_addr.
Qed.

(** ** studies:std_yao_zhou_conjecture_on_the_edge_density_of_4_cri ****************************** *)

(** hyp_inhabited: K_4 is planar and 4-critical; the statement gives 4-critical planar graphs of every large order
    with density at least 7/3 - p / q. *)
Definition g275_yz_hyp_claim : Prop :=
  [/\ wagner_planar ('K_4), χ([set: 'K_4]) = 4, x258_edge_critical ('K_4) 4 &
      (yao_zhou_four_critical_planar_edge_density_limsup_seven_thirds_statement ->
         forall p q n0 : nat, 0 < p -> 0 < q ->
           exists G : sgraph, [/\ n0 <= #|G|, wagner_planar G, χ([set: G]) = 4, x258_edge_critical G 4 &
                                  7 * q * #|G| <= 3 * q * #|E(G)| + 3 * p * #|G|])].

Theorem g275_yz_hyp_inhabited : g275_yz_hyp_claim.
Proof.
split.
- by apply: g275_planar_small; rewrite card_ord.
- exact: g275_chi_K.
- by have := @g275_edge_critical_order ('K_4); rewrite card_ord.
- by move=> h p q n0 p0 q0; have [_ low] := h p q p0 q0; exact: low.
Qed.

(** The edge density of K_n exceeds 10/3 from n = 8 on. *)
Lemma g275_dense_K (n : nat) : 8 <= n -> 10 * n < 3 * #|E(('K_n))|.
Proof.
move=> n8; rewrite card_edge_Kn.
have e : ('C(n, 2)).*2 = n * n.-1 by rewrite bin2 halfK oddM; case: n n8 => [|n'] // _; rewrite /= andNb subn0.
have n0 : 0 < n by apply: leq_trans n8.
rewrite -(ltn_pmul2l (_ : 0 < 2)) // [2 * (3 * _)]mulnCA [2 * 'C(_, 2)]mul2n e.
rewrite mulnA (mulnCA 3 n) [_ * n]mulnC ltn_pmul2l //.
have m7 : 7 <= n.-1 by rewrite -ltnS prednK.
by apply: leq_trans (leq_mul (leqnn 3) m7).
Qed.

(** not_trivially_true: with its upper clause over all graphs, the statement is false (K_n, n >= 8, at eps = 1). *)
Definition g275_yz_all_graphs : Prop :=
  forall p q : nat, 0 < p -> 0 < q ->
    (exists n0 : nat, forall G : sgraph, n0 <= #|G| -> 3 * q * #|E(G)| <= (7 * q + 3 * p) * #|G|) /\
    (forall n0 : nat, exists G : sgraph,
       [/\ n0 <= #|G|, wagner_planar G, χ([set: G]) = 4, x258_edge_critical G 4 &
           7 * q * #|G| <= 3 * q * #|E(G)| + 3 * p * #|G|]).

Definition g275_yz_ntt_claim : Prop :=
  ~ g275_yz_all_graphs /\
  (g275_yz_all_graphs -> yao_zhou_four_critical_planar_edge_density_limsup_seven_thirds_statement).

Theorem g275_yz_not_trivially_true : g275_yz_ntt_claim.
Proof.
split.
- move=> /(_ 1 1 isT isT) [[n0 up] _].
  have n8 : 8 <= n0 + 8 by rewrite leq_addl.
  have hn : n0 <= #|('K_(n0 + 8))| by rewrite card_ord leq_addr.
  have := up _ hn.
  by rewrite card_ord leqNgt muln1 (g275_dense_K n8).
- move=> h p q p0 q0; have [[n0 up] low] := h p q p0 q0; split=> //.
  by exists n0 => G nG _ _ _; exact: up.
Qed.

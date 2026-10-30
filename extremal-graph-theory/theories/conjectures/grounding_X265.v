(** * Extremal.conjectures.grounding_X265 -- grounding certificates of wave X265.

    For each of the two rows: hyp_inhabited (the hypotheses hold on concrete instances) and not_trivially_true in
    the contract form of meta/EXPANSION_PLAN.md 4.4 (a variant obtained from the body by deleting one hypothesis is
    false and implies the row): erdos:1077 without its edge-count hypothesis (the edgeless graph on N + 1 vertices
    has no subgraph with m > n^(1 - alpha) vertices and at least eps m^(1 + alpha) edges); arXiv:2004.10180#00
    without the hypothesis that G - F is triangle-free (F = set0 then breaks the bound at C = 0).  The instances:
    K_n for every n >= 6 has at least n^(3/2) edges (n^3 <= C(n, 2)^2), so the hypothesis of erdos:1077 at
    alpha = 1/2 holds for every size, and K_n itself is a 1-balanced subgraph meeting the conclusion at eps = 1;
    the edgeless graph on N vertices is C_5-free for every N, deleting all edges always leaves a triangle-free
    graph, K_3 is C_5-free with every triangle-destroying F non-empty, and the statement yields for every N a
    C_5-free graph on at least N vertices that is not triangle-free (q = 1, C = 0, F = set0).  No local helper
    (helper_sanity empty). *)

From Extremal.conjectures Require Import X265.
From GTBase Require Import base common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Edgeless graphs, C_5 and K_3 ************************************************ *)

(** The edgeless graph on N vertices: K_N with every edge deleted. *)
Definition g265_edgeless (N : nat) : sgraph := del_edge_set 'K_N E('K_N).

Lemma g265_edgeless_card (N : nat) : #|g265_edgeless N| = N.
Proof. by rewrite card_del_edge_set card_ord. Qed.

Lemma g265_edgeless_noedge (N : nat) (x y : g265_edgeless N) : ~~ x -- y.
Proof. exact: del_edge_setT. Qed.

(** A subgraph of an edgeless host has no edge. *)
Lemma g265_sub_edgeless (G H : sgraph) :
  (forall x y : G, ~~ x -- y) -> has_subgraph G H -> edge_count H = 0.
Proof.
move=> h /has_subgraphP [f [_ hf]]; apply/eqP; rewrite /edge_count cards_eq0; apply/eqP/setP => e.
rewrite in_set0; apply/negP => /edgesP [x [y [_ xy]]].
by move: (h (f x) (f y)); rewrite hf.
Qed.

(** C_5 has an edge, so an edgeless host contains no C_5. *)
Lemma g265_c5_edge : @edge_rel (cycle_graph 5) ord0 (@Ordinal 5 1 isT).
Proof. by []. Qed.

Lemma g265_edgeless_c5_free (G : sgraph) :
  (forall x y : G, ~~ x -- y) -> ~ has_subgraph G (cycle_graph 5).
Proof.
move=> h /has_subgraphP [f [_ hf]].
by move: (h (f ord0) (f (@Ordinal 5 1 isT))); rewrite (hf _ _ g265_c5_edge).
Qed.

(** K_3 is C_5-free (too few vertices). *)
Lemma g265_K3_c5_free : ~ has_subgraph 'K_3 (cycle_graph 5).
Proof. by move/has_subgraph_card; rewrite !card_ord. Qed.

(** Deleting every edge leaves a triangle-free graph; K_3 itself is not triangle-free. *)
Lemma g265_del_all_triangle_free (G : sgraph) : triangle_free (del_edge_set G E(G)).
Proof. by move=> x y z; move/negP: (@del_edge_setT G x y). Qed.

Lemma g265_K3_not_triangle_free : ~ triangle_free (del_edge_set 'K_3 set0).
Proof.
move=> h; apply: (h ord0 (@Ordinal 3 1 isT) ord_max); rewrite del_edge_setE in_set0 andbT //.
Qed.

(** Deleting nothing keeps a triangle-free graph triangle-free. *)
Lemma g265_del0_triangle_free (G : sgraph) : triangle_free G -> triangle_free (del_edge_set G set0).
Proof. by move=> tf x y z; rewrite !(@del_edge_setE G) !in_set0 !andbT; exact: tf. Qed.

(** Every F that makes K_3 triangle-free is non-empty. *)
Lemma g265_K3_F_nonempty (F : {set {set 'K_3}}) :
  triangle_free (del_edge_set 'K_3 F) -> 0 < #|F|.
Proof.
rewrite card_gt0; apply: contraPneq => ->; exact: g265_K3_not_triangle_free.
Qed.

(** ** Complete graphs: degrees and edges ****************************************** *)

Lemma g265_Delta_Kn (n : nat) : Delta 'K_n.+1 <= n.
Proof.
apply/bigmax_leqP => x _; have : #|N(x)| < #|[set: 'K_n.+1]|.
  apply: proper_card; apply/properP; split; [exact: subsetT | exists x; rewrite ?inE ?in_opn ?sg_irrefl //].
by rewrite cardsT card_ord ltnS.
Qed.

Lemma g265_Kn_bin2 (n : nat) : 'C(n, 2).*2 = n * n.-1.
Proof. by case: n => [//|m]; rewrite bin2 halfK oddM /= andNb subn0. Qed.

(** For n >= 6, K_n has at least n^(3/2) edges: n^3 <= C(n, 2)^2. *)
Lemma g265_Kn_hyp (n : nat) : 6 <= n -> #|'K_n| ^ (2 + 1) <= edge_count 'K_n ^ 2.
Proof.
move=> n6; rewrite card_ord edge_count_Kn -(leq_pmul2l (isT : 0 < 4)).
have -> : 4 * 'C(n, 2) ^ 2 = (n * n.-1) ^ 2 by rewrite -g265_Kn_bin2 -mul2n expnMn mulnC.
rewrite expnMn (_ : 2 + 1 = 1 + 2) // expnD expn1 mulnA mulnC leq_mul2l.
case: n n6 => [//|m] /=; rewrite ltnS => m5.
rewrite mulnS (expnS m 1) expn1; apply: leq_trans (_ : m + 4 * m <= m * m).
  by rewrite leq_add2r ltnW.
by rewrite -mulSn leq_mul2r m5 orbT.
Qed.

(** ** erdos:1077 ********************************************************************* *)

Definition g265_bd_hyp_claim : Prop :=
  [/\ forall n : nat, 6 <= n -> #|'K_n| ^ (2 + 1) <= edge_count 'K_n ^ 2,
      forall n : nat, 6 <= n ->
        [/\ has_subgraph ('K_n) ('K_n), #|'K_n| ^ (2 - 1) < #|'K_n| ^ 2,
            (exists d : nat, min_degree ('K_n) d /\ Delta ('K_n) <= 1 * d) &
            1 ^ 2 * #|'K_n| ^ (2 + 1) <= (1 * edge_count ('K_n)) ^ 2] &
      (balanced_dense_subgraph_statement ->
         exists N : nat, forall n : nat, N <= n -> 6 <= n ->
           exists H : sgraph, has_subgraph ('K_n) H /\ #|'K_n| < #|H| ^ 2)].

Theorem g265_bd_hyp_inhabited : g265_bd_hyp_claim.
Proof.
split; first exact: g265_Kn_hyp.
- case=> [//|m] m6; split; first exact: has_subgraph_refl.
  + by rewrite card_ord expn1 -[X in X < _]expn1 ltn_exp2l // (leq_trans _ m6).
  + by exists m; split; [exact: min_degree_Kn | rewrite mul1n; exact: g265_Delta_Kn].
  + by rewrite exp1n !mul1n; exact: g265_Kn_hyp.
- move=> h; have [D [N hN]] := h 1 2 1 1 isT isT isT; exists N => n hn n6.
  have hK : N <= #|'K_n| by rewrite card_ord.
  have [H [hs hc _ _]] := hN 'K_n hK (g265_Kn_hyp n6).
  by exists H; split => //; move: hc; rewrite expn1.
Qed.

(** The statement without its edge-count hypothesis. *)
Definition g265_bd_no_edges : Prop :=
  forall a b r p : nat, 0 < a < b -> 1 <= r -> 1 <= p -> exists D N : nat,
    forall G : sgraph, N <= #|G| ->
      exists H : sgraph, [/\ has_subgraph G H, #|G| ^ (b - a) < #|H| ^ b,
        (exists d : nat, min_degree H d /\ Delta H <= D * d) &
        r ^ b * #|H| ^ (b + a) <= (p * edge_count H) ^ b].

Definition g265_bd_ntt_claim : Prop :=
  ~ g265_bd_no_edges /\ (g265_bd_no_edges -> balanced_dense_subgraph_statement).

Theorem g265_bd_not_trivially_true : g265_bd_ntt_claim.
Proof.
split.
- move=> h; have [D [N hN]] := h 1 2 1 1 isT isT isT.
  have hE : N <= #|g265_edgeless N.+1| by rewrite g265_edgeless_card.
  have [H [hs hc _ he]] := hN (g265_edgeless N.+1) hE.
  move: he; rewrite (g265_sub_edgeless (@g265_edgeless_noedge N.+1) hs) muln0 exp1n mul1n.
  rewrite leqn0 expn_eq0 => /andP [/eqP H0 _]; move: hc; rewrite H0 g265_edgeless_card.
  by [].
- move=> h a b r p ab r1 p1; have [D [N hN]] := h a b r p ab r1 p1; exists D, N => G hG _.
  exact: hN G hG.
Qed.

(** ** arXiv:2004.10180#00 ************************************************************ *)

Definition g265_c5_hyp_claim : Prop :=
  [/\ forall N : nat, N <= #|g265_edgeless N| /\ ~ has_subgraph (g265_edgeless N) (cycle_graph 5),
      forall G : sgraph, E(G) \subset E(G) /\ triangle_free (del_edge_set G E(G)),
      ~ has_subgraph 'K_3 (cycle_graph 5),
      forall F : {set {set 'K_3}}, F \subset E('K_3) -> triangle_free (del_edge_set 'K_3 F) -> 0 < #|F| &
      (c5_free_triangle_deletion_exponent_statement ->
         forall N : nat, exists G : sgraph, [/\ N <= #|G|, ~ has_subgraph G (cycle_graph 5) & ~ triangle_free G])].

Theorem g265_c5_hyp_inhabited : g265_c5_hyp_claim.
Proof.
split.
- move=> N; split; first by rewrite g265_edgeless_card.
  exact: g265_edgeless_c5_free (@g265_edgeless_noedge N).
- by move=> G; split; [exact: subxx | exact: g265_del_all_triangle_free].
- exact: g265_K3_c5_free.
- by move=> F _; exact: g265_K3_F_nonempty.
- move=> h N; have [G [hN hc hF]] := h 1 0 N isT; exists G; split => // tf.
  by move: (hF set0 (sub0set _) (g265_del0_triangle_free tf)); rewrite cards0 mul0n.
Qed.

(** The statement without its hypothesis that G - F is triangle-free. *)
Definition g265_c5_no_tf : Prop :=
  forall q C N : nat, 1 <= q -> exists G : sgraph,
    [/\ N <= #|G|, ~ has_subgraph G (cycle_graph 5) &
      forall F : {set {set G}}, F \subset E(G) -> C * #|G| ^ (3 * q - 2) < #|F| ^ (2 * q)].

Definition g265_c5_ntt_claim : Prop :=
  ~ g265_c5_no_tf /\ (g265_c5_no_tf -> c5_free_triangle_deletion_exponent_statement).

Theorem g265_c5_not_trivially_true : g265_c5_ntt_claim.
Proof.
split.
- move=> h; have [G [_ _ hF]] := h 1 0 0 isT.
  by move: (hF set0 (sub0set _)); rewrite cards0 mul0n.
- move=> h q C N q1; have [G [hN hc hF]] := h q C N q1; exists G; split => // F hFE _.
  exact: hF.
Qed.

Print Assumptions g265_bd_hyp_inhabited.
Print Assumptions g265_bd_not_trivially_true.
Print Assumptions g265_c5_hyp_inhabited.
Print Assumptions g265_c5_not_trivially_true.

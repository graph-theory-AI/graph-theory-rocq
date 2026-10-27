(** * Extremal.conjectures.grounding_X243 -- grounding certificates of wave X243.

    For each of the six rows: hyp_inhabited (the hypotheses hold on a concrete instance, and the statement then
    yields its conclusion there) and not_trivially_true in the contract form of meta/EXPANSION_PLAN.md 4.4 (the row
    with a load-bearing hypothesis dropped is false, and that variant implies the row): the Ramsey hypothesis for
    erdos:88, erdos:636 and erdos:637 (on the edgeless complete_multipartite_graph 1 n: no induced subgraph has one
    edge; at most n + 1 distinct (size, edges) pairs, and (p (n + 1))^2 < n^5 at n = p + 1; a single degree value, so
    n <= p^2 fails at n = p^2 + 1), the density hypothesis for erdos:666 (F = set0 leaves no C_6), the diameter
    hypothesis for erdos:133 (an edgeless graph is triangle-free with every degree 0) and the edge-count hypothesis
    for erdos:1034 (an edgeless graph has no triangle).  The wave has no local helper, so no helper_sanity
    certificate.  Small instances: 'K_2 meets the shared Ramsey hypothesis at C = 3 (every vertex set has at most 2
    vertices, 2^2 < 2^3); Q_1 with F its single edge (1 * 2^1 <= 2 * 1 * 1); the path P_3 (GTBase ordinal_path 3),
    triangle-free with every distance at most 2 (its middle vertex is a common closed neighbour of every pair);
    K_3 with 3^2 < 4 * 3. *)

From Extremal.conjectures Require Import X243.
From GTBase Require Import base common hypercubes graph_metric complete_multipartite_graphs path_graphs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Small instances *)

Lemma g243_edgeless (n : nat) (x y : complete_multipartite_graph 1 n) : ~~ x -- y.
Proof. by rewrite complete_multipartite_edgeE (ord1 x.1) (ord1 y.1) eqxx. Qed.

Lemma g243_K2_ramsey3 : forall S : {set 'K_2}, cliqueb S || stable S -> 2 ^ #|S| < #|'K_2| ^ 3.
Proof.
move=> S _; rewrite card_ord.
apply: (@leq_ltn_trans (2 ^ 2)); last by [].
by rewrite leq_pexp2l //; have := max_card S; rewrite card_ord.
Qed.

Lemma g243_edge_count_edgeless (H : sgraph) : (forall x y : H, ~~ x -- y) -> edge_count H = 0.
Proof.
move=> noE; apply/eqP; rewrite /edge_count cards_eq0; apply/eqP/setP => e; rewrite inE.
by apply/negP => /edgesP [x [y [_ xy]]]; move: (noE x y); rewrite xy.
Qed.

Lemma g243_induced_edgeless (G : sgraph) (S : {set G}) :
  (forall x y : G, ~~ x -- y) -> forall x y : induced S, ~~ x -- y.
Proof. by move=> noE x y; exact: noE. Qed.

(** ** Row erdos:88 *)

Definition g243_mckay_hyp_claim : Prop :=
  [/\ forall S : {set 'K_2}, cliqueb S || stable S -> 2 ^ #|S| < #|'K_2| ^ 3,
      1 * 0 <= #|'K_2| ^ 2 &
      (ramsey_graph_induced_every_edge_count_statement -> exists p : nat, 1 <= p /\
         forall (G : sgraph) (m : nat),
           (forall S : {set G}, cliqueb S || stable S -> 2 ^ #|S| < #|G| ^ 3) ->
           p * m <= #|G| ^ 2 -> exists S : {set G}, edge_count (induced S) = m)].

Theorem g243_mckay_hyp_inhabited : g243_mckay_hyp_claim.
Proof. by split; [exact: g243_K2_ramsey3 | by [] | move=> h; exact: h 3]. Qed.

Definition g243_mckay_no_ramsey : Prop :=
  forall C : nat, exists p : nat, 1 <= p /\
    forall (G : sgraph) (m : nat),
      p * m <= #|G| ^ 2 -> exists S : {set G}, edge_count (induced S) = m.

Definition g243_mckay_ntt_claim : Prop :=
  ~ g243_mckay_no_ramsey /\ (g243_mckay_no_ramsey -> ramsey_graph_induced_every_edge_count_statement).

Theorem g243_mckay_not_trivially_true : g243_mckay_ntt_claim.
Proof.
split.
- move=> h; have [p [p1 hp]] := h 0.
  have [|S] := hp (complete_multipartite_graph 1 p) 1.
    by rewrite card_complete_multipartite_graph mul1n muln1 expnS leq_pmulr // expn1.
  by rewrite (@g243_edge_count_edgeless (induced S) (@g243_induced_edgeless _ S (@g243_edgeless p))).
- by move=> h C; have [p [p1 hp]] := h C; exists p; split => // G m _; exact: hp.
Qed.

(** ** Rows erdos:636 and erdos:637: an edgeless graph has few (size, edges) pairs and one degree value *)

Lemma g243_pairs_edgeless (G : sgraph) : (forall x y : G, ~~ x -- y) ->
  size (undup [seq (#|A|, edge_count (induced A)) | A : {set G} <- enum [set: {set G}]]) <= #|G|.+1.
Proof.
move=> noE; apply: (@leq_trans (size [seq (k, 0) | k <- iota 0 #|G|.+1])); last by rewrite size_map size_iota.
apply: uniq_leq_size; first exact: undup_uniq.
move=> z; rewrite mem_undup => /mapP [A _ ->].
rewrite (@g243_edge_count_edgeless (induced A) (@g243_induced_edgeless _ A noE)).
by apply/mapP; exists #|A| => //; rewrite mem_iota leq0n add0n ltnS max_card.
Qed.

Lemma g243_degrees_edgeless (G : sgraph) (S : {set G}) : (forall x y : G, ~~ x -- y) ->
  size (undup [seq #|N(x)| | x <- enum [set: induced S]]) <= 1.
Proof.
move=> noE; apply: (@leq_trans (size [:: 0])) => //.
apply: uniq_leq_size; first exact: undup_uniq.
move=> z; rewrite mem_undup => /mapP [x _ ->]; rewrite mem_seq1 cards_eq0; apply/eqP/setP => y.
by rewrite !inE; apply/negbTE; exact: (@g243_induced_edgeless _ S noE).
Qed.

Definition g243_pairs_hyp_claim : Prop :=
  [/\ forall S : {set 'K_2}, cliqueb S || stable S -> 2 ^ #|S| < #|'K_2| ^ 3 &
      (ramsey_graph_distinct_size_edge_pairs_statement -> exists p : nat, 1 <= p /\
         forall G : sgraph,
           (forall S : {set G}, cliqueb S || stable S -> 2 ^ #|S| < #|G| ^ 3) ->
           #|G| ^ 5 <=
             (p * size (undup [seq (#|A|, edge_count (induced A)) | A : {set G} <- enum [set: {set G}]])) ^ 2)].

Theorem g243_pairs_hyp_inhabited : g243_pairs_hyp_claim.
Proof. by split; [exact: g243_K2_ramsey3 | move=> h; exact: h 3]. Qed.

Definition g243_pairs_no_ramsey : Prop :=
  forall C : nat, exists p : nat, 1 <= p /\
    forall G : sgraph,
      #|G| ^ 5 <= (p * size (undup [seq (#|A|, edge_count (induced A)) | A : {set G} <- enum [set: {set G}]])) ^ 2.

Definition g243_pairs_ntt_claim : Prop :=
  ~ g243_pairs_no_ramsey /\ (g243_pairs_no_ramsey -> ramsey_graph_distinct_size_edge_pairs_statement).

Theorem g243_pairs_not_trivially_true : g243_pairs_ntt_claim.
Proof.
split; last first.
  by move=> h C; have [p [p1 hp]] := h C; exists p; split => // G _; exact: hp.
move=> h; have [p [p1 hp]] := h 0.
have := hp (complete_multipartite_graph 1 p.+1).
have := g243_pairs_edgeless (@g243_edgeless p.+1).
rewrite card_complete_multipartite_graph mul1n.
set N := size _ => hN h5.
have hpp : p * N <= p.+1 * p.+1.
  by apply: leq_trans (leq_mul (leqnn p) hN) _; rewrite mulnS mulSn mulnS addSn leqW.
have h4 : (p * N) ^ 2 <= p.+1 ^ 4 by rewrite (expnM p.+1 2 2) leq_exp2r // mulnn.
by have := leq_trans h5 h4; rewrite leq_exp2l.
Qed.


(** ** Row erdos:637 *)

Definition g243_degrees_hyp_claim : Prop :=
  [/\ forall S : {set 'K_2}, cliqueb S || stable S -> 2 ^ #|S| < #|'K_2| ^ 3 &
      (ramsey_graph_induced_distinct_degrees_statement -> exists p : nat, 1 <= p /\
         forall G : sgraph,
           (forall S : {set G}, cliqueb S || stable S -> 2 ^ #|S| < #|G| ^ 3) ->
           exists S : {set G}, #|G| <= p * #|S| /\
             #|G| <= (p * size (undup [seq #|N(x)| | x <- enum [set: induced S]])) ^ 2)].

Theorem g243_degrees_hyp_inhabited : g243_degrees_hyp_claim.
Proof. by split; [exact: g243_K2_ramsey3 | move=> h; exact: h 3]. Qed.

Definition g243_degrees_no_ramsey : Prop :=
  forall C : nat, exists p : nat, 1 <= p /\
    forall G : sgraph,
      exists S : {set G}, #|G| <= p * #|S| /\
        #|G| <= (p * size (undup [seq #|N(x)| | x <- enum [set: induced S]])) ^ 2.

Definition g243_degrees_ntt_claim : Prop :=
  ~ g243_degrees_no_ramsey /\ (g243_degrees_no_ramsey -> ramsey_graph_induced_distinct_degrees_statement).

Theorem g243_degrees_not_trivially_true : g243_degrees_ntt_claim.
Proof.
split; last first.
  by move=> h C; have [p [p1 hp]] := h C; exists p; split => // G _; exact: hp.
move=> h; have [p [p1 hp]] := h 0.
have [S [_]] := hp (complete_multipartite_graph 1 (p ^ 2).+1).
have := g243_degrees_edgeless S (@g243_edgeless (p ^ 2).+1).
rewrite card_complete_multipartite_graph mul1n.
set D := size _ => hD.
have : (p * D) ^ 2 <= p ^ 2 by rewrite leq_exp2r // -{2}(muln1 p) leq_mul.
by move=> h1 h2; have := leq_trans h2 h1; rewrite ltnn.
Qed.

(** ** Row erdos:666 *)

(** A graph with every edge deleted has no C_6. *)
Lemma g243_no_edge_no_C6 (G : sgraph) : ~ has_subgraph (del_edge_set G E(G)) (cycle_graph 6).
Proof.
case/has_subgraphP => f [_ fh].
have e01 : (ord0 : cycle_graph 6) -- (Ordinal (isT : 1 < 6)) by [].
have := fh _ _ e01; rewrite del_edge_setE => /andP [xy]; apply/negP; rewrite negbK.
by apply/(@edgesP G); exists (f ord0), (f (Ordinal (isT : 1 < 6))).
Qed.

(** Q_1 has an edge: the instance n = 1, q = 1, F = {that edge} meets the density hypothesis. *)
Definition g243_Q1_x : product_hypercube 1 := (ord0, ord0).
Definition g243_Q1_y : product_hypercube 1 := (ord_max, ord0).

Lemma g243_Q1_edge : g243_Q1_x -- g243_Q1_y.
Proof. by []. Qed.

Definition g243_cube_hyp_claim : Prop :=
  [/\ [set [set g243_Q1_x; g243_Q1_y]] \subset E(product_hypercube 1),
      1 * 2 ^ 1 <= 2 * 1 * #|[set [set g243_Q1_x; g243_Q1_y]]| &
      (hypercube_dense_subgraph_C6_statement -> exists n0 : nat,
         forall (n : nat) (F : {set {set product_hypercube n}}), n0 <= n -> F \subset E(product_hypercube n) ->
           n * 2 ^ n <= 2 * 1 * #|F| ->
           has_subgraph (del_edge_set (product_hypercube n) (E(product_hypercube n) :\: F)) (cycle_graph 6))].

Theorem g243_cube_hyp_inhabited : g243_cube_hyp_claim.
Proof.
split; [|by rewrite cards1 | move=> h; exact: h 1 (leqnn 1)].
by rewrite sub1set; apply/edgesP; exists g243_Q1_x, g243_Q1_y; split; [|exact: g243_Q1_edge].
Qed.

Definition g243_cube_no_density : Prop :=
  forall q : nat, 1 <= q -> exists n0 : nat,
    forall (n : nat) (F : {set {set product_hypercube n}}), n0 <= n -> F \subset E(product_hypercube n) ->
      has_subgraph (del_edge_set (product_hypercube n) (E(product_hypercube n) :\: F)) (cycle_graph 6).

Definition g243_cube_ntt_claim : Prop :=
  ~ g243_cube_no_density /\ (g243_cube_no_density -> hypercube_dense_subgraph_C6_statement).

Theorem g243_cube_not_trivially_true : g243_cube_ntt_claim.
Proof.
split.
- move=> h; have [n0 hn] := h 1 (leqnn 1).
  have := hn n0 set0 (leqnn n0) (sub0set _); rewrite setD0.
  exact: g243_no_edge_no_C6.
- by move=> h q q1; have [n0 hn] := h q q1; exists n0 => n F nn FE _; exact: hn.
Qed.

(** ** Row erdos:133 *)

Lemma g243_edgeless_no_K3 (G : sgraph) : (forall x y : G, ~~ x -- y) -> ~ has_subgraph G 'K_3.
Proof.
move=> noE /has_subgraphP [f [_ hf]].
by have := hf ord0 (Ordinal (isT : 1 < 3)) isT; rewrite (negbTE (noE _ _)).
Qed.

Lemma g243_dist_le (G : sgraph) (x y : G) (k : nat) : y \in rel_ball (--) k x -> graph_dist x y <= k.
Proof. by rewrite /graph_dist; case: ex_minnP => m _ hm hy; apply: hm; rewrite hy. Qed.

(** Two vertices with a common closed neighbour are at distance at most 2. *)
Lemma g243_dist_le2 (G : sgraph) (x y z : G) :
  (x == z) || (x -- z) -> (z == y) || (z -- y) -> graph_dist x y <= 2.
Proof.
move=> xz zy; apply: g243_dist_le.
have z1 : z \in rel_ball (--) 1 x.
  rewrite /= !inE; case/orP: xz => [/eqP -> | xz]; first by rewrite eqxx.
  by apply/orP; right; apply/bigcupP; exists x; rewrite ?inE.
rewrite /= inE; move: z1; rewrite /= => z1; case/orP: zy => [/eqP <- | zy]; first by rewrite z1.
by apply/orP; right; apply/bigcupP; exists z => //; rewrite inE.
Qed.

Lemma g243_P3_no_K3 : ~ has_subgraph (ordinal_path 3) 'K_3.
Proof.
case/has_subgraphP => f [_ hf].
move: (hf ord0 (Ordinal (isT : 1 < 3)) isT) (hf (Ordinal (isT : 1 < 3)) (Ordinal (isT : 2 < 3)) isT)
  (hf ord0 (Ordinal (isT : 2 < 3)) isT).
case: (f ord0) => [[|[|[|a]]] ha] //; case: (f (Ordinal _)) => [[|[|[|b]]] hb] //;
  case: (f (Ordinal _)) => [[|[|[|c]]] hc] //.
Qed.

Lemma g243_P3_diameter : forall x y : ordinal_path 3, graph_dist x y <= 2.
Proof.
move=> x y; apply: (@g243_dist_le2 _ x y (Ordinal (isT : 1 < 3))).
  by case: x => [[|[|[|x]]] hx].
by case: y => [[|[|[|y]]] hy].
Qed.

Definition g243_diam_hyp_claim : Prop :=
  [/\ ~ has_subgraph (ordinal_path 3) ('K_3), (forall x y : ordinal_path 3, graph_dist x y <= 2) &
      (triangle_free_diameter_two_max_degree_statement -> exists n0 : nat,
         forall G : sgraph, n0 <= #|G| -> ~ has_subgraph G 'K_3 -> (forall x y : G, graph_dist x y <= 2) ->
           exists v : G, 1 ^ 2 * #|G| <= #|N(v)| ^ 2)].

Theorem g243_diam_hyp_inhabited : g243_diam_hyp_claim.
Proof. by split; [exact: g243_P3_no_K3 | exact: g243_P3_diameter | move=> h; exact: h 1]. Qed.

Definition g243_diam_no_diameter : Prop :=
  forall c : nat, exists n0 : nat,
    forall G : sgraph, n0 <= #|G| -> ~ has_subgraph G 'K_3 ->
      exists v : G, c ^ 2 * #|G| <= #|N(v)| ^ 2.

Definition g243_diam_ntt_claim : Prop :=
  ~ g243_diam_no_diameter /\ (g243_diam_no_diameter -> triangle_free_diameter_two_max_degree_statement).

Theorem g243_diam_not_trivially_true : g243_diam_ntt_claim.
Proof.
split; last first.
  by move=> h c; have [n0 hn] := h c; exists n0 => G nG tf _; exact: hn.
move=> h; have [n0 hn] := h 1.
have [|v] := hn (complete_multipartite_graph 1 n0.+1) _ (g243_edgeless_no_K3 (@g243_edgeless n0.+1)).
  by rewrite card_complete_multipartite_graph mul1n leqnSn.
have -> : #|N(v)| = 0.
  by apply/eqP; rewrite cards_eq0; apply/eqP/setP => w; rewrite !inE; apply/negbTE; exact: g243_edgeless.
by rewrite card_complete_multipartite_graph.
Qed.

(** ** Row erdos:1034 *)

Definition g243_book_hyp_claim : Prop :=
  [/\ #|'K_3| ^ 2 < 4 * edge_count ('K_3),
      [/\ (ord0 : 'K_3) -- Ordinal (isT : 1 < 3), (Ordinal (isT : 1 < 3) : 'K_3) -- Ordinal (isT : 2 < 3)
        & (ord0 : 'K_3) -- Ordinal (isT : 2 < 3)] &
      (dense_graph_triangle_half_two_neighbour_vertices_statement -> exists n0 : nat,
         forall G : sgraph, n0 <= #|G| -> #|G| ^ 2 < 4 * edge_count G ->
           exists (a b c : G) (Y : {set G}),
             [/\ a -- b, b -- c, a -- c, 1 * #|G| < 2 * 1 * #|Y| + 2 * #|G| &
                 forall y : G, y \in Y -> 2 <= (y -- a) + (y -- b) + (y -- c)])].

Theorem g243_book_hyp_inhabited : g243_book_hyp_claim.
Proof. by split; [rewrite card_ord edge_count_Kn | by [] | move=> h; exact: h 1 (leqnn 1)]. Qed.

Definition g243_book_no_density : Prop :=
  forall q : nat, 1 <= q -> exists n0 : nat,
    forall G : sgraph, n0 <= #|G| ->
      exists (a b c : G) (Y : {set G}),
        [/\ a -- b, b -- c, a -- c, q * #|G| < 2 * q * #|Y| + 2 * #|G| &
            forall y : G, y \in Y -> 2 <= (y -- a) + (y -- b) + (y -- c)].

Definition g243_book_ntt_claim : Prop :=
  ~ g243_book_no_density /\ (g243_book_no_density -> dense_graph_triangle_half_two_neighbour_vertices_statement).

Theorem g243_book_not_trivially_true : g243_book_ntt_claim.
Proof.
split; last first.
  by move=> h q q1; have [n0 hn] := h q q1; exists n0 => G nG _; exact: hn.
move=> h; have [n0 hn] := h 1 (leqnn 1).
have [|a [b [c [Y [ab _ _ _ _]]]]] := hn (complete_multipartite_graph 1 n0).
  by rewrite card_complete_multipartite_graph mul1n.
by move: ab; rewrite (negbTE (g243_edgeless a b)).
Qed.

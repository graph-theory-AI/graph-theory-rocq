(** * Extremal.conjectures.grounding_X278 -- grounding certificates of wave X278.

    For each of the three rows: hyp_inhabited (the hypotheses hold on a concrete instance, and the statement gives
    its consequence there) and not_trivially_true in the contract form (a variant obtained from the body by
    deleting one hypothesis is false and implies the row).  X278.v has no local helper, so there is no
    helper_sanity certificate; the wheel that arxiv:2102.10220#01 writes out gets two checks, its order 2r + 2
    ([g278_wheel_card]) and its hub adjacent to every rim vertex ([g278_wheel_hub]).
    - K_r: K_2 is K_3-free and 2-colourable, and the statement gives, at r = 3 and k = 2, triangle-free graphs on
      every large n that need at least n^2 / (4 a) deletions to become bipartite.  Without the threshold n0 the
      row is false at r = 3, k = n = 1: a one-vertex graph is 1-colourable with nothing deleted, and the lower
      clause asks 1 <= (a * 0) * 1.
    - Odd wheels: K_2 has no W_3 (2 < 4 vertices) and is 2-colourable, and the statement gives, at r = 1 and
      k = 2, W_3-free graphs on every large n whose 2-colourable edge deletions F have n^4 <= 8 (a |F|)^2.
      Without the threshold the row is false at r = 1, k = n = 2: a two-vertex graph is 2-colourable with nothing
      deleted, and the lower clause asks 2^4 <= 0.
    - Meshulam: every graph G is a (1, |E(G)|)-RS graph (each edge alone is an induced matching), so the
      hypotheses hold at every order, here on K_(m,m) with 2m vertices and m * m edges; the statement gives its
      conclusion there at a = 4, b = 1.  Without r >= n^(1/b) the row is false at a = 4: K_(m,m) is a
      (1, m * m)-RS graph on 2m vertices and (2m)^2 <= 4 * (1 * (m * m)), for every m. *)

From Extremal.conjectures Require Import X278.
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A graph on at most k vertices is k-colourable, whatever is deleted. *)
Lemma g278_chi_small (G : sgraph) (F : {set {set G}}) (k : nat) :
  #|G| <= k -> χ([set: del_edge_set G F]) <= k.
Proof. by move=> Gk; apply: leq_trans (leq_chi _) _; rewrite cardsT card_del_edge_set. Qed.

(** ** Row 1: arxiv:2102.10220#00 *)

Definition g278_kr_hyp_claim : Prop :=
  [/\ 3 <= 3, 0 < 2, ~ has_subgraph ('K_2) ('K_3),
      set0 \subset E('K_2) /\ χ([set: del_edge_set ('K_2) set0]) <= 2 &
      (kr_free_k_colourable_deletion_sharp_statement ->
         exists a n0 : nat, 0 < a /\ forall n : nat, n0 <= n ->
           exists G : sgraph,
             [/\ #|G| = n, ~ has_subgraph G ('K_3) &
                 forall F : {set {set G}}, F \subset E(G) -> χ([set: del_edge_set G F]) <= 2 ->
                   n ^ 2 <= a * #|F| * 4])].

Theorem g278_kr_hyp_inhabited : g278_kr_hyp_claim.
Proof.
split=> //.
- by move/has_subgraph_card; rewrite !card_ord.
- by split; [exact: sub0set | apply: g278_chi_small; rewrite card_ord].
move=> h; have [a [A [a0 [_ hk]]]] := h 3 isT; have [n0 hn] := hk 2 isT.
exists a, n0; split=> // n nn; have [_ [G [cG fr low]]] := hn n nn.
by exists G; split.
Qed.

Definition g278_kr_no_threshold : Prop :=
  forall r : nat, 3 <= r -> exists a A : nat, 0 < a /\ 0 < A /\
    forall k : nat, 0 < k -> forall n : nat,
      (forall G : sgraph, #|G| = n -> ~ has_subgraph G ('K_r) ->
         exists F : {set {set G}},
           [/\ F \subset E(G), χ([set: del_edge_set G F]) <= k &
               #|F| ^ (r - 2) * k ^ (r - 1) <= (A * n ^ 2) ^ (r - 2)]) /\
      (exists G : sgraph,
         [/\ #|G| = n, ~ has_subgraph G ('K_r) &
             forall F : {set {set G}}, F \subset E(G) -> χ([set: del_edge_set G F]) <= k ->
               n ^ (2 * (r - 2)) <= (a * #|F|) ^ (r - 2) * k ^ (r - 1)]).

Definition g278_kr_ntt_claim : Prop :=
  ~ g278_kr_no_threshold /\ (g278_kr_no_threshold -> kr_free_k_colourable_deletion_sharp_statement).

Theorem g278_kr_not_trivially_true : g278_kr_ntt_claim.
Proof.
split; last first.
  move=> h r r3; have [a [A [a0 [A0 hk]]]] := h r r3.
  by exists a, A; do 2 split=> //; move=> k k0; exists 0 => n _; exact: hk.
move=> h; have [a [A [a0 [A0 hk]]]] := h 3 isT.
have [_ [G [cG _ low]]] := hk 1 isT 1.
have := low set0 (sub0set _) (g278_chi_small set0 (eq_leq cG)).
by rewrite cards0 muln0.
Qed.

(** ** Row 2: arxiv:2102.10220#01 *)

(** The wheel written out in the body: W_(2r+1) has 2r + 2 vertices ... *)
Lemma g278_wheel_card (r : nat) :
  #|add_node (cycle_graph (2 * r + 1)) [set: cycle_graph (2 * r + 1)]| = (2 * r + 1).+1.
Proof. by rewrite card_option card_ord. Qed.

(** ... and its hub [None] is adjacent to every rim vertex. *)
Lemma g278_wheel_hub (r : nat) (x : cycle_graph (2 * r + 1)) :
  (None : add_node (cycle_graph (2 * r + 1)) [set: cycle_graph (2 * r + 1)]) -- Some x.
Proof. by rewrite /edge_rel /= inE. Qed.

Definition g278_ow_hyp_claim : Prop :=
  [/\ 1 <= 1, 2 <= 2, ~ has_subgraph ('K_2) (add_node (cycle_graph 3) [set: cycle_graph 3]),
      set0 \subset E('K_2) /\ χ([set: del_edge_set ('K_2) set0]) <= 2 &
      (odd_wheel_free_k_colourable_deletion_sharp_statement ->
         exists a n0 : nat, 0 < a /\ forall n : nat, n0 <= n ->
           exists G : sgraph,
             [/\ #|G| = n, ~ has_subgraph G (add_node (cycle_graph 3) [set: cycle_graph 3]) &
                 forall F : {set {set G}}, F \subset E(G) -> χ([set: del_edge_set G F]) <= 2 ->
                   n ^ 4 <= (a * #|F|) ^ 2 * 8])].

Theorem g278_ow_hyp_inhabited : g278_ow_hyp_claim.
Proof.
split=> //.
- by move/has_subgraph_card; rewrite (g278_wheel_card 1) card_ord.
- by split; [exact: sub0set | apply: g278_chi_small; rewrite card_ord].
move=> h; have [a [A [a0 [_ hk]]]] := h 1 isT; have [n0 hn] := hk 2 isT.
exists a, n0; split=> // n nn; have [_ [G [cG fr low]]] := hn n nn.
by exists G; split.
Qed.

Definition g278_ow_no_threshold : Prop :=
  forall r : nat, 1 <= r -> exists a A : nat, 0 < a /\ 0 < A /\
    forall k : nat, 2 <= k -> forall n : nat,
      (forall G : sgraph, #|G| = n ->
         ~ has_subgraph G (add_node (cycle_graph (2 * r + 1)) [set: cycle_graph (2 * r + 1)]) ->
         exists F : {set {set G}},
           [/\ F \subset E(G), χ([set: del_edge_set G F]) <= k &
               #|F| ^ (r + 1) * k ^ (2 * r + 1) <= (A * n ^ 2) ^ (r + 1)]) /\
      (exists G : sgraph,
         [/\ #|G| = n, ~ has_subgraph G (add_node (cycle_graph (2 * r + 1)) [set: cycle_graph (2 * r + 1)]) &
             forall F : {set {set G}}, F \subset E(G) -> χ([set: del_edge_set G F]) <= k ->
               n ^ (2 * (r + 1)) <= (a * #|F|) ^ (r + 1) * k ^ (2 * r + 1)]).

Definition g278_ow_ntt_claim : Prop :=
  ~ g278_ow_no_threshold /\ (g278_ow_no_threshold -> odd_wheel_free_k_colourable_deletion_sharp_statement).

Theorem g278_ow_not_trivially_true : g278_ow_ntt_claim.
Proof.
split; last first.
  move=> h r r1; have [a [A [a0 [A0 hk]]]] := h r r1.
  by exists a, A; do 2 split=> //; move=> k k2; exists 0 => n _; exact: hk.
move=> h; have [a [A [a0 [A0 hk]]]] := h 1 isT.
have [_ [G [cG _ low]]] := hk 2 isT 2.
have := low set0 (sub0set _) (g278_chi_small set0 (eq_leq cG)).
by rewrite cards0 muln0.
Qed.

(** ** Row 3: studies:std_meshulam_s_conjecture_on_ruzsa_szemer_di_graphs *)

(** Every graph is a (1, |E(G)|)-RS graph: each edge alone is an induced matching. *)
Lemma g278_rs_single_edges (G : sgraph) (t : nat) : #|E(G)| = t ->
  exists P : 'I_t -> {set {set G}},
    [/\ \bigcup_(i < t) P i = E(G),
        forall i j : 'I_t, i != j -> [disjoint P i & P j],
        forall i : 'I_t, #|P i| = 1,
        forall i : 'I_t, matching (P i) &
        forall (i : 'I_t) (e f : {set G}), e \in P i -> f \in P i -> e != f ->
          forall x y : G, x \in e -> y \in f -> ~~ (x -- y)].
Proof.
move=> <-; exists (fun i => [set enum_val i]); split.
- apply/setP => e; apply/bigcupP/idP => [[i _]|eE]; first by rewrite inE => /eqP ->; exact: enum_valP.
  by exists (enum_rank_in eE e) => //; rewrite inE enum_rankK_in.
- by move=> i j ij; rewrite disjoints1 inE; apply: contra ij => /eqP /enum_val_inj ->.
- by move=> i; rewrite cards1.
- split; first by move=> e; rewrite inE => /eqP ->; exact: enum_valP.
  by move=> e1 e2; rewrite !inE => /eqP -> /eqP ->.
- by move=> i e f; rewrite !inE => /eqP -> /eqP ->; rewrite eqxx.
Qed.

Definition g278_ms_hyp_claim : Prop :=
  [/\ 0 < 4, 0 < 1,
      (forall m : nat, #|('K_m,m)| = m + m /\
         exists P : 'I_(m * m) -> {set {set ('K_m,m)}},
           [/\ \bigcup_(i < m * m) P i = E('K_m,m),
               forall i j : 'I_(m * m), i != j -> [disjoint P i & P j],
               forall i : 'I_(m * m), #|P i| = 1,
               forall i : 'I_(m * m), matching (P i) &
               forall (i : 'I_(m * m)) (e f : {set ('K_m,m)}), e \in P i -> f \in P i -> e != f ->
                 forall x y : ('K_m,m), x \in e -> y \in f -> ~~ (x -- y)]) &
      (meshulam_ruzsa_szemeredi_statement ->
         exists n0 : nat, forall m : nat, n0 <= m + m ->
           ~ ((m + m) ^ 2 <= 4 * (1 * (m * m)) /\ m + m <= 1 ^ 1))].

Theorem g278_ms_hyp_inhabited : g278_ms_hyp_claim.
Proof.
have rs m := g278_rs_single_edges (card_edge_Knm m m).
have cK m : #|('K_m,m)| = m + m by rewrite card_sum !card_ord.
split=> //; move=> h; have [n0 hn] := h 4 1 isT isT.
by exists n0 => m nm; rewrite -(cK m); apply: (hn ('K_m,m) 1 (m * m)); [rewrite cK | exact: rs].
Qed.

Definition g278_ms_no_large_r : Prop :=
  forall a : nat, 0 < a -> exists n0 : nat,
    forall (G : sgraph) (r t : nat), n0 <= #|G| ->
      (exists P : 'I_t -> {set {set G}},
         [/\ \bigcup_(i < t) P i = E(G),
             forall i j : 'I_t, i != j -> [disjoint P i & P j],
             forall i : 'I_t, #|P i| = r,
             forall i : 'I_t, matching (P i) &
             forall (i : 'I_t) (e f : {set G}), e \in P i -> f \in P i -> e != f ->
               forall x y : G, x \in e -> y \in f -> ~~ (x -- y)]) ->
      ~ (#|G| ^ 2 <= a * (r * t)).

Definition g278_ms_ntt_claim : Prop :=
  ~ g278_ms_no_large_r /\ (g278_ms_no_large_r -> meshulam_ruzsa_szemeredi_statement).

Theorem g278_ms_not_trivially_true : g278_ms_ntt_claim.
Proof.
split; last first.
  move=> h a b a0 _; have [n0 hn] := h a a0.
  by exists n0 => G r t nG rs [le _]; exact: hn G r t nG rs le.
move=> h; have [n0 hn] := h 4 isT.
have cK : #|('K_n0,n0)| = n0 + n0 by rewrite card_sum !card_ord.
apply: (hn ('K_n0,n0) 1 (n0 * n0)); first by rewrite cK leq_addr.
  exact: g278_rs_single_edges (card_edge_Knm n0 n0).
by rewrite cK mul1n addnn -mul2n expnMn mulnn.
Qed.

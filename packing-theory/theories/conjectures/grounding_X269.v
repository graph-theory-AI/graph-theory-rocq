(** * Packing.conjectures.grounding_X269 -- grounding certificates for wave X269 (2026-10-31)

    For each of the three rows: hyp_inhabited (the body's conditions hold together at a small instance, and the
    statement gives its consequence), not_trivially_true (a variant without one hypothesis is false and implies
    the statement), and helper_sanity for the two local helpers of X269.v.
    - arxiv:1904.02595#00: K_2 is complete multipartite and K_2 x K_2 has an edge.  Without the
      complete-multipartite hypothesis the row is false at the one-factor product of the triangular prism
      K_3 box K_2: a stable set meets each triangle once (alpha <= 2), and one triangle is irredundant, each
      vertex keeping its rung neighbour private (IR >= 3).  The prism is not complete multipartite.
    - arxiv:2604.09449#01: at k = t = 1 the one colouring of K_2 is colour-balanced and the edge of K_2 is a
      perfect matching with f_c = 0; the statement's C is positive.  Without colour-balance the row is false: on
      K_(4(C+1)) with every edge of colour 0, colour 1 alone contributes |0 - (C + 1)| = C + 1 to f_c.
    - Gruslys-Leader-Tan: Q_1 is a subgraph of itself with an edge and decomposes the edges of Q_1.  Without "H
      has an edge" the row is false: the one-vertex Q_0 is a subgraph of every Q_k and covers no edge of Q_n,
      n >= 1. *)

From GTBase Require Import base common hypercubes edge_copies.
From Packing.conjectures Require Import X269.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** arxiv:1904.02595#00 ************************************************* *)

(** Small ordinals. *)
Definition g269_o1 : 'I_2 := @Ordinal 2 1 isT.
Definition g269_t1 : 'I_3 := @Ordinal 3 1 isT.
Definition g269_t2 : 'I_3 := @Ordinal 3 2 isT.

(** The triangular prism K_3 box K_2. *)
Definition g269_prism : sgraph := cartesian_product 'K_3 'K_2.

Lemma g269_prism_edge (p q : g269_prism) :
  p -- q = ((p.1 == q.1) && (p.2 != q.2)) || ((p.2 == q.2) && (p.1 != q.1)).
Proof. by []. Qed.

(** A stable set of the prism meets each triangle once, so it has at most two vertices. *)
Lemma g269_prism_stable (S : {set g269_prism}) : stable S -> #|S| <= 2.
Proof.
move=> st.
have inj : {in S &, injective (fun p : g269_prism => p.2)}.
  move=> p q pS qS /= e2; apply/eqP; apply: contraT => pq.
  have e1 : p.1 != q.1 by apply: contraNneq pq => e1; apply/eqP/injective_projections.
  have : p -- q by rewrite g269_prism_edge e2 eqxx e1 orbT.
  by move=> pq'; move/stableP: st => /(_ p q pS qS); rewrite pq'.
rewrite -(card_in_imset inj); apply: leq_trans (max_card _) _; by rewrite card_ord.
Qed.

Lemma g269_prism_alpha : α([set: g269_prism]) <= 2.
Proof. by case: (alphaP [set: g269_prism]) => S /maxstabset_stable st; exact: g269_prism_stable. Qed.

(** One triangle of the prism: each of its vertices has its private neighbour across the rungs. *)
Definition g269_layer : {set g269_prism} := [set p | p.2 == ord0].

Lemma g269_layer_irr : irredundant g269_layer.
Proof.
apply/forallP => v; apply/implyP; rewrite inE => /eqP v2.
apply/set0Pn; exists (v.1, g269_o1); rewrite !inE.
apply/andP; split; last by rewrite g269_prism_edge eqxx v2 orbT.
apply/bigcupP => -[w]; rewrite !inE => /andP [wv /eqP w2] /orP [/eqP e|].
  by move: w2; rewrite -e.
rewrite g269_prism_edge w2 /= andbT => /orP [/eqP e1|//].
by move: wv; rewrite (surjective_pairing w) (surjective_pairing v) e1 w2 v2 eqxx.
Qed.

Lemma g269_layer_card : #|g269_layer| = 3.
Proof.
have -> : g269_layer = [set (i, ord0 : 'I_2) | i : 'I_3].
  apply/setP => -[i j]; rewrite !inE /=; apply/eqP/imsetP => [-> | [i' _ [_ ->]]] //.
  by exists i.
by rewrite card_imset ?card_ord // => i i' [].
Qed.

Lemma g269_prism_IR : 3 <= IR g269_prism.
Proof.
rewrite /IR; case: arg_maxnP => [|M _ Mmax]; first by apply/forallP => v; rewrite inE.
by rewrite -g269_layer_card; exact: Mmax g269_layer_irr.
Qed.

(** The prism is not complete multipartite: non-adjacency is not transitive on it. *)
Lemma g269_prism_not_mp : ~ x269_multipartite_complete g269_prism.
Proof.
case=> k [p hp].
have na (x y : g269_prism) : ~~ x -- y -> p x = p y by rewrite hp negbK => /eqP.
have e1 := na (ord0, ord0) (g269_t1, g269_o1) isT.
have e2 := na (g269_t1, g269_o1) (g269_t2, ord0) isT.
by have := hp (ord0, ord0) (g269_t2, ord0); rewrite e1 e2 eqxx.
Qed.

(** Two factors K_2. *)
Definition g269_K2s : 'I_2 -> sgraph := fun _ => 'K_2.

Lemma g269_K2_mp : x269_multipartite_complete 'K_2.
Proof. by exists 2, id. Qed.

(** hyp_inhabited: K_2 is complete multipartite (two singleton parts), K_2 x K_2 has an edge, and the statement
    gives alpha = IR there. *)
Definition g269_mp_hyp_claim : Prop :=
  [/\ forall i, x269_multipartite_complete (g269_K2s i),
      (exists x y : x269_tensor_prod g269_K2s, x -- y) &
      (alpha_ir_multipartite_products_statement ->
         α([set: x269_tensor_prod g269_K2s]) = IR (x269_tensor_prod g269_K2s))].

Theorem g269_mp_hyp_inhabited : g269_mp_hyp_claim.
Proof.
have mp : forall i, x269_multipartite_complete (g269_K2s i) by move=> i; exact: g269_K2_mp.
split=> //; first by exists (ord0, ord0), (g269_o1, g269_o1).
by move=> h; exact: h 1 g269_K2s mp.
Qed.

(** not_trivially_true: without the complete-multipartite hypothesis the statement is false at the one-factor
    product of the prism (alpha <= 2 < 3 <= IR). *)
Definition g269_mp_no_mp : Prop :=
  forall (n : nat) (H : 'I_n.+1 -> sgraph), α([set: x269_tensor_prod H]) = IR (x269_tensor_prod H).

Definition g269_mp_ntt_claim : Prop :=
  ~ g269_mp_no_mp /\ (g269_mp_no_mp -> alpha_ir_multipartite_products_statement).

Theorem g269_mp_not_trivially_true : g269_mp_ntt_claim.
Proof.
split.
- move=> h; have e : α([set: g269_prism]) = IR g269_prism := h 0 (fun _ => g269_prism).
  by have := leq_trans g269_prism_IR (leq_trans (eq_leq (esym e)) g269_prism_alpha).
- by move=> h n H _; exact: h.
Qed.

(** ** arxiv:2604.09449#01 ************************************************* *)

(** k = t = 1: the one colouring of K_2 and its one edge. *)
Definition g269_c1 : {set 'K_(2 * 1 * 1)} -> 'I_1 := fun _ => ord0.
Definition g269_M1 : {set {set 'K_(2 * 1 * 1)}} := [set [set: 'K_(2 * 1 * 1)]].

Lemma g269_c1_balanced (i j : 'I_1) :
  #|[set e in E('K_(2 * 1 * 1)) | g269_c1 e == i]| = #|[set e in E('K_(2 * 1 * 1)) | g269_c1 e == j]|.
Proof. by rewrite (ord1 i) (ord1 j). Qed.

(** hyp_inhabited: the colouring is colour-balanced, the edge is a perfect matching with f_c = 0, and the
    statement's constant is positive. *)
Definition g269_cb_hyp_claim : Prop :=
  [/\ forall i j : 'I_1,
        #|[set e in E('K_(2 * 1 * 1)) | g269_c1 e == i]| = #|[set e in E('K_(2 * 1 * 1)) | g269_c1 e == j]|,
      perfect_matching g269_M1,
      \sum_(i < 1) (let a := #|[set e in g269_M1 | g269_c1 e == i]| in (a - 1) + (1 - a)) = 0 &
      (colour_balanced_perfect_matching_statement -> exists C : nat, 0 < C)].

Theorem g269_cb_hyp_inhabited : g269_cb_hyp_claim.
Proof.
split; [exact: g269_c1_balanced | exact: perfect_matching_K2 | | ].
- rewrite big_ord1 /=.
  have -> : [set e in g269_M1 | g269_c1 e == ord0] = g269_M1 by apply/setP => e; rewrite inE eqxx andbT.
  by rewrite cards1.
- move=> [C hC]; have [M [_ hM]] := hC 1 1 isT isT g269_c1 g269_c1_balanced.
  by exists C; exact: leq_ltn_trans (leq0n _) hM.
Qed.

(** not_trivially_true: without colour-balance the statement is false (all edges of colour 0, two colours). *)
Definition g269_cb_no_balance : Prop :=
  exists C : nat, forall k t : nat, 0 < k -> 0 < t ->
    forall c : {set 'K_(2 * k * t)} -> 'I_k,
      exists M : {set {set 'K_(2 * k * t)}}, perfect_matching M /\
        \sum_(i < k) (let a := #|[set e in M | c e == i]| in (a - t) + (t - a)) < C.

Definition g269_cb_ntt_claim : Prop :=
  ~ g269_cb_no_balance /\ (g269_cb_no_balance -> colour_balanced_perfect_matching_statement).

Theorem g269_cb_not_trivially_true : g269_cb_ntt_claim.
Proof.
split.
- move=> [C hC]; have [M [_]] := hC 2 C.+1 isT isT (fun _ => ord0).
  rewrite big_ord_recr /=.
  have -> : [set e in M | (ord0 : 'I_2) == ord_max] = set0 by apply/setP => e; rewrite !inE andbF.
  rewrite cards0 sub0n add0n subn0 => h.
  by have := leq_ltn_trans (leq_addl _ _) h; rewrite ltnNge leqnSn.
- by move=> [C hC]; exists C => k t k0 t0 c _; exact: hC.
Qed.

(** ** studies:std_gruslys_leader_tan_conjecture_hypercube_edge_dec ************* *)

(** Q_(m+1) has an edge: flip the first coordinate of the all-false tuple. *)
Lemma g269_hc_edge (m : nat) :
  ([tuple of false :: nseq_tuple m false] : tuple_hypercube m.+1) -- [tuple of true :: nseq_tuple m false].
Proof. by rewrite tuple_hypercube_edge_cons eqxx. Qed.

Lemma g269_hc_edges (n : nat) : 1 <= n -> 0 < #|E(tuple_hypercube n)|.
Proof.
case: n => // m _; apply/card_gt0P.
by exists [set [tuple of false :: nseq_tuple m false]; [tuple of true :: nseq_tuple m false]];
  rewrite in_edges g269_hc_edge.
Qed.

(** An edgeless pattern has an empty edge image. *)
Lemma g269_edge_image_edgeless (G T : sgraph) (f : T -> G) :
  (forall x y : T, x -- y = false) -> edge_image f = set0.
Proof.
move=> T0; apply/setP => e; rewrite edge_imageE inE; apply/existsP => -[[x y]] /=.
by rewrite T0.
Qed.

Lemma g269_hc_sub0 (k : nat) : has_subgraph (tuple_hypercube k) (tuple_hypercube 0).
Proof.
apply/has_subgraphP; exists (fun _ => nseq_tuple k false); split.
- by move=> x y _; rewrite (tuple0 x) (tuple0 y).
- by move=> x y; rewrite tuple_hypercube0_edge.
Qed.

(** hyp_inhabited: Q_1 is a subgraph of Q_1 with an edge, and it decomposes the edges of Q_1 by itself; the
    statement gives a decomposition of some Q_n, n >= 1, into copies of Q_1. *)
Definition g269_hc_hyp_claim : Prop :=
  [/\ has_subgraph (tuple_hypercube 1) (tuple_hypercube 1), 0 < #|E(tuple_hypercube 1)|,
      edge_decomposition_exact (tuple_hypercube 1) [:: E(tuple_hypercube 1)] &
      (hypercube_edge_decomposition_statement ->
         exists n : nat, 1 <= n /\
           exists D : seq {set {set tuple_hypercube n}}, edge_decomposition_exact (tuple_hypercube 1) D)].

Theorem g269_hc_hyp_inhabited : g269_hc_hyp_claim.
Proof.
have sub1 : has_subgraph (tuple_hypercube 1) (tuple_hypercube 1).
  by apply/has_subgraphP; exists id; split; [exact: inj_id | by []].
split; [exact: sub1 | exact: g269_hc_edges | exact: edge_decomposition_exact_self | ].
move=> h; exact: (h 1 (tuple_hypercube 1) isT sub1 (@g269_hc_edges 1 isT)).
Qed.

(** not_trivially_true: without "H has an edge" the statement is false (the one-vertex pattern Q_0 covers no edge
    of Q_n, n >= 1). *)
Definition g269_hc_no_edge : Prop :=
  forall (k : nat) (H : sgraph), 1 <= k -> has_subgraph (tuple_hypercube k) H ->
    exists n : nat, 1 <= n /\ exists D : seq {set {set tuple_hypercube n}}, edge_decomposition_exact H D.

Definition g269_hc_ntt_claim : Prop :=
  ~ g269_hc_no_edge /\ (g269_hc_no_edge -> hypercube_edge_decomposition_statement).

Theorem g269_hc_not_trivially_true : g269_hc_ntt_claim.
Proof.
split.
- move=> h; have [n [n1 [D [cp cnt]]]] := h 1 (tuple_hypercube 0) isT (g269_hc_sub0 1).
  have [e eE] := card_gt0P (g269_hc_edges n1).
  have := cnt e; rewrite eE /= => c1.
  have : has (fun A : {set {set tuple_hypercube n}} => e \in A) D by rewrite has_count c1.
  case/hasP => A AD eA; have [f [_ _ eAf]] := cp A AD.
  by move: eA; rewrite eAf g269_edge_image_edgeless ?inE // => x y; rewrite tuple_hypercube0_edge.
- move=> h k H k1 sub _; exact: (h k H k1 sub).
Qed.

(** ** helper_sanity ********************************************************* *)

(** [x269_multipartite_complete]: K_2 is complete multipartite, the prism is not. *)
Definition g269_mp_helper_claim : Prop :=
  x269_multipartite_complete 'K_2 /\ ~ x269_multipartite_complete g269_prism.

Theorem g269_mp_helper_sanity : g269_mp_helper_claim.
Proof. by split; [exact: g269_K2_mp | exact: g269_prism_not_mp]. Qed.

(** [x269_tensor_prod]: one factor is the factor itself; two factors are their binary tensor product, adjacent iff
    adjacent in both coordinates. *)
Definition g269_tp_helper_claim : Prop :=
  [/\ forall H : 'I_1 -> sgraph, x269_tensor_prod H = H ord0,
      x269_tensor_prod g269_K2s = tensor_product 'K_2 'K_2 &
      forall x y : (tensor_product 'K_2 'K_2), x -- y = (x.1 != y.1) && (x.2 != y.2)].

Theorem g269_tp_helper_sanity : g269_tp_helper_claim.
Proof. by []. Qed.

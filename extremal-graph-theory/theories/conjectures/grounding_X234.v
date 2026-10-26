(** * Extremal.conjectures.grounding_X234 -- grounding certificates of wave X234.

    For each of the three rows: hyp_inhabited (the hypotheses hold on a concrete instance, and the
    statement then yields its conclusion object there) and not_trivially_true (the contract form of
    meta/EXPANSION_PLAN.md 4.4: a variant dropping a load-bearing hypothesis or strengthening the
    conclusion is false, and that variant implies the row).  The helper_sanity certificate for
    [x234_blowup_colouring] is shared by the three rows, with two positive instances and one
    negative instance.  Small instances: K_1, K_2 and K_3 (r_q(K_2) = 2 for every q >= 1), the
    blowups K_1[2] (no edge) and K_2[2]. *)

From GTBase Require Import base common clique_counts complete_multipartite_graphs.
From Extremal.foundations Require Import edge_colourings.
From Extremal.conjectures Require Import X195 X234.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Ramsey facts and helper instances *)

(** Any graph with an edge arrows K_2 in any positive number of colours. *)
Lemma g234_edge_arrows (G : sgraph) (u v : G) (q : nat) :
  u -- v -> x195_arrows G q (fun _ : 'I_1 => 'K_2).
Proof.
move=> uv col; exists ord0, (col [set u; v]).
have uv' : u != v by rewrite (sg_edgeNeq uv).
pose emb (x : 'K_2) : G := if x == ord0 then u else v.
have embE (x y : 'K_2) : x != y -> [set emb x; emb y] = [set u; v].
  move=> xy; rewrite /emb; case: (eqVneq x ord0) => [x0|x0]; case: (eqVneq y ord0) => [y0|y0].
  - by move: xy; rewrite x0 y0 eqxx.
  - by [].
  - by rewrite setUC.
  - exfalso; move: x0 y0 xy; case: x => [[|[|x]] hx] //; case: y => [[|[|y]] hy] //.
exists emb; split.
- move=> x y; rewrite /emb; case: (eqVneq x ord0) => [x0|x0]; case: (eqVneq y ord0) => [y0|y0].
  + by rewrite x0 y0.
  + by move=> e; move: uv'; rewrite e eqxx.
  + by move=> e; move: uv'; rewrite e eqxx.
  + by move: x0 y0; case: x => [[|[|x]] hx] //; case: y => [[|[|y]] hy] //; move=> _ _ _; apply: val_inj.
- move=> x y xy; rewrite /emb; case: (eqVneq x ord0) => [x0|x0]; case: (eqVneq y ord0) => [y0|y0].
  + by move: xy; rewrite x0 y0 sg_irrefl.
  + exact: uv.
  + by rewrite sg_sym.
  + by exfalso; move: x0 y0 xy; case: x => [[|[|x]] hx] //; case: y => [[|[|y]] hy] //.
- by move=> x y xy; rewrite embE.
Qed.

Lemma g234_K2_ramsey (q : nat) : 0 < q -> x195_ramsey_number q (fun _ : 'I_1 => 'K_2) 2.
Proof.
move=> q0; split; first exact: (@g234_edge_arrows 'K_2 ord0 (Ordinal (isT : 1 < 2))).
move=> m m2 h.
have [i [c [emb [inj _ _]]]] := h (fun _ => Ordinal q0).
by move: (leq_card _ inj); rewrite !card_ord leqNgt m2.
Qed.

Lemma g234_ramsey_unique (k r : nat) (Fam : 'I_r -> sgraph) (n n' : nat) :
  x195_ramsey_number k Fam n -> x195_ramsey_number k Fam n' -> n = n'.
Proof.
move=> [a m] [a' m']; apply/eqP; rewrite eqn_leq; apply/andP; split; rewrite leqNgt; apply/negP => lt.
- exact: m _ lt a'.
- exact: m' _ lt a.
Qed.

(** On K_1[2] every colouring is a blowup colouring (no edges). *)
Lemma g234_blowup_K1 (col : {set complete_multipartite_graph 1 2} -> 'I_2) : x234_blowup_colouring col.
Proof. by exists (fun _ => ord0) => x y; rewrite (ord1 x.1) (ord1 y.1) eqxx. Qed.

(** A constant colouring is a blowup colouring. *)
Lemma g234_blowup_const (n : nat) (c : 'I_2) :
  x234_blowup_colouring (fun _ : {set complete_multipartite_graph n 2} => c).
Proof. by exists (fun _ => c). Qed.

(** A colouring of K_2[2] giving the two edges (0,0)-(1,0) and (0,1)-(1,0), which join the same two
    parts, different colours is not a blowup colouring (arXiv:2207.07775 l.1110). *)
Definition g234_v (p i : nat) (hp : p < 2) (hi : i < 2) : complete_multipartite_graph 2 2 :=
  (Ordinal hp, Ordinal hi).

Definition g234_split_col (e : {set complete_multipartite_graph 2 2}) : 'I_2 :=
  if e == [set g234_v (isT : 0 < 2) (isT : 1 < 2); g234_v (isT : 1 < 2) (isT : 0 < 2)]
  then @Ordinal 2 1 isT else ord0.

Lemma g234_blowup_negative : ~ x234_blowup_colouring g234_split_col.
Proof.
case=> chi h.
set a00 := g234_v (isT : 0 < 2) (isT : 0 < 2).
set a01 := g234_v (isT : 0 < 2) (isT : 1 < 2).
set a10 := g234_v (isT : 1 < 2) (isT : 0 < 2).
have ne : [set a00; a10] != [set a01; a10].
  apply/negP => /eqP e; have : a00 \in [set a01; a10] by rewrite -e !inE eqxx.
  by rewrite !inE.
have h1 := h a00 a10 isT; have h2 := h a01 a10 isT.
move: h1 h2; rewrite /g234_split_col -/a01 -/a10 (negbTE ne) eqxx => h1 h2.
have e : @Ordinal 2 1 isT = (ord0 : 'I_2) by rewrite h2 h1.
by move/(congr1 val): e.
Qed.

(** ** helper_sanity *)

Definition g234_blowup_claim : Prop :=
  [/\ forall (n : nat) (c : 'I_2), x234_blowup_colouring (fun _ : {set complete_multipartite_graph n 2} => c),
      forall col : {set complete_multipartite_graph 1 2} -> 'I_2, x234_blowup_colouring col
    & ~ x234_blowup_colouring g234_split_col].

Theorem g234_blowup_sanity : g234_blowup_claim.
Proof. split; [exact: g234_blowup_const | exact: g234_blowup_K1 | exact: g234_blowup_negative]. Qed.

(** ** Row arxiv:2207.07775#01 *)

Definition g234_mixed_hyp_claim : Prop :=
  x195_ramsey_number 2 (fun _ : 'I_1 => 'K_2) 2 /\
  (mixed_blowup_colouring_statement ->
     exists k R : nat, 2 <= k /\ x195_ramsey_number 2 (fun _ : 'I_1 => 'K_k) R).

Theorem g234_mixed_hyp_inhabited : g234_mixed_hyp_claim.
Proof.
split; first exact: g234_K2_ramsey.
by move=> h; have [k [R [k2 hR _]]] := h 2; exists k, R.
Qed.

(** The variant "for EVERY k >= 2" is false at k = 2 (r(2) = 2 and K_1[2] has no edges, so
    every colouring is a blowup colouring); it implies the row. *)
Definition g234_mixed_all : Prop :=
  forall k : nat, 2 <= k -> exists R : nat, x195_ramsey_number 2 (fun _ : 'I_1 => 'K_k) R /\
    exists col : {set complete_multipartite_graph R.-1 2} -> 'I_2,
      (forall c : 'I_2, ~ mono_copy 'K_k col c) /\ ~ x234_blowup_colouring col.

Definition g234_mixed_ntt_claim : Prop :=
  ~ g234_mixed_all /\ (g234_mixed_all -> mixed_blowup_colouring_statement).

Theorem g234_mixed_not_trivially_true : g234_mixed_ntt_claim.
Proof.
split.
- move=> h; have [R [hR [col [_ nb]]]] := h 2 (leqnn 2).
  have eR := g234_ramsey_unique hR (g234_K2_ramsey (isT : 0 < 2)).
  subst R; apply: nb; exact: g234_blowup_K1.
- move=> h N; have [R [hR hc]] := h (maxn N 2) (leq_maxr N 2).
  by exists (maxn N 2), R; split=> //; rewrite leq_maxl.
Qed.

(** ** Row arxiv:2312.06895#00 *)

Definition g234_clique_hyp_claim : Prop :=
  [/\ x195_ramsey_number 2 (fun _ : 'I_1 => 'K_2) 2,
      x195_arrows 'K_2 2 (fun _ : 'I_1 => 'K_2) &
      (clique_ramsey_count_statement ->
         forall G : sgraph, x195_arrows G 2 (fun _ : 'I_1 => 'K_2) -> 1 <= clique_count_size G 2)].

Theorem g234_clique_hyp_inhabited : g234_clique_hyp_claim.
Proof.
have r2 := g234_K2_ramsey (isT : 0 < 2).
split=> //; first exact: r2.1.
move=> h G hG; have [_ low] := h 2 2 (leqnn 2) 2 r2; exact: low G hG.
Qed.

(** K_1 has no 2-clique. *)
Lemma g234_K1_no_edge : clique_count_size 'K_1 2 = 0.
Proof. by apply: clique_count_size_gt; rewrite card_ord. Qed.

(** Contract form: the row with the load-bearing hypothesis [x195_arrows G] dropped from the lower
    bound is false (s = t = 2, R = r(K_2) = 2, G = K_1: no edge, C(2, 2) = 1); it implies the row. *)
Definition g234_clique_noarrows : Prop :=
  forall s t : nat, s <= t -> forall R : nat, x195_ramsey_number 2 (fun _ : 'I_1 => 'K_t) R ->
    (exists G : sgraph, x195_arrows G 2 (fun _ : 'I_1 => 'K_t) /\ clique_count_size G s = 'C(R, s)) /\
    (forall G : sgraph, 'C(R, s) <= clique_count_size G s).

(** An extra: the variant "EVERY K_t-Ramsey graph has exactly C(R, s) s-cliques" is false (K_3
    arrows K_2 and has 3 edges, C(2, 2) = 1); it implies the row (K_R itself is K_t-Ramsey). *)
Definition g234_clique_exact : Prop :=
  forall s t : nat, s <= t -> forall R : nat, x195_ramsey_number 2 (fun _ : 'I_1 => 'K_t) R ->
    forall G : sgraph, x195_arrows G 2 (fun _ : 'I_1 => 'K_t) -> clique_count_size G s = 'C(R, s).

Definition g234_clique_ntt_claim : Prop :=
  [/\ ~ g234_clique_noarrows, g234_clique_noarrows -> clique_ramsey_count_statement,
      ~ g234_clique_exact & g234_clique_exact -> clique_ramsey_count_statement].

Theorem g234_clique_not_trivially_true : g234_clique_ntt_claim.
Proof.
split.
- move=> h; have [_ low] := h 2 2 (leqnn 2) 2 (g234_K2_ramsey (isT : 0 < 2)).
  by have := low 'K_1; rewrite g234_K1_no_edge.
- move=> h s t st R hR; have [ex low] := h s t st R hR.
  by split=> // G _; exact: low G.
- move=> h.
  have k3 : x195_arrows 'K_3 2 (fun _ : 'I_1 => 'K_2).
    exact: (@g234_edge_arrows 'K_3 ord0 (Ordinal (isT : 1 < 3))).
  have := h 2 2 (leqnn 2) 2 (g234_K2_ramsey (isT : 0 < 2)) 'K_3 k3.
  by rewrite clique_count_size2 card_sg_edge_set_K3.
- move=> h s t st R hR; split.
  + by exists 'K_R; split; [exact: hR.1 | exact: h s t st R hR 'K_R hR.1].
  + by move=> G hG; rewrite (h s t st R hR G hG).
Qed.

(** ** Row arxiv:2312.06895#01 *)

Definition g234_multi_hyp_claim : Prop :=
  [/\ x195_ramsey_number 3 (fun _ : 'I_1 => 'K_2) 2,
      x195_arrows 'K_2 3 (fun _ : 'I_1 => 'K_2) &
      (multicolour_clique_ramsey_count_statement ->
         forall G : sgraph, x195_arrows G 3 (fun _ : 'I_1 => 'K_2) -> 1 <= clique_count_size G 2)].

Theorem g234_multi_hyp_inhabited : g234_multi_hyp_claim.
Proof.
have r2 := g234_K2_ramsey (isT : 0 < 3).
split=> //; first exact: r2.1.
move=> h G hG; have [_ low] := h 3 2 2 isT (leqnn 2) 2 r2; exact: low G hG.
Qed.

(** Contract form, as for arxiv:2312.06895#00: without [x195_arrows G] in the lower bound the row
    fails at q = 2, s = t = 2, R = 2, G = K_1; with it restored the variant is the row. *)
Definition g234_multi_noarrows : Prop :=
  forall q s t : nat, 2 <= q -> s <= t ->
    forall R : nat, x195_ramsey_number q (fun _ : 'I_1 => 'K_t) R ->
      (exists G : sgraph, x195_arrows G q (fun _ : 'I_1 => 'K_t) /\ clique_count_size G s = 'C(R, s)) /\
      (forall G : sgraph, 'C(R, s) <= clique_count_size G s).

(** An extra, as for arxiv:2312.06895#00: "exactly C(R, s)" fails for K_3 and K_2 (q = 3). *)
Definition g234_multi_exact : Prop :=
  forall q s t : nat, 2 <= q -> s <= t ->
    forall R : nat, x195_ramsey_number q (fun _ : 'I_1 => 'K_t) R ->
      forall G : sgraph, x195_arrows G q (fun _ : 'I_1 => 'K_t) -> clique_count_size G s = 'C(R, s).

Definition g234_multi_ntt_claim : Prop :=
  [/\ ~ g234_multi_noarrows, g234_multi_noarrows -> multicolour_clique_ramsey_count_statement,
      ~ g234_multi_exact & g234_multi_exact -> multicolour_clique_ramsey_count_statement].

Theorem g234_multi_not_trivially_true : g234_multi_ntt_claim.
Proof.
split.
- move=> h; have [_ low] := h 2 2 2 (leqnn 2) (leqnn 2) 2 (g234_K2_ramsey (isT : 0 < 2)).
  by have := low 'K_1; rewrite g234_K1_no_edge.
- move=> h q s t q2 st R hR; have [ex low] := h q s t q2 st R hR.
  by split=> // G _; exact: low G.
- move=> h.
  have k3 : x195_arrows 'K_3 3 (fun _ : 'I_1 => 'K_2).
    exact: (@g234_edge_arrows 'K_3 ord0 (Ordinal (isT : 1 < 3))).
  have := h 3 2 2 isT (leqnn 2) 2 (g234_K2_ramsey (isT : 0 < 3)) 'K_3 k3.
  by rewrite clique_count_size2 card_sg_edge_set_K3.
- move=> h q s t q2 st R hR; split.
  + by exists 'K_R; split; [exact: hR.1 | exact: h q s t q2 st R hR 'K_R hR.1].
  + by move=> G hG; rewrite (h q s t q2 st R hR G hG).
Qed.

(** Row arxiv:2312.06895#01 at q = 2 is row arxiv:2312.06895#00, by conversion. *)
Remark g234_multi_two : multicolour_clique_ramsey_count_statement -> clique_ramsey_count_statement.
Proof. by move=> h s t st R hR; exact: h 2 s t (leqnn 2) st R hR. Qed.

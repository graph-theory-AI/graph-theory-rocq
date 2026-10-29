(** * Extremal.conjectures.grounding_X257 -- grounding certificates of wave X257.

    For each of the two rows: hyp_inhabited (the hypotheses hold with concrete values of the relational hypotheses, and
    the statement then yields its conclusion at a concrete parameter) and not_trivially_true in the contract form of
    meta/EXPANSION_PLAN.md 4.4 (a variant obtained from the body is false and implies the row): each row without its
    relational hypotheses (erdos:600 without both threshold hypotheses: a = 1, b = 0 against M + a <= b; erdos:80
    without the book hypothesis: f = 0 against n < f^q).  The concrete values are e(3,2) = e(3,3) = 4 and
    f_{1/3}(3) = 1, both witnessed by K_3: three edges, each in exactly one triangle (grounding_X230's g230_book_Kn).
    helper_sanity: e(3,2) = 4 (four edges force vacuously, three do not: K_3) and 5 is not e(3,2); f_{1/3}(3) = 1 (one
    edge is forced, two are not: K_3) and 2 is not f_{1/3}(3).  The facts X257.v's Notes use: g257_number_mono
    (e(n,r) <= e(n,r+1)), g257_forcing_vacuous (C(n,2) + 1 edges force), g257_forcing_exact and g257_exact_one (the
    pinned threshold against the exact-edge wording of Er87), g257_book_empty_1 (no f_c(1)) and g257_poly_log (the
    main question of erdos:80 implies its fallback). *)

From Extremal.conjectures Require Import X230 grounding_X230 grounding_X239 X257.
From GTBase Require Import base common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** K_3: three edges, each in exactly one triangle ***************************** *)

Lemma g257_K3_edges : edge_count 'K_3 = 3.
Proof. by rewrite edge_count_Kn. Qed.

Lemma g257_K3_triangles (x y : 'K_3) : x -- y -> 0 < #|[set z | x -- z & y -- z]|.
Proof. by move=> xy; rewrite (g230_book_Kn_common xy). Qed.

Lemma g257_K3_book : x230_book_at_most 'K_3 1.
Proof. exact: (proj1 (g230_book_Kn (leqnn 3))). Qed.

(** ** Local vocabulary: the threshold e(n,r) ************************************ *)

(** A count forcing r + 1 forces r, so e(n,r) <= e(n,r+1): the lower half of the ratio clause. *)
Lemma g257_forcing_mono (n r m : nat) : x257_triangle_forcing n r.+1 m -> x257_triangle_forcing n r m.
Proof. by move=> h G hG hm ht b hb; exact: ltnW (h G hG hm ht b hb). Qed.

Lemma g257_number_mono (n r a b : nat) :
  x257_triangle_forcing_number n r a -> x257_triangle_forcing_number n r.+1 b -> a <= b.
Proof. by move=> [_ ha] [hb _]; apply: ha; exact: g257_forcing_mono. Qed.

(** A forcing count stays forcing when it grows ("at least m edges" is monotone in m). *)
Lemma g257_forcing_up (n r m m' : nat) : m <= m' -> x257_triangle_forcing n r m -> x257_triangle_forcing n r m'.
Proof. by move=> mm h G hG hm; apply: h hG (leq_trans mm hm). Qed.

(** C(n,2) + 1 edges force everything vacuously (no graph on n vertices has that many), so e(n,r) exists for every n
    and r. *)
Lemma g257_forcing_vacuous (n r : nat) : x257_triangle_forcing n r 'C(n, 2).+1.
Proof. by move=> G hG hm; exfalso; have := g239_edge_count_le hG; rewrite leqNgt hm. Qed.

(** Three edges do not force r >= 2 on three vertices: K_3. *)
Lemma g257_not_forcing_3_3 (r : nat) : 2 <= r -> ~ x257_triangle_forcing 3 r 3.
Proof.
move=> r2 h.
have := h 'K_3 (card_ord 3) (eq_leq (esym g257_K3_edges)) g257_K3_triangles 1 g257_K3_book.
by move/(leq_trans r2).
Qed.

(** e(3,r) = 4 for r >= 2. *)
Lemma g257_forcing_3 (r : nat) : 2 <= r -> x257_triangle_forcing_number 3 r 4.
Proof.
move=> r2; split; first exact: g257_forcing_vacuous.
move=> m h; case: (leqP 4 m) => // m3; exfalso; rewrite ltnS in m3.
exact: g257_not_forcing_3_3 r2 (g257_forcing_up m3 h).
Qed.

(** Er87 quantifies over graphs with exactly e edges.  The pinned threshold at m is that exact-edge property at every
    count e >= m. *)
Lemma g257_forcing_exact (n r m : nat) :
  x257_triangle_forcing n r m <->
  (forall e : nat, m <= e -> forall G : sgraph, #|G| = n -> edge_count G = e ->
     (forall x y : G, x -- y -> 0 < #|[set z | x -- z & y -- z]|) ->
     forall b : nat, x230_book_at_most G b -> r <= b).
Proof.
split.
- by move=> h e me G hG eG; apply: h hG _; rewrite eG.
- by move=> h G hG mG; exact: h (edge_count G) mG G hG erefl.
Qed.

(** Taken literally, the exact-edge property holds vacuously at one edge, for all n and r: if xy is the only edge, a
    common neighbour z of x and y would give a second edge xz. *)
Lemma g257_exact_one (n r : nat) (G : sgraph) : #|G| = n -> edge_count G = 1 ->
  (forall x y : G, x -- y -> 0 < #|[set z | x -- z & y -- z]|) ->
  forall b : nat, x230_book_at_most G b -> r <= b.
Proof.
move=> _ e1 ht b _; exfalso.
have : 0 < edge_count G by rewrite e1.
rewrite /edge_count card_gt0 => /set0Pn [s /edgesP [x [y [_ xy]]]].
have /card_gt0P [z] := ht x y xy; rewrite inE => /andP [xz yz].
have : 1 < edge_count G.
  apply/card_gt1P; exists [set x; y], [set x; z]; rewrite !in_edges xy xz; split=> //.
  apply/negP => /eqP e; have := set22 x y; rewrite e => /set2P [yx | yz'].
  - by move: xy; rewrite yx sg_irrefl.
  - by move: yz; rewrite yz' sg_irrefl.
by rewrite e1.
Qed.

(** helper_sanity: e(3,2) = 4: four edges force (vacuously), three do not (K_3), and 5 is not e(3,2). *)
Definition g257_tf_helper_claim : Prop :=
  [/\ x257_triangle_forcing 3 2 4, ~ x257_triangle_forcing 3 2 3, x257_triangle_forcing_number 3 2 4 &
      ~ x257_triangle_forcing_number 3 2 5].

Theorem g257_tf_helper_sanity : g257_tf_helper_claim.
Proof.
split; [exact: g257_forcing_vacuous | exact: g257_not_forcing_3_3 | exact: g257_forcing_3 |].
by case=> _ /(_ 4 (@g257_forcing_vacuous 3 2)).
Qed.

(** ** Local vocabulary: the forced book size f_c(n), c = 1/p ********************* *)

(** A smaller book is forced whenever a larger one is. *)
Lemma g257_book_forced_down (n p m m' : nat) : m' <= m -> x257_book_forced n p m -> x257_book_forced n p m'.
Proof. by move=> mm h G hG hm ht b hb; exact: leq_trans mm (h G hG hm ht b hb). Qed.

(** One triangle at an edge is forced for every n >= 1: a qualifying graph has an edge (n^2 <= p e(G) with n >= 1),
    and that edge lies in a triangle. *)
Lemma g257_book_forced_1 (n p : nat) : 0 < n -> x257_book_forced n p 1.
Proof.
move=> n0 G hG hm ht b hb.
have : 0 < edge_count G.
  rewrite lt0n; apply/negP => /eqP e0; move: hm; rewrite e0 muln0 leqn0 expn_eq0 => /andP [/eqP n00 _].
  by move: n0; rewrite n00.
rewrite /edge_count card_gt0 => /set0Pn [s /edgesP [x [y [_ xy]]]].
exact: leq_trans (ht x y xy) (hb x y xy).
Qed.

(** Two triangles at an edge are not forced on three vertices at c = 1/3: K_3 (3^2 <= 3 * 3). *)
Lemma g257_not_book_forced_3_2 : ~ x257_book_forced 3 3 2.
Proof.
move=> h; have e3 : 3 ^ 2 <= 3 * edge_count 'K_3 by rewrite g257_K3_edges.
by have := h 'K_3 (card_ord 3) e3 g257_K3_triangles 1 g257_K3_book.
Qed.

(** f_{1/3}(3) = 1. *)
Lemma g257_book_3 : x257_book_number 3 3 1.
Proof.
split; first exact: g257_book_forced_1.
move=> m h; case: (leqP m 1) => // m1; exfalso.
exact: g257_not_book_forced_3_2 (g257_book_forced_down m1 h).
Qed.

(** f_c(1) does not exist: no graph on one vertex has an edge, so no graph qualifies and every m is forced. *)
Lemma g257_book_empty_1 (p f : nat) : ~ x257_book_number 1 p f.
Proof.
case=> _ /(_ f.+1) h; suff : f.+1 <= f by rewrite ltnn.
apply: h => G hG; have e0 : edge_count G = 0.
  by apply/eqP; rewrite -leqn0; exact: (g239_edge_count_le hG).
by rewrite e0 muln0.
Qed.

(** The main question of erdos:80 implies its fallback: n < f^q gives n <= 2^(q f), as f < 2^f. *)
Lemma g257_poly_log (p : nat) :
  (exists q N : nat, 1 <= q /\ forall n f : nat, N <= n -> x257_book_number n p f -> n < f ^ q) ->
  exists C N : nat, forall n f : nat, N <= n -> x257_book_number n p f -> n <= 2 ^ (C * f).
Proof.
case=> q [N [q1 h]]; exists q, N => n f hn hf.
apply: ltnW; apply: (leq_trans (h n f hn hf)).
rewrite mulnC expnM leq_exp2r //; exact: ltnW (ltn_expl _ (isT : 1 < 2)).
Qed.

(** helper_sanity: f_{1/3}(3) = 1: one edge is forced, two are not (K_3), and 2 is not f_{1/3}(3). *)
Definition g257_bk_helper_claim : Prop :=
  [/\ x257_book_forced 3 3 1, ~ x257_book_forced 3 3 2, x257_book_number 3 3 1 & ~ x257_book_number 3 3 2].

Theorem g257_bk_helper_sanity : g257_bk_helper_claim.
Proof.
split; [exact: g257_book_forced_1 | exact: g257_not_book_forced_3_2 | exact: g257_book_3 |].
by case=> h _; exact: g257_not_book_forced_3_2 h.
Qed.

(** ** erdos:600 ************************************************************* *)

(** hyp_inhabited: r = 2 meets the guard, e(3,2) = e(3,3) = 4 are concrete threshold values, and the statement then
    gives its first clause at r = 2. *)
Definition g257_tf_hyp_claim : Prop :=
  [/\ 2 <= 2, x257_triangle_forcing_number 3 2 4, x257_triangle_forcing_number 3 3 4 &
      (triangle_covered_book_threshold_increments_statement ->
         forall M : nat, exists N : nat, forall n a b : nat, N <= n ->
           x257_triangle_forcing_number n 2 a -> x257_triangle_forcing_number n 3 b -> M + a <= b)].

Theorem g257_tf_hyp_inhabited : g257_tf_hyp_claim.
Proof.
split=> //; [exact: g257_forcing_3 | exact: g257_forcing_3 |].
by move=> h; exact: (proj1 (h 2 (leqnn 2))).
Qed.

(** not_trivially_true: without the two threshold hypotheses, a = 1 and b = 0 break M + a <= b at r = 2, M = 0. *)
Definition g257_tf_no_threshold : Prop :=
  forall r : nat, 2 <= r ->
    (forall M : nat, exists N : nat, forall n a b : nat, N <= n -> M + a <= b) /\
    (forall q : nat, 1 <= q -> exists N : nat, forall n a b : nat, N <= n -> q * b <= (q + 1) * a).

Definition g257_tf_ntt_claim : Prop :=
  ~ g257_tf_no_threshold /\ (g257_tf_no_threshold -> triangle_covered_book_threshold_increments_statement).

Theorem g257_tf_not_trivially_true : g257_tf_ntt_claim.
Proof.
split.
- by move=> h; have [N hN] := proj1 (h 2 (leqnn 2)) 0; have := hN N 1 0 (leqnn N).
- move=> h r hr; have [h1 h2] := h r hr; split.
  + by move=> M; have [N hN] := h1 M; exists N => n a b hn _ _; exact: hN.
  + by move=> q hq; have [N hN] := h2 q hq; exists N => n a b hn _ _; exact: hN.
Qed.

(** ** erdos:80 ************************************************************** *)

(** hyp_inhabited: p = 3 (c = 1/3) meets the guard, f_{1/3}(3) = 1 is a concrete book value, and the statement then
    gives its conclusion at p = 3. *)
Definition g257_bk_hyp_claim : Prop :=
  [/\ 1 <= 3, x257_book_number 3 3 1 &
      (triangle_covered_dense_book_polynomial_statement ->
         exists q N : nat, 1 <= q /\ forall n f : nat, N <= n -> x257_book_number n 3 f -> n < f ^ q)].

Theorem g257_bk_hyp_inhabited : g257_bk_hyp_claim.
Proof. by split=> //; [exact: g257_book_3 | move=> h; exact: h 3 isT]. Qed.

(** not_trivially_true: without the book hypothesis, f = 0 breaks n < f^q (q >= 1) at p = 1. *)
Definition g257_bk_no_book : Prop :=
  forall p : nat, 1 <= p -> exists q N : nat, 1 <= q /\ forall n f : nat, N <= n -> n < f ^ q.

Definition g257_bk_ntt_claim : Prop :=
  ~ g257_bk_no_book /\ (g257_bk_no_book -> triangle_covered_dense_book_polynomial_statement).

Theorem g257_bk_not_trivially_true : g257_bk_ntt_claim.
Proof.
split.
- move=> h; have [q [N [q1 hN]]] := h 1 (leqnn 1); have := hN N 0 (leqnn N).
  by rewrite exp0n // ltn0.
- move=> h p hp; have [q [N [q1 hN]]] := h p hp; exists q, N; split=> // n f hn _; exact: hN.
Qed.

Print Assumptions g257_tf_helper_sanity.
Print Assumptions g257_bk_helper_sanity.
Print Assumptions g257_number_mono.
Print Assumptions g257_forcing_exact.
Print Assumptions g257_exact_one.
Print Assumptions g257_poly_log.
Print Assumptions g257_book_empty_1.
Print Assumptions g257_tf_hyp_inhabited.
Print Assumptions g257_tf_not_trivially_true.
Print Assumptions g257_bk_hyp_inhabited.
Print Assumptions g257_bk_not_trivially_true.

(** * Extremal.conjectures.grounding_X237 -- grounding certificates of wave X237.

    For each of the six rows: hyp_inhabited (the hypotheses hold on a concrete instance, and the
    statement then yields its conclusion there) and not_trivially_true in the contract form of
    meta/EXPANSION_PLAN.md 4.4 (the row with its load-bearing hypothesis dropped is false, and that
    variant implies the row): the Ramsey hypothesis for erdos:181, erdos:1029 and the Schur-Erdos
    row, the Turan hypothesis for erdos:572 and erdos:714, and "m(G) <= m" for the
    Kuperwasser-Samotij-Wigderson row (refuted at m = 1/5 by two disjoint triangles, Arthur's A3
    item: a forest misses an edge of each triangle, as a forest has no K_3 minor).  One
    helper_sanity certificate covers the two x237_ helpers, with positive and negative instances.
    Small instances: K_1, K_2, K_3, K_5, Q_1, C_6, K_{2,2} and two disjoint triangles. *)

From Extremal.foundations Require Import edge_colourings.
From Extremal.conjectures Require Import X195 D2tur X233 X237.
(* GTBase last: its canonical [edge_count] must shadow D2tur's eta-alias of the same name. *)
From GTBase Require Import base common hypercubes complete_multipartite_graphs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Ramsey and Turan instances *)

Lemma g237_edge_arrows (G : sgraph) (u v : G) (q : nat) :
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

Lemma g237_K2_ramsey (q : nat) : 0 < q -> x195_ramsey_number q (fun _ : 'I_1 => 'K_2) 2.
Proof.
move=> q0; split; first exact: (@g237_edge_arrows 'K_2 ord0 (Ordinal (isT : 1 < 2))).
move=> m m2 h.
have [i [c [emb [inj _ _]]]] := h (fun _ => Ordinal q0).
by move: (leq_card _ inj); rewrite !card_ord leqNgt m2.
Qed.

(** Copies transfer along injective homomorphisms, and need enough host vertices. *)
Lemma g237_mono_copy_hom (Host F F' : sgraph) (C : eqType) (col : {set Host} -> C) (c : C)
    (h : F' -> F) :
  injective h -> (forall x y : F', x -- y -> h x -- h y) -> mono_copy F col c -> mono_copy F' col c.
Proof.
move=> hi hh [emb [ei eh ec]]; exists (emb \o h); split.
- exact: inj_comp.
- by move=> x y xy; apply: eh; apply: hh.
- by move=> x y xy; apply: ec; apply: hh.
Qed.

Lemma g237_mono_copy_card (Host F : sgraph) (C : eqType) (col : {set Host} -> C) (c : C) :
  mono_copy F col c -> #|F| <= #|Host|.
Proof. by case=> emb [ei _ _]; exact: leq_card ei. Qed.

(** Q_1 = K_2 x K_1 has Ramsey number 2. *)
Lemma g237_Q1_ramsey : x195_ramsey_number 2 (fun _ : 'I_1 => product_hypercube 1) 2.
Proof.
split.
- move=> col; have [i [c hc]] := @g237_edge_arrows 'K_2 ord0 (Ordinal (isT : 1 < 2)) 2 isT col.
  exists i, c; apply: (@g237_mono_copy_hom _ 'K_2 (product_hypercube 1) _ col c (fun v => v.1)) hc.
  + by move=> [a x] [b y] /= e; rewrite e (ord1 x) (ord1 y).
  + move=> [a x] [b y]; rewrite /edge_rel /= /box_rel /=.
    by case/orP => /andP [h1 h2] //; move: h2; rewrite /edge_rel /= (ord1 x) (ord1 y) eqxx.
- move=> m m2 h; have [i [c hc]] := h (fun _ => ord0).
  by have := g237_mono_copy_card hc; rewrite card_prod !card_ord leqNgt m2.
Qed.

(** One colour: K_3 is its own Ramsey number. *)
Lemma g237_K3_one_colour : x195_ramsey_number 1 (fun _ : 'I_1 => 'K_3) 3.
Proof.
split.
- move=> col; exists ord0, ord0, id; split => //.
  by move=> x y _; rewrite (ord1 (col _)).
- move=> m m3 h; have [i [c hc]] := h (fun _ => ord0).
  by have := g237_mono_copy_card hc; rewrite !card_ord leqNgt m3.
Qed.

(** At most 'C(n, 2) edges on n vertices. *)
Lemma g237_edge_count_le (G : sgraph) (n : nat) : #|G| = n -> edge_count G <= 'C(n, 2).
Proof.
move=> e; rewrite -(edge_count_Kn n).
pose h (v : G) : 'K_n := cast_ord e (enum_rank v).
have hi : injective h by move=> x y /cast_ord_inj /enum_rank_inj.
apply: (@sub_card_edge G 'K_n h hi).
by move=> x y xy; rewrite /edge_rel /= (inj_eq hi) (sg_edgeNeq xy).
Qed.

(** Turan instances: K_5 is C_6-free with 10 edges, K_3 is K_{2,2}-free with 3 edges. *)
Lemma g237_turan_C6 : is_turan_number 5 (fun _ : 'I_1 => cycle_graph 6) 10.
Proof.
split.
- exists 'K_5; split; [by rewrite card_ord | by rewrite /D2tur.edge_count edge_count_Kn |].
  by move=> i [h hi _]; have := leq_card h hi; rewrite !card_ord.
- by move=> m' [G [hG <- _]]; exact: g237_edge_count_le hG.
Qed.

Lemma g237_turan_K22 : is_turan_number 3 (fun _ : 'I_1 => complete_multipartite_graph 2 2) 3.
Proof.
split.
- exists 'K_3; split; [by rewrite card_ord | by rewrite /D2tur.edge_count edge_count_Kn |].
  by move=> i [h hi _]; have := leq_card h hi; rewrite card_prod !card_ord.
- by move=> m' [G [hG <- _]]; exact: g237_edge_count_le hG.
Qed.

(** ** Row erdos:181 *)

Definition g237_hcube_hyp_claim : Prop :=
  x195_ramsey_number 2 (fun _ : 'I_1 => product_hypercube 1) 2 /\
  (hypercube_ramsey_linear_statement -> exists C : nat, 2 <= C * 2 ^ 1).

Theorem g237_hcube_hyp_inhabited : g237_hcube_hyp_claim.
Proof.
split; first exact: g237_Q1_ramsey.
by case=> C h; exists C; exact: h 1 2 g237_Q1_ramsey.
Qed.

(** Contract form: without the Ramsey hypothesis the bound fails (n = 0, R = C + 1). *)
Definition g237_hcube_no_ramsey : Prop := exists C : nat, forall n R : nat, R <= C * 2 ^ n.

Definition g237_hcube_ntt_claim : Prop :=
  ~ g237_hcube_no_ramsey /\ (g237_hcube_no_ramsey -> hypercube_ramsey_linear_statement).

Theorem g237_hcube_not_trivially_true : g237_hcube_ntt_claim.
Proof.
split.
- by case=> C h; have := h 0 C.+1; rewrite expn0 muln1 ltnn.
- by case=> C h; exists C => n R _; exact: h.
Qed.

(** ** Row erdos:1029 *)

Definition g237_diag_hyp_claim : Prop :=
  x195_ramsey_number 2 (fun _ : 'I_1 => 'K_2) 2 /\
  (diagonal_ramsey_ratio_unbounded_statement ->
     exists k0 : nat, forall k R : nat, k0 <= k ->
       x195_ramsey_number 2 (fun _ : 'I_1 => 'K_k) R -> 1 ^ 2 * k ^ 2 * 2 ^ k <= R ^ 2).

Theorem g237_diag_hyp_inhabited : g237_diag_hyp_claim.
Proof. by split; [exact: g237_K2_ramsey | move=> h; exact: h 1]. Qed.

(** Contract form: without the Ramsey hypothesis the bound fails (M = 1, R = 0). *)
Definition g237_diag_no_ramsey : Prop :=
  forall M : nat, exists k0 : nat, forall k R : nat, k0 <= k -> M ^ 2 * k ^ 2 * 2 ^ k <= R ^ 2.

Definition g237_diag_ntt_claim : Prop :=
  ~ g237_diag_no_ramsey /\ (g237_diag_no_ramsey -> diagonal_ramsey_ratio_unbounded_statement).

Theorem g237_diag_not_trivially_true : g237_diag_ntt_claim.
Proof.
split.
- move=> h; have [k0 hk] := h 1; have := hk k0.+1 0 (leqnSn k0).
  by rewrite exp1n mul1n exp0n // leqn0 muln_eq0 !expn_eq0.
- by move=> h M; have [k0 hk] := h M; exists k0 => k R kk _; exact: hk.
Qed.

(** ** Row studies:std_schur_erd_s_problem *)

Definition g237_schur_hyp_claim : Prop :=
  [/\ 3 <= 3, 1 <= 1, x195_ramsey_number 1 (fun _ : 'I_1 => 'K_3) 3 &
      (multicolour_clique_ramsey_exponential_statement -> exists C : nat, 3 <= C ^ 1)].

Theorem g237_schur_hyp_inhabited : g237_schur_hyp_claim.
Proof.
split=> //; first exact: g237_K3_one_colour.
by move=> h; have [C hC] := h 3 (leqnn 3); exists C; exact: hC 1 3 (leqnn 1) g237_K3_one_colour.
Qed.

(** Contract form: without the Ramsey hypothesis the bound fails (m = 1, R = C + 1). *)
Definition g237_schur_no_ramsey : Prop :=
  forall p : nat, 3 <= p -> exists C : nat, forall m R : nat, 1 <= m -> R <= C ^ m.

Definition g237_schur_ntt_claim : Prop :=
  ~ g237_schur_no_ramsey /\ (g237_schur_no_ramsey -> multicolour_clique_ramsey_exponential_statement).

Theorem g237_schur_not_trivially_true : g237_schur_ntt_claim.
Proof.
split.
- by move=> h; have [C hC] := h 3 (leqnn 3); have := hC 1 C.+1 (leqnn 1); rewrite expn1 ltnn.
- by move=> h p p3; have [C hC] := h p p3; exists C => m R m1 _; exact: hC.
Qed.

(** ** Row erdos:572 *)

Definition g237_c2k_hyp_claim : Prop :=
  [/\ 3 <= 3, is_turan_number 5 (fun _ : 'I_1 => cycle_graph (2 * 3)) 10 &
      (even_cycle_turan_lower_statement ->
         exists a b n0 : nat, [/\ 0 < a, 0 < b & n0 <= 5 -> a ^ 3 * 5 ^ 4 <= (b * 10) ^ 3])].

Theorem g237_c2k_hyp_inhabited : g237_c2k_hyp_claim.
Proof.
split=> //; first exact: g237_turan_C6.
move=> h; have [a [b [n0 [a0 b0 hb]]]] := h 3 (leqnn 3).
by exists a, b, n0; split=> // n05; exact: hb 5 10 n05 g237_turan_C6.
Qed.

(** Contract form: without the Turan hypothesis the bound fails (m = 0). *)
Definition g237_c2k_no_turan : Prop :=
  forall k : nat, 3 <= k -> exists a b n0 : nat, [/\ 0 < a, 0 < b &
    forall n m : nat, n0 <= n -> a ^ k * n ^ k.+1 <= (b * m) ^ k].

Definition g237_c2k_ntt_claim : Prop :=
  ~ g237_c2k_no_turan /\ (g237_c2k_no_turan -> even_cycle_turan_lower_statement).

Theorem g237_c2k_not_trivially_true : g237_c2k_ntt_claim.
Proof.
split.
- move=> h; have [a [b [n0 [a0 _ hb]]]] := h 3 (leqnn 3); have := hb n0.+1 0 (leqnSn n0).
  by rewrite muln0 exp0n // leqn0 muln_eq0 !expn_eq0 eqn0Ngt a0.
- move=> h k k3; have [a [b [n0 [a0 b0 hb]]]] := h k k3.
  by exists a, b, n0; split=> // n m nn _; exact: hb.
Qed.

(** ** Row erdos:714 *)

Definition g237_krr_hyp_claim : Prop :=
  [/\ 2 <= 2, is_turan_number 3 (fun _ : 'I_1 => complete_multipartite_graph 2 2) 3 &
      (complete_bipartite_turan_lower_statement ->
         exists a b n0 : nat, [/\ 0 < a, 0 < b & n0 <= 3 -> a ^ 2 * 3 ^ (2 * 2) <= (b * 3) ^ 2 * 3])].

Theorem g237_krr_hyp_inhabited : g237_krr_hyp_claim.
Proof.
split=> //; first exact: g237_turan_K22.
move=> h; have [a [b [n0 [a0 b0 hb]]]] := h 2 (leqnn 2).
by exists a, b, n0; split=> // n03; exact: hb 3 3 n03 g237_turan_K22.
Qed.

(** Contract form: without the Turan hypothesis the bound fails (m = 0). *)
Definition g237_krr_no_turan : Prop :=
  forall r : nat, 2 <= r -> exists a b n0 : nat, [/\ 0 < a, 0 < b &
    forall n m : nat, n0 <= n -> a ^ r * n ^ (2 * r) <= (b * m) ^ r * n].

Definition g237_krr_ntt_claim : Prop :=
  ~ g237_krr_no_turan /\ (g237_krr_no_turan -> complete_bipartite_turan_lower_statement).

Theorem g237_krr_not_trivially_true : g237_krr_ntt_claim.
Proof.
split.
- move=> h; have [a [b [n0 [a0 _ hb]]]] := h 2 (leqnn 2); have := hb n0.+1 0 (leqnSn n0).
  by rewrite muln0 exp0n // mul0n leqn0 muln_eq0 !expn_eq0 eqn0Ngt a0.
- move=> h r r2; have [a [b [n0 [a0 b0 hb]]]] := h r r2.
  by exists a, b, n0; split=> // n m nn _; exact: hb.
Qed.

(** ** Forests, triangles and edge counts (row Kuperwasser-Samotij-Wigderson) *)

(** A triangle is a K_3 subgraph. *)
Lemma g237_tri_sub (G : sgraph) (x y z : G) : x -- y -> y -- z -> z -- x -> subgraph 'K_3 G.
Proof.
move=> xy yz zx; have nxy := sg_edgeNeq xy; have nyz := sg_edgeNeq yz; have nzx := sg_edgeNeq zx.
exists (fun i : 'K_3 => nth x [:: x; y; z] i).
- move=> [[|[|[|i]]] hi] [[|[|[|j]]] hj] //= e;
    first [by apply: val_inj | by move: nxy; rewrite e eqxx | by move: nyz; rewrite e eqxx
          | by move: nzx; rewrite e eqxx | by move: nxy; rewrite -e eqxx
          | by move: nyz; rewrite -e eqxx | by move: nzx; rewrite -e eqxx].
- by move=> [[|[|[|i]]] hi] [[|[|[|j]]] hj] //= _ _; rewrite sg_sym.
Qed.

(** A forest contains no triangle (K3_free_forest), and two vertices make a forest. *)
Lemma g237_forest_no_triangle (G : sgraph) (x y z : G) :
  is_forest [set: G] -> x -- y -> y -- z -> z -- x -> False.
Proof.
move=> hf xy yz zx; apply: (proj2 (minor.K3_free_forest G) hf).
exact: minor.sub_minor (g237_tri_sub xy yz zx).
Qed.

Lemma g237_small_forest (G : sgraph) : #|G| <= 2 -> is_forest [set: G].
Proof.
move=> h2; apply/minor.K3_free_forest => /minor_card.
by rewrite card_ord => h3; have := leq_trans h3 h2.
Qed.

(** The whole vertex set, as an induced subgraph, keeps every edge; induced sets keep their size. *)
Lemma g237_edges_inducedT (G : sgraph) : #|E(G)| <= #|E(induced [set: G])|.
Proof.
pose h (x : G) : induced [set: G] := Sub x (in_setT x).
have hi : injective h by move=> x y /(congr1 val).
exact: (@sub_card_edge G (induced [set: G]) h hi).
Qed.

Lemma g237_card_induced (G : sgraph) (S : {set G}) : #|induced S| = #|S|.
Proof. by rewrite card_sig. Qed.

(** Two disjoint triangles on 'I_2 * 'I_3. *)
Definition g237_two_triangles : sgraph := fg_mk_sgraph (fun x y : 'I_2 * 'I_3 => x.1 == y.1).

(** A forest misses an edge of each triangle. *)
Lemma g237_tri_edge_left (F : {set {set g237_two_triangles}}) (t : 'I_2) :
  x237_forest_edges F -> exists i j : 'I_3, i != j /\ [set ((t, i) : g237_two_triangles); (t, j)] \notin F.
Proof.
case=> _ hf.
pose o1 : 'I_3 := Ordinal (isT : 1 < 3).
pose o2 : 'I_3 := Ordinal (isT : 2 < 3).
case: (boolP ([set ((t, ord0) : g237_two_triangles); (t, o1)] \in F)) => h01; last by exists ord0, o1.
case: (boolP ([set ((t, o1) : g237_two_triangles); (t, o2)] \in F)) => h12; last by exists o1, o2.
case: (boolP ([set ((t, o2) : g237_two_triangles); (t, ord0)] \in F)) => h20; last by exists o2, ord0.
exfalso.
apply: (@g237_forest_no_triangle (del_edge_set g237_two_triangles (E(g237_two_triangles) :\: F))
          (t, ord0) (t, o1) (t, o2) hf).
all: by rewrite del_edge_setE !inE ?h01 ?h12 ?h20 /= andbT;
  rewrite /edge_rel /= /fg_srel eqxx orbT andbT xpair_eqE eqxx /=.
Qed.

(** So G - F keeps two edges, and the six-vertex set violates m_2 <= 1/5: 5 * 2 + 2 > 6 + 5. *)
Lemma g237_two_triangles_bad (F : {set {set g237_two_triangles}}) :
  x237_forest_edges F -> ~ x237_two_density_at_most (del_edge_set g237_two_triangles F) 1 5.
Proof.
move=> hF h2.
pose o1 : 'I_2 := Ordinal (isT : 1 < 2).
have [i0 [j0 [ij0 n0]]] := g237_tri_edge_left ord0 hF.
have [i1 [j1 [ij1 n1]]] := g237_tri_edge_left o1 hF.
set e0 : {set g237_two_triangles} := [set (ord0, i0); (ord0, j0)].
set e1 : {set g237_two_triangles} := [set (o1, i1); (o1, j1)].
have he0 : e0 \in E(del_edge_set g237_two_triangles F).
  rewrite edges_del_edge_set inE n0 /=.
  apply/(@edgesP g237_two_triangles); exists (ord0, i0), (ord0, j0); split=> //.
  by rewrite /edge_rel /= /fg_srel eqxx orbT andbT xpair_eqE eqxx /=.
have he1 : e1 \in E(del_edge_set g237_two_triangles F).
  rewrite edges_del_edge_set inE n1 /=.
  apply/(@edgesP g237_two_triangles); exists (o1, i1), (o1, j1); split=> //.
  by rewrite /edge_rel /= /fg_srel eqxx orbT andbT xpair_eqE eqxx /=.
have ne : e0 != e1.
  apply/negP => /eqP e; have : ((ord0, i0) : g237_two_triangles) \in e1 by rewrite -e !inE eqxx.
  by rewrite !inE !xpair_eqE.
have c2 : 2 <= #|E(del_edge_set g237_two_triangles F)|.
  have := cards2 e0 e1; rewrite ne => <-.
  by apply: subset_leq_card; apply/subsetP => e; rewrite !inE => /orP [] /eqP ->.
have c6 : #|[set: del_edge_set g237_two_triangles F]| = 6 by rewrite cardsT card_prod !card_ord.
have := h2 [set: del_edge_set g237_two_triangles F]; rewrite c6 => /(_ isT).
have ec := leq_trans c2 (g237_edges_inducedT _); move=> h.
have : 5 * 2 + 2 * 1 <= 1 * 6 + 5 by apply: leq_trans h; rewrite leq_add2r leq_mul2l; exact: ec.
by [].
Qed.

(** Helper instances. *)
Lemma g237_K2_density : x233_max_density_at_most 'K_2 1 1.
Proof.
move=> S; rewrite !mul1n.
have hS : #|S| <= 2 by have := max_card S; rewrite card_ord.
apply: leq_trans (g237_edge_count_le (g237_card_induced S)) _.
by move: hS; case: #|S| => [|[|[|s]]].
Qed.

Lemma g237_K2_two_density : x237_two_density_at_most 'K_2 1 1.
Proof. by move=> S h3; have := max_card S; rewrite card_ord => h2; have := leq_trans h3 h2. Qed.

Lemma g237_K3_not_two_density : ~ x237_two_density_at_most 'K_3 1 1.
Proof.
move=> h; have := h [set: 'K_3]; rewrite cardsT card_ord => /(_ isT).
have e3 := leq_trans (eq_leq (esym card_sg_edge_set_K3)) (g237_edges_inducedT 'K_3).
move=> h'; have : 1 * 3 + 2 * 1 <= 1 * 3 + 1 by apply: leq_trans h'; rewrite leq_add2r leq_mul2l; exact: e3.
by [].
Qed.

Lemma g237_K2_forest_edges : x237_forest_edges (E('K_2)).
Proof. by split=> //; apply: g237_small_forest; rewrite card_ord. Qed.

Lemma g237_K3_not_forest_edges : ~ x237_forest_edges (E('K_3)).
Proof.
case=> _; rewrite setDv => hf.
pose o1 : 'K_3 := Ordinal (isT : 1 < 3).
pose o2 : 'K_3 := Ordinal (isT : 2 < 3).
apply: (@g237_forest_no_triangle (del_edge_set 'K_3 set0) ord0 o1 o2 hf);
  by rewrite del_edge_setE inE andbT.
Qed.

(** ** helper_sanity (shared by the six rows) *)

Definition g237_ksw_helpers_claim : Prop :=
  [/\ x237_two_density_at_most 'K_2 1 1, ~ x237_two_density_at_most 'K_3 1 1,
      x237_forest_edges (E('K_2)) & ~ x237_forest_edges (E('K_3))].

Theorem g237_ksw_helpers_sanity : g237_ksw_helpers_claim.
Proof.
split; [exact: g237_K2_two_density | exact: g237_K3_not_two_density
       | exact: g237_K2_forest_edges | exact: g237_K3_not_forest_edges].
Qed.

(** ** Row studies:std_kuperwasser_samotij_wigderson_conjecture *)

Definition g237_ksw_hyp_claim : Prop :=
  x233_max_density_at_most 'K_2 1 1 /\
  (forest_removal_two_density_statement ->
     exists F : {set {set 'K_2}}, x237_forest_edges F /\ x237_two_density_at_most (del_edge_set 'K_2 F) 1 1).

Theorem g237_ksw_hyp_inhabited : g237_ksw_hyp_claim.
Proof. by split; [exact: g237_K2_density | move=> h; exact: h 1 1 'K_2 isT isT g237_K2_density]. Qed.

(** Contract form (Arthur's (135) b): without "m(G) <= m" the row fails at m = 1/5 for two
    disjoint triangles. *)
Definition g237_ksw_no_density : Prop :=
  forall (a b : nat) (G : sgraph), 0 < a -> 0 < b ->
    exists F : {set {set G}}, x237_forest_edges F /\ x237_two_density_at_most (del_edge_set G F) a b.

Definition g237_ksw_ntt_claim : Prop :=
  ~ g237_ksw_no_density /\ (g237_ksw_no_density -> forest_removal_two_density_statement).

Theorem g237_ksw_not_trivially_true : g237_ksw_ntt_claim.
Proof.
split.
- move=> h; have [F [hF h2]] := h 1 5 g237_two_triangles isT isT.
  exact: g237_two_triangles_bad hF h2.
- by move=> h a b G a0 b0 _; exact: h.
Qed.

(** * GTMisc.conjectures.grounding_X274 -- grounding certificates for wave X274 (2026-10-31)

    For each of the three rows: hyp_inhabited (the body's conditions hold at a small instance, and the statement
    gives its consequence) and not_trivially_true (a variant is false and implies the statement).  X274.v has no
    local helper, so there is no helper_sanity certificate.
    - Kalai-Meshulam: K_2 is ternary (it has no cycle at all), and the statement gives its parity bound.  Without
      "ternary" the row is false: K_3 has one even stable set (the empty set) and three odd ones (the vertices).
    - Linear arboricity: Delta(K_2) = 1, one colour, and the statement gives a colouring of K_2.  The row has no
      hypothesis; the variant is the ceil(Delta / 2) bound (every edge coloured below ceil(Delta / 2)), STRICTLY
      STRONGER than the row (a colouring with fewer colours is one with more colours, the extra classes empty), and
      K_3 refutes it: Delta = 2 leaves one colour, and a triangle is not a forest.  Every edgeless graph, the empty
      graph and K_1 included, satisfies the variant, so the refutation is K_3's, not an empty palette's.
    - Walther-Zamfirescu: K_1 is connected, and the statement gives a transversal of its longest paths.  Without
      "connected" the row is false for every c: the edgeless graph on c + 1 vertices has c + 1 pairwise disjoint
      longest paths (its vertices). *)

From GTBase Require Import base induced_cycles edge_colourings path_trees.
From GTMisc.conjectures Require Import X274.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** studies:std_kalai_meshulam_conjecture ********************************* *)

(** K_2 is ternary: an induced cycle on k >= 3 vertices would inject 'I_k into the two vertices. *)
Lemma g274_K2_ternary (k : nat) : 3 <= k -> 3 %| k -> ~ has_ordinal_induced_cycle 'K_2 k.
Proof.
move=> k3 _ [f [inj _]]; have := leq_card f inj; rewrite !card_ord => le.
by have := leq_trans k3 le.
Qed.

(** Every stable set of K_3 has at most one vertex. *)
Lemma g274_K3_stable (A : {set 'K_3}) : stable A -> #|A| <= 1.
Proof.
move=> st; rewrite leqNgt; apply/negP => /card_gt1P [x [y [xA yA xy]]].
by move/stableP: st => /(_ x y xA yA); rewrite /edge_rel /= xy.
Qed.

Lemma g274_K3_even (A : {set 'K_3}) : stable A -> ~~ odd #|A| -> A = set0.
Proof.
move=> st ev; apply/eqP; rewrite -cards_eq0; move: (g274_K3_stable st) ev.
by case: #|A| => [|[|]].
Qed.

(** K_3 has at most one even stable set ... *)
Lemma g274_K3_e : #|[set A : {set 'K_3} | stable A && ~~ odd #|A|]| <= 1.
Proof.
apply: (@leq_trans #|[set (set0 : {set 'K_3})]|); last by rewrite cards1.
apply: subset_leq_card; apply/subsetP => A.
by rewrite !inE => /andP [st ev]; rewrite (g274_K3_even st ev).
Qed.

Lemma g274_set1_stable (G : sgraph) (x : G) : stable [set x].
Proof. by apply/stableP => u v; rewrite !inE => /eqP -> /eqP ->; rewrite sg_irrefl. Qed.

(** ... and at least three odd ones, its singletons. *)
Lemma g274_K3_o : 3 <= #|[set A : {set 'K_3} | stable A && odd #|A|]|.
Proof.
pose S1 : {set {set 'K_3}} := [set [set x] | x : 'K_3].
have c3 : #|S1| = 3 by rewrite card_imset ?card_ord //; exact: set1_inj.
have sub : S1 \subset [set A : {set 'K_3} | stable A && odd #|A|].
  by apply/subsetP => A /imsetP [x _ ->]; rewrite !inE g274_set1_stable cards1.
by have := subset_leq_card sub; rewrite c3.
Qed.

(** hyp_inhabited: K_2 is ternary, and the statement gives its parity bound. *)
Definition g274_km_hyp_claim : Prop :=
  (forall k : nat, 3 <= k -> 3 %| k -> ~ has_ordinal_induced_cycle 'K_2 k) /\
  (kalai_meshulam_even_odd_stable_sets_statement ->
     let e := #|[set A : {set 'K_2} | stable A && ~~ odd #|A|]| in
     let o := #|[set A : {set 'K_2} | stable A && odd #|A|]| in
     e <= o.+1 /\ o <= e.+1).

Theorem g274_km_hyp_inhabited : g274_km_hyp_claim.
Proof. by split; [exact: g274_K2_ternary | move=> h; exact: h 'K_2 g274_K2_ternary]. Qed.

(** not_trivially_true: without "ternary" the statement is false (K_3: one even stable set, three odd). *)
Definition g274_km_no_ternary : Prop :=
  forall G : sgraph,
    let e := #|[set A : {set G} | stable A && ~~ odd #|A|]| in
    let o := #|[set A : {set G} | stable A && odd #|A|]| in
    e <= o.+1 /\ o <= e.+1.

Definition g274_km_ntt_claim : Prop :=
  ~ g274_km_no_ternary /\ (g274_km_no_ternary -> kalai_meshulam_even_odd_stable_sets_statement).

Theorem g274_km_not_trivially_true : g274_km_ntt_claim.
Proof.
split; last by move=> h G _; exact: h.
move=> h; have [_ oe] := h 'K_3.
have := leq_trans g274_K3_o oe; rewrite ltnS => e2.
by have := leq_trans e2 g274_K3_e.
Qed.

(** ** studies:std_linear_arboricity_conjecture ****************************** *)

Lemma g274_N_Kn (n : nat) (v : 'K_n.+1) : #|N(v)| = n.
Proof.
have -> : N(v) = [set~ v] by apply/setP => w; rewrite !inE /edge_rel /= eq_sym.
by rewrite cardsC1 card_ord.
Qed.

(** The maximum degree of K_(n+1) is n. *)
Lemma g274_Delta_Kn (n : nat) : Delta 'K_n.+1 = n.
Proof.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- by apply/bigmax_leqP => v _; rewrite g274_N_Kn.
- by apply: leq_trans (leq_bigmax ord0); rewrite g274_N_Kn.
Qed.

(** hyp_inhabited: Delta(K_2) = 1, so one colour, and the statement gives a colouring of K_2. *)
Definition g274_la_hyp_claim : Prop :=
  [/\ Delta 'K_2 = 1, ceil_div (Delta 'K_2 + 1) 2 = 1 &
      (linear_arboricity_conjecture_statement ->
         exists col : {set 'K_2} -> 'I_(ceil_div (Delta 'K_2 + 1) 2),
           forall i, linear_forest (edge_colour_class col (pred1 i)))].

Theorem g274_la_hyp_inhabited : g274_la_hyp_claim.
Proof. by split; [exact: g274_Delta_Kn | rewrite g274_Delta_Kn | move=> h; exact: h 'K_2]. Qed.

Definition g274_t1 : 'I_3 := @Ordinal 3 1 isT.

(** The ceil(Delta / 2) variant: the same palette, every edge coloured below ceil(Delta / 2).  It is strictly
    stronger than the statement (the colouring itself witnesses the statement, the classes of the unused colours
    being edgeless), and every edgeless graph satisfies it. *)
Definition g274_la_half : Prop :=
  forall G : sgraph,
    exists col : {set G} -> 'I_(ceil_div (Delta G + 1) 2),
      (forall e, e \in E(G) -> val (col e) < ceil_div (Delta G) 2) /\
      forall i, linear_forest (edge_colour_class col (pred1 i)).

(** K_3 refutes the variant: Delta = 2 leaves one colour for the three edges, and a forest on three vertices has a
    non-adjacent pair. *)
Lemma g274_la_half_K3 : ~ g274_la_half.
Proof.
move=> h; have [col [lt cl]] := h 'K_3.
have b : ceil_div (Delta 'K_3) 2 = 1 by rewrite g274_Delta_Kn.
have t01 : (ord0 : 'K_3) -- g274_t1 by [].
have one : forall x y : ('K_3), x -- y -> col [set x; y] = col [set ord0; g274_t1].
  move=> x y xy; apply: val_inj.
  have l1 := lt [set x; y]; have l2 := lt [set ord0; g274_t1]; rewrite !in_edges in l1 l2.
  by move: (l1 xy) (l2 t01); rewrite b !ltnS !leqn0 => /eqP -> /eqP ->.
have /linear_forest_forest Hf := cl (col [set ord0; g274_t1]).
have card3 : 3 <= #|edge_colour_class col (pred1 (col [set ord0; g274_t1]))| by rewrite card_ord.
have [x [y [xy nadj]]] := forest3 Hf card3.
have xyK : @edge_rel 'K_3 x y by rewrite /edge_rel /= xy.
by move: nadj; rewrite edge_colour_classE xyK (one x y xyK) /= eqxx.
Qed.

(** not_trivially_true: the ceil(Delta / 2) variant is false (K_3) and implies the statement. *)
Definition g274_la_ntt_claim : Prop :=
  ~ g274_la_half /\ (g274_la_half -> linear_arboricity_conjecture_statement).

Theorem g274_la_not_trivially_true : g274_la_ntt_claim.
Proof.
split; first exact: g274_la_half_K3.
by move=> h G; have [col [_ cl]] := h G; exists col.
Qed.

(** ** studies:std_walther_zamfirescu_longest_path_transversal_ques ********** *)

Lemma g274_K1_connected : connected [set: 'K_1].
Proof. by move=> x y _ _; rewrite (ord1 x) (ord1 y); exact: connect0. Qed.

(** hyp_inhabited: K_1 is connected, and the statement gives a transversal of its longest paths. *)
Definition g274_wz_hyp_claim : Prop :=
  connected [set: 'K_1] /\
  (walther_zamfirescu_bounded_longest_path_transversal_statement ->
     exists c : nat, 0 < c /\ exists T : {set 'K_1}, #|T| <= c /\
       forall (x : 'K_1) (p : seq 'K_1), path (@sedge 'K_1) x p -> uniq (x :: p) ->
         (forall (x' : 'K_1) (p' : seq 'K_1), path (@sedge 'K_1) x' p' -> uniq (x' :: p') -> size p' <= size p) ->
         exists2 v, v \in T & v \in x :: p).

Theorem g274_wz_hyp_inhabited : g274_wz_hyp_claim.
Proof.
split; first exact: g274_K1_connected.
by move=> [c [c0 h]]; exists c; split=> //; exact: h _ g274_K1_connected.
Qed.

(** The edgeless graph on n vertices: every vertex alone is a longest path. *)
Definition g274_edgeless (n : nat) : sgraph :=
  @SGraph 'I_n (fun _ _ => false) (fun _ _ => erefl) (fun _ => erefl).

Lemma g274_edgeless_path (n : nat) (x : g274_edgeless n) (p : seq (g274_edgeless n)) :
  path (@sedge _) x p -> p = [::].
Proof. by case: p. Qed.

(** not_trivially_true: without "connected" the statement is false for every c (the edgeless graph on c + 1
    vertices). *)
Definition g274_wz_no_conn : Prop :=
  exists c : nat, 0 < c /\
    forall G : sgraph,
      exists T : {set G}, #|T| <= c /\
        forall (x : G) (p : seq G), path (@sedge G) x p -> uniq (x :: p) ->
          (forall (x' : G) (p' : seq G), path (@sedge G) x' p' -> uniq (x' :: p') -> size p' <= size p) ->
          exists2 v, v \in T & v \in x :: p.

Definition g274_wz_ntt_claim : Prop :=
  ~ g274_wz_no_conn /\ (g274_wz_no_conn -> walther_zamfirescu_bounded_longest_path_transversal_statement).

Theorem g274_wz_not_trivially_true : g274_wz_ntt_claim.
Proof.
split; last by move=> [c [c0 h]]; exists c; split=> // G _; exact: h.
move=> [c [c0 h]]; have [T [Tc hT]] := h (g274_edgeless c.+1).
have sub : [set: g274_edgeless c.+1] \subset T.
  apply/subsetP => x _.
  have [v vT] := hT x [::] isT isT (fun x' p' pp _ => eq_leq (congr1 size (g274_edgeless_path pp))).
  by rewrite inE => /eqP <-.
have := subset_leq_card sub; rewrite cardsT card_ord => le.
by have := leq_trans le Tc; rewrite ltnn.
Qed.

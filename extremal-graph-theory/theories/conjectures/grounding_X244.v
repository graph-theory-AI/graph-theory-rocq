(** * Extremal.conjectures.grounding_X244 -- grounding certificates of wave X244.

    For each of the five rows: hyp_inhabited (the hypotheses hold on a concrete instance, and the statement then
    yields its conclusion there) and not_trivially_true in the contract form of meta/EXPANSION_PLAN.md 4.4 (the row
    with a load-bearing hypothesis dropped is false, and that variant implies the row): "triangle-free" for
    erdos:134 and erdos:618 (g244_tri m: a triangle beside isolated vertices, every degree <= 3, meets the degree
    bound and keeps its triangle after any addition), "edge_count G = m" for erdos:127 (on 'K_1 the cut is empty),
    "not Ramsey for K_3" for erdos:925 (the stable sets of K_N have at most one vertex) and "n0 <= n" for erdos:76
    (K_3 with one pair coloured differently has no monochromatic triangle, while q = 2 asks for one).  The wave has
    no local helper, so no helper_sanity certificate.  Small instances: the edgeless complete_multipartite_graph 1 5
    (triangle-free, every degree 0), 'K_1 (no edge), 'K_2 (no triangle under any colouring), K_3 with a constant
    colouring (one monochromatic triangle). *)

From Extremal.foundations Require Import edge_colourings.
From Extremal.conjectures Require Import X244.
(* GTBase last, as in X244.v. *)
From GTBase Require Import base common graph_metric complete_multipartite_graphs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Small instances *)

Lemma g244_edgeless (n : nat) (x y : complete_multipartite_graph 1 n) : ~~ x -- y.
Proof. by rewrite complete_multipartite_edgeE (ord1 x.1) (ord1 y.1) eqxx. Qed.

Lemma g244_edgeless_deg (G : sgraph) (v : G) : (forall x y : G, ~~ x -- y) -> #|N(v)| = 0.
Proof.
by move=> noE; apply/eqP; rewrite cards_eq0; apply/eqP/setP => w; rewrite !inE; apply/negbTE; exact: noE.
Qed.

Lemma g244_edgeless_no_K3 (G : sgraph) : (forall x y : G, ~~ x -- y) -> ~ has_subgraph G 'K_3.
Proof.
move=> noE /has_subgraphP [f [_ hf]].
by have := hf ord0 (Ordinal (isT : 1 < 3)) isT; rewrite (negbTE (noE _ _)).
Qed.

(** Adding edges keeps every subgraph. *)
Lemma g244_add_edges_sub (G H : sgraph) (X : {set {set G}}) :
  has_subgraph G H -> has_subgraph (compl (del_edge_set (compl G) X)) H.
Proof.
case/has_subgraphP => f [fi fh]; apply/has_subgraphP; exists f; split => // x y xy.
have := fh _ _ xy; rewrite compl_adjE del_edge_setE compl_adjE => fxy.
by rewrite (sg_edgeNeq fxy) fxy.
Qed.

(** A triangle on the vertices 0, 1, 2 of 'I_n.+3, all other vertices isolated. *)
Definition g244_tri_rel (n : nat) : rel 'I_n.+3 := fun i j => (i != j) && (i < 3) && (j < 3).

Lemma g244_tri_sym (n : nat) : symmetric (@g244_tri_rel n).
Proof. by move=> i j; rewrite /g244_tri_rel eq_sym; case: (i < 3); case: (j < 3); rewrite ?andbT ?andbF. Qed.

Lemma g244_tri_irrefl (n : nat) : irreflexive (@g244_tri_rel n).
Proof. by move=> i; rewrite /g244_tri_rel eqxx. Qed.

Definition g244_tri (n : nat) : sgraph := SGraph (@g244_tri_sym n) (@g244_tri_irrefl n).

Lemma g244_tri_K3 (n : nat) : has_subgraph (g244_tri n) 'K_3.
Proof.
apply/has_subgraphP; exists (fun i : 'K_3 => widen_ord (isT : 3 <= 3 + n) i : g244_tri n).
split; first by move=> i j /(congr1 val) /= /val_inj.
move=> i j ij; rewrite /edge_rel /= /g244_tri_rel /= (ltn_ord i) (ltn_ord j) !andbT.
by move: ij; rewrite /edge_rel /= -!(inj_eq val_inj).
Qed.

Lemma g244_tri_deg (n : nat) (v : g244_tri n) : #|N(v)| <= 3.
Proof.
apply: (@leq_trans #|[set widen_ord (isT : 3 <= 3 + n) i | i : 'I_3]|); last first.
  by apply: (leq_trans (leq_imset_card _ _)); rewrite card_ord.
apply/subset_leq_card/subsetP => w; rewrite !inE /edge_rel /= /g244_tri_rel => /andP [/andP [_ _] w3].
by apply/imsetP; exists (Ordinal w3) => //; apply/val_inj.
Qed.

Lemma g244_card_tri (n : nat) : #|g244_tri n| = n.+3.
Proof. exact: card_ord. Qed.

(** ** Rows erdos:134 and erdos:618 *)

(** The edgeless graph meets both degree hypotheses at every size; X = set0 is a valid addition set. *)
Definition g244_low_hyp_claim : Prop :=
  [/\ ~ has_subgraph (complete_multipartite_graph 1 5) ('K_3),
      (forall v : complete_multipartite_graph 1 5,
         #|N(v)| ^ (2 * 1) * #|complete_multipartite_graph 1 5| ^ 2 < #|complete_multipartite_graph 1 5| ^ 1) &
      (triangle_free_low_degree_diameter_two_completion_statement -> exists n0 : nat,
         forall G : sgraph, n0 <= #|G| -> ~ has_subgraph G 'K_3 ->
           (forall v : G, #|N(v)| ^ (2 * 1) * #|G| ^ 2 < #|G| ^ 1) ->
           exists X : {set {set G}},
             [/\ X \subset E(compl G), 1 * #|X| <= #|G| ^ 2,
                 ~ has_subgraph (compl (del_edge_set (compl G) X)) 'K_3 &
                 forall x y : compl (del_edge_set (compl G) X), graph_dist x y <= 2])].

Theorem g244_low_hyp_inhabited : g244_low_hyp_claim.
Proof.
split; [exact: g244_edgeless_no_K3 (@g244_edgeless 5) | | by move=> h; exact: h 1 1 isT isT].
by move=> v; rewrite (g244_edgeless_deg v (@g244_edgeless 5)) card_complete_multipartite_graph.
Qed.

Definition g244_low_no_tf : Prop :=
  forall q p : nat, 1 <= q -> 1 <= p -> exists n0 : nat,
    forall G : sgraph, n0 <= #|G| ->
      (forall v : G, #|N(v)| ^ (2 * q) * #|G| ^ 2 < #|G| ^ q) ->
      exists X : {set {set G}},
        [/\ X \subset E(compl G), p * #|X| <= #|G| ^ 2,
            ~ has_subgraph (compl (del_edge_set (compl G) X)) 'K_3 &
            forall x y : compl (del_edge_set (compl G) X), graph_dist x y <= 2].

Definition g244_low_ntt_claim : Prop :=
  ~ g244_low_no_tf /\ (g244_low_no_tf -> triangle_free_low_degree_diameter_two_completion_statement).

Theorem g244_low_not_trivially_true : g244_low_ntt_claim.
Proof.
split; last first.
  by move=> h q p q1 p1; have [n0 hn] := h q p q1 p1; exists n0 => G nG _; exact: hn.
move=> h; have [n0 hn] := h 3 1 isT isT.
have [|v|X [_ _ tf _]] := hn (g244_tri (n0 + 730)).
- rewrite g244_card_tri; apply: (@leq_trans (n0 + 730)); first exact: leq_addr.
  exact: leq_trans (leqnSn _) (leq_trans (leqnSn _) (leqnSn _)).
- rewrite g244_card_tri; have d := g244_tri_deg v; set N := (n0 + 730).+3.
  apply: (@leq_ltn_trans (3 ^ (2 * 3) * N ^ 2)); first by rewrite leq_mul2r leq_exp2r // d orbT.
  rewrite [N ^ 3]expnS ltn_mul2r expn_gt0 /N /=; apply: (@leq_trans 730) => //.
  apply: leq_trans (leq_addl n0 730) _; exact: leq_trans (leqnSn _) (leq_trans (leqnSn _) (leqnSn _)).
- exact: tf (g244_add_edges_sub X (g244_tri_K3 _)).
Qed.


Definition g244_sub_hyp_claim : Prop :=
  [/\ ~ has_subgraph (complete_multipartite_graph 1 5) ('K_3),
      (forall v : complete_multipartite_graph 1 5, (1 * #|N(v)|) ^ 2 <= #|complete_multipartite_graph 1 5|) &
      (triangle_free_sublinear_degree_diameter_two_completion_statement -> exists r n0 : nat, 1 <= r /\
         forall G : sgraph, n0 <= #|G| -> ~ has_subgraph G 'K_3 ->
           (forall v : G, (r * #|N(v)|) ^ 2 <= #|G|) ->
           exists X : {set {set G}},
             [/\ X \subset E(compl G), 1 * #|X| <= #|G| ^ 2,
                 ~ has_subgraph (compl (del_edge_set (compl G) X)) 'K_3 &
                 forall x y : compl (del_edge_set (compl G) X), graph_dist x y <= 2])].

Theorem g244_sub_hyp_inhabited : g244_sub_hyp_claim.
Proof.
split; [exact: g244_edgeless_no_K3 (@g244_edgeless 5) | | by move=> h; exact: h 1 isT].
by move=> v; rewrite (g244_edgeless_deg v (@g244_edgeless 5)) card_complete_multipartite_graph.
Qed.

Definition g244_sub_no_tf : Prop :=
  forall p : nat, 1 <= p -> exists r n0 : nat, 1 <= r /\
    forall G : sgraph, n0 <= #|G| ->
      (forall v : G, (r * #|N(v)|) ^ 2 <= #|G|) ->
      exists X : {set {set G}},
        [/\ X \subset E(compl G), p * #|X| <= #|G| ^ 2,
            ~ has_subgraph (compl (del_edge_set (compl G) X)) 'K_3 &
            forall x y : compl (del_edge_set (compl G) X), graph_dist x y <= 2].

Definition g244_sub_ntt_claim : Prop :=
  ~ g244_sub_no_tf /\ (g244_sub_no_tf -> triangle_free_sublinear_degree_diameter_two_completion_statement).

Theorem g244_sub_not_trivially_true : g244_sub_ntt_claim.
Proof.
split; last first.
  by move=> h p p1; have [r [n0 [r1 hn]]] := h p p1; exists r, n0; split => // G nG _; exact: hn.
move=> h; have [r [n0 [r1 hn]]] := h 1 isT.
have [|v|X [_ _ tf _]] := hn (g244_tri (n0 + (r * 3) ^ 2)).
- rewrite g244_card_tri; apply: (@leq_trans (n0 + (r * 3) ^ 2)); first exact: leq_addr.
  exact: leq_trans (leqnSn _) (leq_trans (leqnSn _) (leqnSn _)).
- rewrite g244_card_tri; apply: (@leq_trans ((r * 3) ^ 2)).
    by rewrite leq_exp2r // leq_mul2l g244_tri_deg orbT.
  apply: leq_trans (leq_addl n0 _) _; exact: leq_trans (leqnSn _) (leq_trans (leqnSn _) (leqnSn _)).
- exact: tf (g244_add_edges_sub X (g244_tri_K3 _)).
Qed.

(** ** Row erdos:127 *)

Definition g244_cut_hyp_claim : Prop :=
  [/\ edge_count 'K_1 = 0 &
      (bipartite_subgraph_edwards_excess_unbounded_statement -> exists m : nat, forall G : sgraph, edge_count G = m ->
         exists (A : {set G}) (X : nat),
           X + 4 * m + 8 * 0 = 8 * #|[set e in E(G) | #|e :&: A| == 1]| + 1 /\ 8 * m + 1 <= X ^ 2)].

Theorem g244_cut_hyp_inhabited : g244_cut_hyp_claim.
Proof. by split; [exact: (proj2 edge_count_K0_K1) | move=> h; exact: h 0]. Qed.

Definition g244_cut_no_count : Prop :=
  forall K : nat, exists m : nat,
    forall G : sgraph,
      exists (A : {set G}) (X : nat),
        X + 4 * m + 8 * K = 8 * #|[set e in E(G) | #|e :&: A| == 1]| + 1 /\ 8 * m + 1 <= X ^ 2.

Definition g244_cut_ntt_claim : Prop :=
  ~ g244_cut_no_count /\ (g244_cut_no_count -> bipartite_subgraph_edwards_excess_unbounded_statement).

Theorem g244_cut_not_trivially_true : g244_cut_ntt_claim.
Proof.
split; last first.
  by move=> h K; have [m hm] := h K; exists m => G _; exact: hm.
move=> h; have [m hm] := h 1; have [A [X [e _]]] := hm 'K_1.
have c0 : #|[set e in E('K_1) | #|e :&: A| == 1]| = 0.
  apply/eqP; rewrite -leqn0; apply: (@leq_trans #|E('K_1)|).
    by apply/subset_leq_card/subsetP => e'; rewrite inE => /andP [].
  by have := proj2 edge_count_K0_K1; rewrite /edge_count => ->.
by have := leq_addl (X + 4 * m) (8 * 1); rewrite e c0.
Qed.

(** ** Row erdos:925 *)

Lemma g244_no_K3_in_K2 (col : {set 'K_2} -> bool) (b : bool) : ~ mono_copy 'K_3 col b.
Proof. by case=> emb [inj _ _]; have := leq_card emb inj; rewrite !card_ord. Qed.

Definition g244_ram_hyp_claim : Prop :=
  [/\ (exists col : {set 'K_2} -> bool, forall b : bool, ~ mono_copy 'K_3 col b) &
      (not_triangle_ramsey_independent_set_exponent_statement -> exists q c n0 : nat, [/\ 1 <= q, 1 <= c &
         n0 <= #|'K_2| -> exists S : {set 'K_2}, stable S /\ #|'K_2| ^ (q + 3) <= (c * #|S|) ^ (3 * q)])].

Theorem g244_ram_hyp_inhabited : g244_ram_hyp_claim.
Proof.
split; first by exists (fun _ => true); exact: g244_no_K3_in_K2.
move=> [q [c [n0 [q1 c1 h]]]]; exists q, c, n0; split => // n2.
by apply: h n2 _; exists (fun _ => true); exact: g244_no_K3_in_K2.
Qed.

Lemma g244_Kn_stable (n : nat) (S : {set 'K_n}) : stable S -> #|S| <= 1.
Proof.
move=> st; apply/card_le1_eqP => x y xS yS; apply/eqP; apply: contraT => xy.
by move/stableP: st => /(_ x y xS yS); rewrite /edge_rel /= eq_sym xy.
Qed.

Definition g244_ram_no_hyp : Prop :=
  exists q c n0 : nat, [/\ 1 <= q, 1 <= c &
    forall G : sgraph, n0 <= #|G| ->
      exists S : {set G}, stable S /\ #|G| ^ (q + 3) <= (c * #|S|) ^ (3 * q)].

Definition g244_ram_ntt_claim : Prop :=
  ~ g244_ram_no_hyp /\ (g244_ram_no_hyp -> not_triangle_ramsey_independent_set_exponent_statement).

Theorem g244_ram_not_trivially_true : g244_ram_ntt_claim.
Proof.
split; last first.
  by move=> [q [c [n0 [q1 c1 h]]]]; exists q, c, n0; split => // G nG _; exact: h.
move=> [q [c [n0 [q1 c1 h]]]].
have [|S [st hS]] := h 'K_(n0 + c ^ (3 * q)).+1.
  by rewrite card_ord; apply: leq_trans (leq_addr _ _) (leqnSn _).
have s1 := g244_Kn_stable st.
move: hS; rewrite card_ord; set N := (n0 + c ^ (3 * q)).+1 => hS.
have e1 : (c * #|S|) ^ (3 * q) <= c ^ (3 * q).
  by rewrite leq_exp2r ?muln_gt0 //; have := leq_mul (leqnn c) s1; rewrite muln1.
have e2 : c ^ (3 * q) < N by rewrite /N ltnS leq_addl.
have e3 : N <= N ^ (q + 3) by rewrite -{1}[N]expn1; apply: leq_pexp2l => //; rewrite addn3.
by have := leq_ltn_trans (leq_trans (leq_trans e3 hS) e1) e2; rewrite ltnn.
Qed.


(** ** Row erdos:76 *)

Definition g244_mono_hyp_claim : Prop :=
  [/\ exists T : {set {set 'I_3}},
        [/\ forall t : {set 'I_3}, t \in T ->
              #|t| = 3 /\ exists b : bool, forall x y : 'I_3, x \in t -> y \in t -> x != y ->
                (fun _ : {set 'I_3} => true) [set x; y] = b,
            forall t u : {set 'I_3}, t \in T -> u \in T -> t != u -> #|t :&: u| <= 1 & 1 <= #|T|] &
      (two_colouring_edge_disjoint_monochromatic_triangles_statement -> exists n0 : nat,
         forall (n : nat) (col : {set 'I_n} -> bool), n0 <= n ->
           exists T : {set {set 'I_n}},
             [/\ forall t : {set 'I_n}, t \in T ->
                   #|t| = 3 /\ exists b : bool, forall x y : 'I_n, x \in t -> y \in t -> x != y -> col [set x; y] = b,
                 forall t u : {set 'I_n}, t \in T -> u \in T -> t != u -> #|t :&: u| <= 1 &
                 1 * n ^ 2 <= 12 * 1 * #|T| + n ^ 2])].

Theorem g244_mono_hyp_inhabited : g244_mono_hyp_claim.
Proof.
split; last by move=> h; exact: h 1 isT.
exists [set setT]; split; last by rewrite cards1.
- by move=> t; rewrite inE => /eqP ->; split; [rewrite cardsT card_ord | exists true].
- by move=> t u; rewrite !inE => /eqP -> /eqP ->; rewrite eqxx.
Qed.

Definition g244_mono_no_size : Prop :=
  forall q : nat, 1 <= q -> exists n0 : nat,
    forall (n : nat) (col : {set 'I_n} -> bool),
      exists T : {set {set 'I_n}},
        [/\ forall t : {set 'I_n}, t \in T ->
              #|t| = 3 /\ exists b : bool, forall x y : 'I_n, x \in t -> y \in t -> x != y -> col [set x; y] = b,
            forall t u : {set 'I_n}, t \in T -> u \in T -> t != u -> #|t :&: u| <= 1 &
            q * n ^ 2 <= 12 * q * #|T| + n ^ 2].

Definition g244_mono_ntt_claim : Prop :=
  ~ g244_mono_no_size /\ (g244_mono_no_size -> two_colouring_edge_disjoint_monochromatic_triangles_statement).

Theorem g244_mono_not_trivially_true : g244_mono_ntt_claim.
Proof.
split; last first.
  by move=> h q q1; have [n0 hn] := h q q1; exists n0 => n col _; exact: hn.
move=> h; have [n0 hn] := h 2 isT.
pose c3 := fun s : {set 'I_3} => s == [set ord0; Ordinal (isT : 1 < 3)].
have [T [hm _ hT]] := hn 3 c3.
have T0 : #|T| = 0.
  apply/eqP; rewrite cards_eq0; apply/eqP/setP => t; rewrite inE; apply/negP => tT.
  have [t3 [b hb]] := hm t tT.
  have tS : t = setT by apply/eqP; rewrite eqEcard subsetT cardsT card_ord t3.
  have e1 := hb ord0 (Ordinal (isT : 1 < 3)).
  have e2 := hb (Ordinal (isT : 1 < 3)) (Ordinal (isT : 2 < 3)).
  rewrite tS !inE in e1 e2.
  have f1 : c3 [set ord0; Ordinal (isT : 1 < 3)] = true by rewrite /c3 eqxx.
  have f2 : c3 [set Ordinal (isT : 1 < 3); Ordinal (isT : 2 < 3)] = false.
    by apply/negbTE/eqP => /setP /(_ (Ordinal (isT : 2 < 3))); rewrite !inE.
  by move: (e1 isT isT isT) (e2 isT isT isT); rewrite f1 f2 => <-.
by move: hT; rewrite T0.
Qed.


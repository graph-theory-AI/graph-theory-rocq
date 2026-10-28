(** * Extremal.conjectures.grounding_X252 -- grounding certificates of wave X252.

    For each of the three rows: hyp_inhabited (the hypotheses hold on a concrete instance, with a concrete Turan value
    where the row has a Turan hypothesis, and the statement then yields its conclusion there) and not_trivially_true in
    the contract form of meta/EXPANSION_PLAN.md 4.4 (a variant obtained from the body is false and implies the row):
    erdos:113 strengthened in one clause, "and G is 2-degenerate" (every bipartite graph would satisfy both sides),
    false at 'K_3,3 (bipartite, 3-regular, its whole vertex set induces minimum degree 3); erdos:1021 without its Turan
    hypothesis (n = 0, m = 1: 1 <= c * 0); erdos:1079 without its Turan hypothesis (m = 0 and the edgeless graph on two
    vertices: 2 <= c * 0).  No certificate needs a Turan number to exist in general (D2tur proves none): the concrete
    values are ex(1; G_3) = 0 ('K_1) and ex(2; K_4) = 1 ('K_2), as grounding_X245's ex(1; K_3) = 0.  The wave has no local
    helper, so no helper_sanity certificate. *)

From Extremal.conjectures Require Import D2tur grounding_X239 X252.
(* GTBase last: its canonical [edge_count] must shadow D2tur's eta-alias of the same name. *)
From GTBase Require Import base common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(** 'K_3,3 is bipartite (the side of a vertex is a proper 2-colouring). *)
Lemma g252_K33_bipartite : bipartite ('K_3,3).
Proof. by exists (fun x : 'K_3,3 => is_inl x) => [[a|a] [b|b]]. Qed.

(** 'K_3,3 is not 2-degenerate: its whole vertex set induces minimum degree 3. *)
Lemma g252_K33_not_2degenerate : ~ (forall S : {set 'K_3,3}, S != set0 -> ~ min_degree_at_least (induced S) 3).
Proof.
move=> h; apply: (h setT); first by apply/set0Pn; exists (inl ord0); rewrite inE.
move=> v.
have e : val @: N(v) = N(val v).
  apply/setP => w; apply/imsetP/idP => [[u uN ->]|wN].
    by move: uN; rewrite !inE.
  have wT : w \in [set: 'K_3,3] by rewrite inE.
  exists (Sub w wT : induced [set: 'K_3,3]) => //.
  by move: wN; rewrite !inE.
rewrite -(card_imset _ val_inj) e.
by case: (val v) => a; [rewrite deg_Knm_l | rewrite deg_Knm_r].
Qed.

(** hyp_inhabited: 'K_1 is bipartite; the statement then gives the biconditional there. *)
Definition g252_deg_hyp_claim : Prop :=
  bipartite ('K_1) /\
  (bipartite_three_halves_iff_two_degenerate_statement ->
     ((exists c : nat, forall n m : nat, is_turan_number n (fun _ : 'I_1 => 'K_1) m -> m ^ 2 <= c * n ^ 3) <->
      (forall S : {set 'K_1}, S != set0 -> ~ min_degree_at_least (induced S) 3))).

Theorem g252_deg_hyp_inhabited : g252_deg_hyp_claim.
Proof.
have b : bipartite ('K_1) by exists (fun _ => true) => x y; rewrite (ord1 x) (ord1 y) sg_irrefl.
by split => // h; exact: h _ b.
Qed.

(** not_trivially_true: the row plus the clause "G is 2-degenerate" (every bipartite graph would satisfy both sides)
    implies the row and fails at 'K_3,3. *)
Definition g252_deg_plus_two_degenerate : Prop :=
  forall G : sgraph, bipartite G ->
    ((exists c : nat, forall n m : nat, is_turan_number n (fun _ : 'I_1 => G) m -> m ^ 2 <= c * n ^ 3) <->
     (forall S : {set G}, S != set0 -> ~ min_degree_at_least (induced S) 3)) /\
    (forall S : {set G}, S != set0 -> ~ min_degree_at_least (induced S) 3).

Definition g252_deg_ntt_claim : Prop :=
  ~ g252_deg_plus_two_degenerate /\ (g252_deg_plus_two_degenerate -> bipartite_three_halves_iff_two_degenerate_statement).

Theorem g252_deg_not_trivially_true : g252_deg_ntt_claim.
Proof.
split; last by move=> h G bG; exact: (h G bG).1.
move=> h; have [_ hr] := h _ g252_K33_bipartite.
exact: g252_K33_not_2degenerate hr.
Qed.

(** not_trivially_true: without the Turan hypothesis the bound fails at n = 0, m = 1 (3q - 2 >= 1). *)
Definition g252_sd_no_turan : Prop :=
  forall k : nat, 3 <= k -> exists q c : nat, 1 <= q /\
    forall n m : nat, m ^ (2 * q) <= c * n ^ (3 * q - 2).

Definition g252_sd_ntt_claim : Prop :=
  ~ g252_sd_no_turan /\ (g252_sd_no_turan -> one_subdivision_clique_turan_power_saving_statement).

Theorem g252_sd_not_trivially_true : g252_sd_ntt_claim.
Proof.
split; last by move=> h k k3; have [q [c [q1 hb]]] := h k k3; exists q, c; split => // n m _; exact: hb.
move=> h; have [q [c [q1 hb]]] := h 3 (leqnn 3).
have := hb 0 1; rewrite exp1n exp0n ?muln0 //.
by rewrite ltn_subRL addn0; apply: (@leq_trans (3 * 1)); rewrite ?leq_mul2l.
Qed.

(** A concrete Turan value: ex(1; G_3) = 0 ('K_1 is G_3-free, as G_3 has more than one vertex). *)
Lemma g252_turan_sd_1 : is_turan_number 1 (fun _ : 'I_1 => subdivision 'K_3 2) 0.
Proof.
split.
- exists 'K_1; split; [by rewrite card_ord | by rewrite /D2tur.edge_count (proj2 edge_count_K0_K1) |].
  move=> i [h hi _].
  have e : h (inl ord0) = h (inl (Ordinal (isT : 1 < 3))) by rewrite (ord1 (h (inl ord0))) (ord1 (h (inl _))).
  by have := hi _ _ e.
- by move=> m' [G [hG <- _]]; exact: g239_edge_count_le hG.
Qed.

(** hyp_inhabited: k = 3 meets the guard and its Turan hypothesis has a value (ex(1; G_3) = 0); the statement then
    gives its bound there. *)
Definition g252_sd_hyp_claim : Prop :=
  [/\ 3 <= 3, is_turan_number 1 (fun _ : 'I_1 => subdivision 'K_3 2) 0 &
      (one_subdivision_clique_turan_power_saving_statement ->
         exists q c : nat, 1 <= q /\
           forall n m : nat, is_turan_number n (fun _ : 'I_1 => subdivision 'K_3 2) m -> m ^ (2 * q) <= c * n ^ (3 * q - 2))].

Theorem g252_sd_hyp_inhabited : g252_sd_hyp_claim.
Proof. by split; [| exact: g252_turan_sd_1 | move=> h; exact: h 3 (leqnn 3)]. Qed.

(** not_trivially_true: without the Turan hypothesis, m = 0 and the edgeless graph on two vertices (no vertex of
    positive degree) refute the bound; the variant implies the row. *)
Definition g252_nb_no_turan : Prop :=
  forall r : nat, 4 <= r -> exists c : nat, 1 <= c /\
    forall (G : sgraph) (m : nat), 2 <= #|G| -> m <= edge_count G ->
      exists v : G, #|G| <= c * #|N(v)| /\
        forall t : nat, is_turan_number #|N(v)| (fun _ : 'I_1 => 'K_(r - 1)) t -> t <= edge_count (induced N(v)).

Definition g252_nb_ntt_claim : Prop :=
  ~ g252_nb_no_turan /\ (g252_nb_no_turan -> turan_density_neighbourhood_turan_statement).

Theorem g252_nb_not_trivially_true : g252_nb_ntt_claim.
Proof.
split; last first.
  move=> h r r4; have [c [c1 hc]] := h r r4; exists c; split => // G m n2 _ me; exact: hc G m n2 me.
move=> h; have [c [c1 hc]] := h 4 (leqnn 4).
have n2 : 2 <= #|compl 'K_2| by rewrite card_ord.
have [v [hv _]] := hc (compl 'K_2) 0 n2 (leq0n _).
have N0 : N(v) = set0.
  by apply/setP => w; rewrite !inE (negbTE (compl_Kn_edgeless v w)).
by move: hv; rewrite N0 cards0 muln0 card_ord.
Qed.

(** A concrete Turan value: ex(2; K_4) = 1 ('K_2 is K_4-free; a graph on two vertices has at most one edge). *)
Lemma g252_turan_K4_2 : is_turan_number 2 (fun _ : 'I_1 => 'K_4) 1.
Proof.
split.
- exists 'K_2; split; [by rewrite card_ord | by rewrite /D2tur.edge_count edge_count_Kn |].
  by move=> i [h hi _]; have := leq_card h hi; rewrite !card_ord.
- by move=> m' [G [hG <- _]]; exact: g239_edge_count_le hG.
Qed.

(** hyp_inhabited: at r = 4, 'K_2 has two vertices, its Turan hypothesis has the value ex(2; K_4) = 1 and it has that
    many edges; the statement then yields its vertex there. *)
Definition g252_nb_hyp_claim : Prop :=
  [/\ 4 <= 4, 2 <= #|'K_2|, is_turan_number #|'K_2| (fun _ : 'I_1 => 'K_4) 1, 1 <= edge_count 'K_2 &
      (turan_density_neighbourhood_turan_statement ->
         exists c : nat, 1 <= c /\
           exists v : ('K_2), #|'K_2| <= c * #|N(v)| /\
             forall t : nat, is_turan_number #|N(v)| (fun _ : 'I_1 => 'K_(4 - 1)) t -> t <= edge_count (induced N(v)))].

Theorem g252_nb_hyp_inhabited : g252_nb_hyp_claim.
Proof.
have n2 : 2 <= #|'K_2| by rewrite card_ord.
have tv : is_turan_number #|'K_2| (fun _ : 'I_1 => 'K_4) 1 by rewrite card_ord; exact: g252_turan_K4_2.
have e1 : 1 <= edge_count 'K_2 by rewrite edge_count_Kn.
split => //.
move=> h; have [c [c1 hc]] := h 4 (leqnn 4); exists c; split => //.
exact: hc ('K_2) 1 n2 tv e1.
Qed.

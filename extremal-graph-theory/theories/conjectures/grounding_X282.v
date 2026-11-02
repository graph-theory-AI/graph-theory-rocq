(** * Extremal.conjectures.grounding_X282 -- grounding certificates of wave X282.

    For each of the three rows: hyp_inhabited (the hypotheses hold on a concrete instance, and the statement gives its
    consequence there) and not_trivially_true in the contract form (a variant obtained from the body by deleting one
    hypothesis or guard is false and implies the row); helper_sanity for [x282_ramsey_size_linear] in every row.
    - List Ramsey: on K_3 the constant colouring 1 avoids K_4 (three vertices), the constant lists {1, 2} are valid
      2-lists, and the statement gives an avoiding colouring from them.  Without the validity of the lists the row is
      false at n = 3 with the empty lists: no colouring picks the colour of an edge from an empty list.
    - Ramsey size-linear: K_1 is, with C = 1: a host with an edge count's worth of vertices contains K_1 when it has a
      vertex, and when it has none the graph H has no edge, hence (no isolated vertex) no vertex, and is a copy in the
      complement.
    - Erdos #79: the statement gives a non-Ramsey-size-linear graph with a vertex.  Without the properness bound the
      row is false: G is a subgraph of itself.
    - k-connected growth: f(n) = n meets the hypothesis (R(K_n) >= n, through the host K_R), and the statement gives
      2-connected graphs of every large order.  Without the threshold n0 the row is false at n = 0: a 2-connected
      graph has more than two vertices. *)

From Extremal.conjectures Require Import X282 X235 XE1.
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The helper: Ramsey size-linear *)

(** A graph with no isolated vertex and no edge has no vertex. *)
Lemma g282_no_isolated_empty (H : sgraph) :
  min_degree_at_least H 1 -> #|E(H)| = 0 -> #|H| = 0.
Proof.
move=> iso E0; apply/eqP; rewrite -leqn0 leqNgt; apply/negP => /card_gt0P [v _].
have /card_gt0P [u] := iso v; rewrite in_opn => vu.
have : [set v; u] \in E(H) by rewrite in_edges.
by move=> uvE; move: E0; rewrite (cardD1 [set v; u]) uvE.
Qed.

(** A graph with a vertex contains K_1. *)
Lemma g282_has_K1 (F : sgraph) : 0 < #|F| -> has_subgraph F ('K_1).
Proof.
move=> /card_gt0P [x _]; apply/has_subgraphP; exists (fun _ => x); split.
  by move=> a b _; rewrite (ord1 a) (ord1 b).
by move=> a b; rewrite (ord1 a) (ord1 b) sgP.
Qed.

Definition g282_rsl_helper_claim : Prop := x282_ramsey_size_linear ('K_1).

Theorem g282_rsl_helper_sanity : g282_rsl_helper_claim.
Proof.
exists 1 => H R iso [_ least]; rewrite mul1n; apply: least => F cF.
case: (posnP #|F|) => [F0|Fpos]; last by left; exact: g282_has_K1.
right; apply: has_subgraph0; apply: g282_no_isolated_empty iso _.
by rewrite cF in F0.
Qed.

(** ** Row 1: arxiv:1902.07018#01 *)

(** A colour class of a colouring of K_n has n vertices, so it holds no K_r for r > n. *)
Lemma g282_no_big_clique (n r : nat) (phi : 'I_n -> 'I_n -> nat) (c : nat) :
  n < r -> ~ has_subgraph (lr_color_graph phi c) ('K_r).
Proof. by move=> nr /has_subgraph_card; rewrite !card_ord leqNgt nr. Qed.

(** The constant colouring 1 of K_3 is a 2-colouring with no monochromatic K_4. *)
Lemma g282_K3_avoids :
  exists phi : 'I_3 -> 'I_3 -> nat,
    lr_nat_admissible (fun _ _ => [:: 1; 2]) phi /\
    forall c : nat, ~ has_subgraph (lr_color_graph phi c) ('K_4).
Proof. by exists (fun _ _ => 1); split=> // c; exact: g282_no_big_clique. Qed.

Definition g282_lr_hyp_claim : Prop :=
  [/\ 3 < 4,
      (exists phi : 'I_3 -> 'I_3 -> nat,
         lr_nat_admissible (fun _ _ => [:: 1; 2]) phi /\
         forall c : nat, ~ has_subgraph (lr_color_graph phi c) ('K_4)),
      lr_nat_valid_lists 2 (fun _ _ : 'I_3 => [:: 1; 2]) &
      (list_ramsey_two_colour_clique_equality_statement ->
         exists phi : 'I_3 -> 'I_3 -> nat,
           lr_nat_admissible (fun _ _ => [:: 1; 2]) phi /\
           forall c : nat, ~ has_subgraph (lr_color_graph phi c) ('K_4))].

Theorem g282_lr_hyp_inhabited : g282_lr_hyp_claim.
Proof.
have val : lr_nat_valid_lists 2 (fun _ _ : 'I_3 => [:: 1; 2]) by [].
split=> //; first exact: g282_K3_avoids.
move=> S; exact: S 4 3 isT g282_K3_avoids _ val.
Qed.

(** The variant without the validity of the lists. *)
Definition g282_lr_any_lists : Prop :=
  forall r n : nat, 3 < r ->
    (exists phi : 'I_n -> 'I_n -> nat,
       lr_nat_admissible (fun _ _ => [:: 1; 2]) phi /\
       forall c : nat, ~ has_subgraph (lr_color_graph phi c) ('K_r)) ->
    forall L : 'I_n -> 'I_n -> seq nat,
      exists phi : 'I_n -> 'I_n -> nat,
        lr_nat_admissible L phi /\ forall c : nat, ~ has_subgraph (lr_color_graph phi c) ('K_r).

Definition g282_lr_ntt_claim : Prop :=
  ~ g282_lr_any_lists /\ (g282_lr_any_lists -> list_ramsey_two_colour_clique_equality_statement).

Theorem g282_lr_not_trivially_true : g282_lr_ntt_claim.
Proof.
split; last by move=> h r n r3 hyp L _; exact: h.
move=> h; have [phi [[_ inL] _]] := h 4 3 isT g282_K3_avoids (fun _ _ => [::]).
have := inL ord0 (inord 1).
rewrite in_nil => H; suff : false by []; apply: H; by rewrite -val_eqE /= inordK.
Qed.

(** ** Row 2: erdos:79 *)

Definition g282_e79_hyp_claim : Prop :=
  x282_ramsey_size_linear ('K_1) /\
  (erdos_79_minimal_non_ramsey_size_linear_statement ->
     exists G : sgraph, 1 <= #|G| /\ ~ x282_ramsey_size_linear G).

Theorem g282_e79_hyp_inhabited : g282_e79_hyp_claim.
Proof.
split; first exact: g282_rsl_helper_sanity.
by move=> S; have [G [G1 nG _]] := S 1; exists G.
Qed.

(** The variant without the properness bound on the subgraphs. *)
Definition g282_e79_every_subgraph : Prop :=
  forall N : nat, exists G : sgraph,
    [/\ N <= #|G|, ~ x282_ramsey_size_linear G &
        forall H : sgraph, has_subgraph G H -> x282_ramsey_size_linear H].

Definition g282_e79_ntt_claim : Prop :=
  ~ g282_e79_every_subgraph /\
  (g282_e79_every_subgraph -> erdos_79_minimal_non_ramsey_size_linear_statement).

Theorem g282_e79_not_trivially_true : g282_e79_ntt_claim.
Proof.
split.
  by move=> h; have [G [_ nG all]] := h 0; exact: nG (all G (has_subgraph_refl G)).
by move=> h N; have [G [NG nG all]] := h N; exists G; split=> // H HG _; exact: all.
Qed.

(** ** Row 3: studies:std_pavez_sign_piga_sanhueza_matamala_conjecture_on *)

(** R(K_n) >= n: below n vertices, neither K_R nor its complement holds K_n. *)
Lemma g282_ramsey_Kn_ge (n R : nat) : xe1_diagonal_ramsey_number ('K_n) R -> n <= R.
Proof.
move=> [arrows _]; rewrite leqNgt; apply/negP => Rn.
have [h|h] := arrows ('K_R) (card_ord R); move: (has_subgraph_card h); rewrite !card_ord leqNgt Rn //.
Qed.

Lemma g282_id_growth (n R : nat) : xe1_diagonal_ramsey_number ('K_n) R -> n <= n <= R.
Proof. by move/g282_ramsey_Kn_ge => nR; rewrite leqnn. Qed.

Definition g282_kc_hyp_claim : Prop :=
  [/\ 2 <= 2,
      (forall n R : nat, xe1_diagonal_ramsey_number ('K_n) R -> n <= (fun m => m) n <= R) &
      (k_connected_ramsey_growth_statement ->
         exists n0 : nat, forall n : nat, n0 <= n -> exists G : sgraph, #|G| = n /\ k_connected G 2)].

Theorem g282_kc_hyp_inhabited : g282_kc_hyp_claim.
Proof.
split=> // [n R|S]; first exact: g282_id_growth.
have [a [b [n0 h]]] := S 2 isT (fun m => m) g282_id_growth.
by exists n0 => n nn; have [G [cG kG _]] := h n nn; exists G.
Qed.

(** The variant asking for the graphs at every order, without the threshold n0. *)
Definition g282_kc_every_order : Prop :=
  forall k : nat, 2 <= k -> forall f : nat -> nat,
    (forall n R : nat, xe1_diagonal_ramsey_number ('K_n) R -> n <= f n <= R) ->
    exists a b : nat, forall n : nat,
      exists G : sgraph,
        [/\ #|G| = n, k_connected G k &
            exists2 R : nat, xe1_diagonal_ramsey_number G R & (f n <= b * R) && (R <= a * f n)].

Definition g282_kc_ntt_claim : Prop :=
  ~ g282_kc_every_order /\ (g282_kc_every_order -> k_connected_ramsey_growth_statement).

Theorem g282_kc_not_trivially_true : g282_kc_ntt_claim.
Proof.
split; last first.
  by move=> h k k2 f hf; have [a [b hab]] := h k k2 f hf; exists a, b, 0 => n _; exact: hab.
move=> h; have [a [b hab]] := h 2 isT (fun m => m) g282_id_growth.
by have [G [cG [kG _] _]] := hab 0; move: kG; rewrite cG.
Qed.

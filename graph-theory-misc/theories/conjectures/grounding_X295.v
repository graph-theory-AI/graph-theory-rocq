(** * GTMisc.conjectures.grounding_X295 -- grounding certificates for wave X295 (2026-11-06)

    For the one row (the Strong Normal Graph Conjecture): hyp_inhabited (both sides of the equivalence hold at a
    small instance, and the statement then gives one side from the other there) and not_trivially_true (the variant
    "both sides hold for every graph" is false and implies the statement).  X295 has no helper, so no helper_sanity.
    - hyp: at K_2 every induced subgraph is complete, hence normal (the clique of all vertices, and the singletons as
      stable sets: g295_complete_normal), and K_2 and its complement have no induced C_5 or C_7 (too few vertices).
    - ntt: C_5 induces itself (g295_C5_induced_C5), so "both sides for every graph" fails there.
    - the graph with no vertex satisfies both sides (g295_K0_both_sides), the degenerate instance of the Notes. *)

From GTBase Require Import base.
From GTMisc.conjectures Require Import X29 X295.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* A graph whose distinct vertices are all adjacent is normal: the one clique of all vertices, and the singletons as
   stable sets. *)
Lemma g295_complete_normal (F : sgraph) : (forall x y : F, x != y -> x -- y) -> x29_normal_graph F.
Proof.
move=> cF; exists [:: [set: F]], [seq [set v] | v <- enum F]; split; [|split].
- split=> [K|v]; first by rewrite inE => /eqP-> x y _ _; exact: cF.
  by exists [set: F]; rewrite inE eqxx inE.
- split=> [I /mapP[v _ ->]|v]; first exact: stable1.
  by exists [set v]; split; [apply/mapP; exists v; rewrite ?mem_enum | exact: set11].
- move=> K I; rewrite inE => /eqP-> /mapP[v _ ->]; rewrite setTI; apply/set0Pn; exists v; exact: set11.
Qed.

(* Every induced subgraph of a complete graph is complete, hence normal. *)
Lemma g295_Kn_strongly_normal (n : nat) (T : {set 'K_n}) : x29_normal_graph (induced T).
Proof. apply: g295_complete_normal => x y xy; by move: xy; rewrite -(inj_eq val_inj). Qed.

(* No induced cycle longer than the graph. *)
Lemma g295_no_long_cycle (G : sgraph) (n : nat) : (#|G| < n)%N -> ~ x29_has_induced_cycle G n.
Proof. by move=> lt [S [cS _]]; move: (max_card S); rewrite cS leqNgt lt. Qed.

(* Every graph induces itself on all its vertices. *)
Lemma g295_induced_setT (G : sgraph) : inhabited (induced [set: G] ≃ G).
Proof.
constructor; pose g : G -> induced [set: G] := fun x => Sub x (in_setT x).
apply: (@Diso' (induced [set: G]) G val g _ _ _).
- by move=> x; apply: val_inj.
- by [].
- by [].
Qed.

(* C_5 has an induced C_5 (itself). *)
Lemma g295_C5_induced_C5 : x29_has_induced_cycle (cycle_graph 5) 5.
Proof.
exists [set: cycle_graph 5]; split; first by rewrite cardsT card_ord.
exact: g295_induced_setT.
Qed.

(* ** hyp_inhabited: both sides hold at K_2, and the statement then says so. *)
Definition g295_sng_hyp_claim : Prop :=
  [/\ forall T : {set 'K_2}, x29_normal_graph (induced T),
      [/\ ~ x29_has_induced_cycle ('K_2) 5, ~ x29_has_induced_cycle ('K_2) 7,
          ~ x29_has_induced_cycle (compl ('K_2)) 5 & ~ x29_has_induced_cycle (compl ('K_2)) 7] &
      (strong_normal_graph_statement ->
       [/\ ~ x29_has_induced_cycle ('K_2) 5, ~ x29_has_induced_cycle ('K_2) 7,
           ~ x29_has_induced_cycle (compl ('K_2)) 5 & ~ x29_has_induced_cycle (compl ('K_2)) 7] ->
       forall T : {set 'K_2}, x29_normal_graph (induced T))].

Theorem g295_sng_hyp_inhabited : g295_sng_hyp_claim.
Proof.
have small : forall n, (2 < n)%N -> ~ x29_has_induced_cycle ('K_2) n /\ ~ x29_has_induced_cycle (compl ('K_2)) n.
  by move=> n lt; split; apply: g295_no_long_cycle; rewrite card_ord.
have [a5 b5] := small 5 isT; have [a7 b7] := small 7 isT.
split; [exact: g295_Kn_strongly_normal | by split | ].
by move=> st rhs; apply/(st ('K_2)).
Qed.

(* ** not_trivially_true: both sides for every graph implies the row, and fails at C_5. *)
Definition g295_sng_both_sides : Prop :=
  forall G : sgraph,
    (forall T : {set G}, x29_normal_graph (induced T)) /\
    [/\ ~ x29_has_induced_cycle G 5, ~ x29_has_induced_cycle G 7,
        ~ x29_has_induced_cycle (compl G) 5 & ~ x29_has_induced_cycle (compl G) 7].

Definition g295_sng_ntt_claim : Prop :=
  ~ g295_sng_both_sides /\ (g295_sng_both_sides -> strong_normal_graph_statement).

Theorem g295_sng_not_trivially_true : g295_sng_ntt_claim.
Proof.
split; last by move=> h G; split=> _; case: (h G).
by move=> h; case: (h (cycle_graph 5)) => _ [no5 _ _ _]; exact: no5 g295_C5_induced_C5.
Qed.

(* Degenerate instance: the graph with no vertex satisfies both sides. *)
Lemma g295_K0_both_sides :
  (forall T : {set 'K_0}, x29_normal_graph (induced T)) /\
  [/\ ~ x29_has_induced_cycle ('K_0) 5, ~ x29_has_induced_cycle ('K_0) 7,
      ~ x29_has_induced_cycle (compl ('K_0)) 5 & ~ x29_has_induced_cycle (compl ('K_0)) 7].
Proof.
split; first exact: g295_Kn_strongly_normal.
by split; apply: g295_no_long_cycle; rewrite card_ord.
Qed.

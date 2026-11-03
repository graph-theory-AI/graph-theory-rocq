(** * GTMisc.conjectures.grounding_X283 -- grounding certificates for wave X283 (2026-11-03)

    For each of the three rows: hyp_inhabited (the body's conditions hold at a small instance, and the statement
    gives its consequence) and not_trivially_true (a variant is false and implies the statement).  X283.v has no
    local helper, so there is no helper_sanity certificate.
    - Sivaraman: K_1 is connected and P_5-free, and the statement gives c(K_1) <= 2.  Without the guard 5 <= t the
      row is false: at t = 0 every graph is P_0-free (no induced path has no vertex), and K_1 needs a cop.
    - Strongly-separating path systems: K_3 has two distinct edges, and the statement gives a path through one and
      not the other.  Without "e != f" the row is false: on K_2 the pair (e, e) asks for a path containing e and
      not e.
    - Pivot Gray codes: the edge of K_2 is a spanning tree, and the statement lists it.  The cyclic variant (a
      pivot also from the last tree back to the first) is STRICTLY STRONGER than the row and false: K_1 has one
      spanning tree, the empty edge set, and no edge to remove. *)

From GTBase Require Import base induced_paths walks_paths finite_graph spanning_trees.
From GTMisc.foundations Require Import cops.
From GTMisc.conjectures Require Import X283.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** studies:std_sivaraman_s_conjecture_cop_number_of_p_t_free_gr ********** *)

Lemma g283_K1_connected : connected [set: 'K_1].
Proof. by move=> x y _ _; rewrite (ord1 x) (ord1 y); exact: connect0. Qed.

(** No induced path has 0 vertices: every graph is P_0-free. *)
Lemma g283_no_path0 (G : sgraph) : ~ has_induced_path_of_order G 0.
Proof. by move=> [p [/size0nil -> []]]. Qed.

(** K_1 is P_5-free: five distinct vertices do not fit in one. *)
Lemma g283_K1_no_path5 : ~ has_induced_path_of_order ('K_1) 5.
Proof.
move=> [p [sz ip]]; case: p sz ip => // x q sz /= [uq _].
have /card_uniqP := (uq : uniq (x :: q)); rewrite sz => h.
by have := max_card (mem (x :: q)); rewrite h card_ord.
Qed.

(** hyp_inhabited: K_1 is connected and P_5-free, and the statement gives c(K_1) <= 2. *)
Definition g283_sv_hyp_claim : Prop :=
  [/\ 5 <= 5, connected [set: 'K_1], ~ has_induced_path_of_order ('K_1) 5
    & (sivaraman_cop_number_pt_free_statement -> cop_number_le ('K_1) 2)].

Theorem g283_sv_hyp_inhabited : g283_sv_hyp_claim.
Proof.
split=> //; [exact: g283_K1_connected | exact: g283_K1_no_path5 |].
by move=> h; exact: (h 5 isT ('K_1) g283_K1_connected g283_K1_no_path5).
Qed.

(** not_trivially_true: without the guard 5 <= t the statement is false (t = 0, K_1). *)
Definition g283_sv_no_guard : Prop :=
  forall t : nat,
    forall G : sgraph, connected [set: G] ->
      ~ has_induced_path_of_order G t -> cop_number_le G (t - 3).

Definition g283_sv_ntt_claim : Prop :=
  ~ g283_sv_no_guard /\ (g283_sv_no_guard -> sivaraman_cop_number_pt_free_statement).

Theorem g283_sv_not_trivially_true : g283_sv_ntt_claim.
Proof.
split; last by move=> h t _ G; exact: h.
move=> h; have := h 0 ('K_1) g283_K1_connected (@g283_no_path0 _).
by apply: not_cop_number_le_0; rewrite card_ord.
Qed.

(** ** arxiv:2301.08707#00 *************************************************** *)

Definition g283_t1 : 'I_3 := @Ordinal 3 1 isT.
Definition g283_t2 : 'I_3 := @Ordinal 3 2 isT.

(** hyp_inhabited: K_3 has the two distinct edges {0, 1} and {0, 2}, and the statement gives a path through the
    first and not the second. *)
Definition g283_ss_hyp_claim : Prop :=
  [/\ [set (ord0 : 'K_3); g283_t1] \in E('K_3), [set (ord0 : 'K_3); g283_t2] \in E('K_3),
      [set (ord0 : 'K_3); g283_t1] != [set ord0; g283_t2]
    & (strongly_separating_path_system_2n_statement ->
         exists2 p : seq ('K_3), seq_simple_path p &
           ([set ord0; g283_t1] \in seq_edge_set p) && ([set ord0; g283_t2] \notin seq_edge_set p))].

Theorem g283_ss_hyp_inhabited : g283_ss_hyp_claim.
Proof.
have e1 : [set (ord0 : 'K_3); g283_t1] \in E('K_3) by rewrite in_edges.
have e2 : [set (ord0 : 'K_3); g283_t2] \in E('K_3) by rewrite in_edges.
have ne : [set (ord0 : 'K_3); g283_t1] != [set ord0; g283_t2].
  by apply/eqP => /setP /(_ g283_t1); rewrite !inE.
split=> // h; have [P [_ sp sep]] := h 'K_3.
have [p pP sepp] := sep _ _ e1 e2 ne.
by exists p => //; exact: sp.
Qed.

(** not_trivially_true: without "e != f" the statement is false (K_2, e = f). *)
Definition g283_ss_no_distinct : Prop :=
  forall G : sgraph, exists P : seq (seq G),
    [/\ size P <= 2 * #|G|,
        forall p : seq G, p \in P -> seq_simple_path p
      & forall e f : {set G}, e \in E(G) -> f \in E(G) ->
          exists2 p : seq G, p \in P & (e \in seq_edge_set p) && (f \notin seq_edge_set p)].

Definition g283_ss_ntt_claim : Prop :=
  ~ g283_ss_no_distinct /\ (g283_ss_no_distinct -> strongly_separating_path_system_2n_statement).

Theorem g283_ss_not_trivially_true : g283_ss_ntt_claim.
Proof.
split; last first.
  move=> h G; have [P [sz sp sep]] := h G.
  by exists P; split=> // e f eE fE _; exact: sep.
move=> h; have [P [_ _ sep]] := h 'K_2.
have eE : [set (ord0 : 'K_2); ord_max] \in E('K_2) by rewrite in_edges.
have [p _] := sep _ _ eE eE.
by rewrite andbN.
Qed.

(** ** arxiv:2603.28614#00 *************************************************** *)

(** hyp_inhabited: the edge of K_2 is a spanning tree, and the statement lists it. *)
Definition g283_pg_hyp_claim : Prop :=
  fg_spanning_tree (fg_edges ('K_2)) /\
  (pivot_gray_code_spanning_trees_statement ->
     exists2 s : seq {set {set ('K_2)}}, uniq s & fg_edges ('K_2) \in s).

Theorem g283_pg_hyp_inhabited : g283_pg_hyp_claim.
Proof.
split; first exact: fg_spanning_tree_K2.
move=> h; have [s [u mem _]] := h 'K_2.
by exists s => //; apply/mem; exact: fg_spanning_tree_K2.
Qed.

(** K_1 has exactly one spanning tree, the empty edge set. *)
Lemma g283_K1_tree (T : {set {set 'K_1}}) : fg_spanning_tree T <-> T = set0.
Proof.
split=> [/fg_spanning_tree_sub sub|->]; last exact: fg_spanning_tree_K1.
apply/setP => e; rewrite inE; apply/negbTE/negP => eT.
have := subsetP sub e eT; rewrite fg_edgesE => /edgesP [x [y [_ xy]]].
by move: xy; rewrite (ord1 x) (ord1 y) sg_irrefl.
Qed.

(** The cyclic variant: also a pivot from the last tree back to the first.  It is strictly stronger than the
    statement. *)
Definition g283_pg_cyclic : Prop :=
  forall G : sgraph, exists s : seq {set {set G}},
    [/\ uniq s,
        forall T : {set {set G}}, T \in s <-> fg_spanning_tree T,
        forall i : nat, i.+1 < size s ->
          exists e f : {set G},
            [/\ e \in nth set0 s i, f \notin nth set0 s i,
                nth set0 s i.+1 = (nth set0 s i :\ e) :|: [set f] & e :&: f != set0]
      & s != [::] ->
          exists e f : {set G},
            [/\ e \in last set0 s, f \notin last set0 s,
                head set0 s = (last set0 s :\ e) :|: [set f] & e :&: f != set0]].

(** not_trivially_true: the cyclic variant is false (K_1: its only tree has no edge to remove) and implies the
    statement. *)
Definition g283_pg_ntt_claim : Prop :=
  ~ g283_pg_cyclic /\ (g283_pg_cyclic -> pivot_gray_code_spanning_trees_statement).

Theorem g283_pg_not_trivially_true : g283_pg_ntt_claim.
Proof.
split; last first.
  by move=> h G; have [s [u mem piv _]] := h G; exists s; split.
move=> h; have [s [_ mem _ cyc]] := h 'K_1.
have s0 : set0 \in s by apply/mem; exact: fg_spanning_tree_K1.
have sn : s != [::] by case: s s0 {mem cyc}.
have [e [f [eT _ _ _]]] := cyc sn.
have : last set0 s \in s by case: s s0 sn {mem cyc eT} => // x s' _ _ /=; exact: mem_last.
move=> /mem /g283_K1_tree lT; move: eT; rewrite lT.
by rewrite inE.
Qed.

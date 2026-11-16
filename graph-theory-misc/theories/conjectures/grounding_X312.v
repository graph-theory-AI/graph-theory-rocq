(** * GTMisc.conjectures.grounding_X312 -- grounding certificates of wave X312: for each row a hyp_inhabited and a
      not_trivially_true certificate, and the helper_sanity certificate of x312_packing (named in every row) *)

From GTBase Require Import base petersen induced_paths induced_cycles.
From Minor.conjectures Require Import X42.
From Minor.foundations Require Import width_params.
From GTMisc.conjectures Require Import X91 X312.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The Petersen graph (GTBase petersen_ord): subcubic, connected, dominated by {0, 7, 8}, not dominated by any
    set of at most two vertices, and every packing has at most one vertex. The checks run on an explicit list of the
    ten vertices (no computation on a finset or on enum 'I_10); lemmas transfer them. *)
Local Notation Pg := petersen_ord.
Local Notation O10 i := (@Ordinal 10 i isT).

Definition g312_pv : seq Pg :=
  [:: O10 0; O10 1; O10 2; O10 3; O10 4; O10 5; O10 6; O10 7; O10 8; O10 9].

Lemma g312_pv_all (x : Pg) : x \in g312_pv.
Proof. by case: x => -[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]] Hx //=; apply/eqP. Qed.

Lemma g312_pv_uniq : uniq g312_pv.
Proof. by vm_compute. Qed.

Arguments g312_pv : simpl never.

Lemma g312_nbrs_ok : all (fun v => size [seq y <- g312_pv | @edge_rel Pg v y] <= 3) g312_pv.
Proof. by vm_compute. Qed.

Lemma g312_subcubic : subcubic Pg.
Proof.
move=> v; move/allP: g312_nbrs_ok => /(_ v (g312_pv_all v)); apply: leq_trans.
have /card_uniqP <- := filter_uniq (fun y => @edge_rel Pg v y) g312_pv_uniq.
by apply: eq_leq; apply: eq_card => y; rewrite in_opn mem_filter g312_pv_all andbT.
Qed.

(* Breadth-first reachability from vertex 0 over the explicit vertex list. *)
Fixpoint g312_reach (n : nat) (R : seq Pg) : seq Pg :=
  if n is n'.+1 then
    g312_reach n' (R ++ [seq y <- g312_pv | (y \notin R) && has (fun x => @edge_rel Pg x y) R])
  else R.

Lemma g312_reachP n R :
  (forall x, x \in R -> connect (preliminaries.restrict_mem (mem [set: Pg]) (--)) (O10 0) x) ->
  forall y, y \in g312_reach n R -> connect (preliminaries.restrict_mem (mem [set: Pg]) (--)) (O10 0) y.
Proof.
elim: n R => [|n IH] R hR y; first exact: hR.
move=> hy; apply: (IH _ _ y hy) => x; rewrite mem_cat => /orP[/hR // |].
rewrite mem_filter => /andP[/andP[_ /hasP[z hz hzx]] _].
apply: connect_trans (hR z hz) (connect1 _).
by rewrite /preliminaries.restrict_mem /= !inE hzx.
Qed.

Lemma g312_reach_all : all (fun y => y \in g312_reach 10 [:: O10 0]) g312_pv.
Proof. by vm_compute. Qed.

Lemma g312_connected : connected [set: Pg].
Proof.
apply: (@connected_center Pg (O10 0 : Pg)) => [y _|]; last by rewrite inE.
apply: (@g312_reachP 10 [:: O10 0]); last by move/allP: g312_reach_all; apply; exact: g312_pv_all.
by move=> x; rewrite inE => /eqP ->; exact: connect0.
Qed.

(* {0, 7, 8} dominates. *)
Lemma g312_dom_ok :
  all (fun v => has (fun u => (u == v) || @edge_rel Pg u v) [:: O10 0; O10 7; O10 8]) g312_pv.
Proof. by vm_compute. Qed.

Lemma g312_dominating : dominating ([set O10 0; O10 7; O10 8] : {set Pg}).
Proof.
apply/forallP => v; move/allP: g312_dom_ok => /(_ v (g312_pv_all v)) /hasP[u hu huv].
apply/bigcupP; exists u; last by rewrite in_cln.
by move: hu; rewrite !inE -orbA.
Qed.

(* No set of at most two vertices dominates: for every u, w some vertex is in neither closed neighbourhood. *)
Lemma g312_pairs_ok :
  all (fun u => all (fun w =>
    ~~ all (fun v => ((u == v) || @edge_rel Pg u v) || ((w == v) || @edge_rel Pg w v)) g312_pv) g312_pv) g312_pv.
Proof. by vm_compute. Qed.

Lemma g312_no_small_dom (D : {set Pg}) : #|D| <= 2 -> ~~ dominating D.
Proof.
move=> hD; apply/negP => /forallP hdom.
have hs : size (enum D) <= 2 by rewrite -cardE.
pose u := nth (O10 0) (enum D) 0; pose w := nth (O10 0) (enum D) 1.
have hx : forall x, x \in D -> (x == u) || (x == w).
  move=> x; rewrite -mem_enum /u /w; move: hs.
  case: (enum D) => [|a [|b [|c s]]] //= _; first by rewrite inE => ->.
  by rewrite !inE.
move/allP: g312_pairs_ok => /(_ u (g312_pv_all u)) /allP /(_ w (g312_pv_all w)) /allPn[v _].
case/bigcupP: (hdom v) => x hxD; rewrite in_cln /dominates.
by case/orP: (hx x hxD) => /eqP -> ->; rewrite ?orbT.
Qed.

(* Distinct vertices share a closed-neighbourhood vertex (diameter 2), so every packing has at most one vertex. *)
Lemma g312_common_ok :
  all (fun u => all (fun v => (u == v) ||
    has (fun x => ((u == x) || @edge_rel Pg u x) && ((v == x) || @edge_rel Pg v x)) g312_pv) g312_pv) g312_pv.
Proof. by vm_compute. Qed.

Lemma g312_packing_le1 (P : {set Pg}) : x312_packing P -> #|P| <= 1.
Proof.
move=> hP; rewrite leqNgt; apply/negP => /card_gt1P[u [v [hu hv huv]]].
move/allP: g312_common_ok => /(_ u (g312_pv_all u)) /allP /(_ v (g312_pv_all v)).
rewrite (negbTE huv) orFb => /hasP[x _ /andP[hux hvx]].
have := hP u v hu hv huv; rewrite disjoint_subset => /subsetP /(_ x).
by rewrite in_cln /dominates hux => /(_ isT); rewrite inE in_cln /dominates hvx.
Qed.


(** ** helper_sanity: x312_packing holds for the empty set and every singleton, and fails for two vertices of the
    Petersen graph *)
Lemma g312_packing0 (G : sgraph) : x312_packing (set0 : {set G}).
Proof. by move=> u v; rewrite inE. Qed.

Lemma g312_packing1 (G : sgraph) (w : G) : x312_packing [set w].
Proof. by move=> u v; rewrite !inE => /eqP -> /eqP ->; rewrite eqxx. Qed.

Definition g312_helper_claim : Prop :=
  [/\ forall G : sgraph, x312_packing (set0 : {set G}),
      forall (G : sgraph) (w : G), x312_packing [set w]
    & ~ x312_packing ([set O10 0; O10 1] : {set Pg})].

Theorem g312_helper_sanity : g312_helper_claim.
Proof.
split; [exact: g312_packing0 | exact: g312_packing1 |].
by move=> /g312_packing_le1; rewrite cards2.
Qed.

(** ** R1: hyp_inhabited (the Petersen graph) and not_trivially_true (the variant gamma <= 2 rho fails there) *)
Definition g312_hlr_at (G : sgraph) : Prop :=
  exists D P : {set G}, [/\ dominating D, x312_packing P & #|D| <= 2 * #|P| + 1].

Definition g312_hlr_hyp_claim : Prop :=
  [/\ connected [set: Pg], subcubic Pg, g312_hlr_at Pg &
      (subcubic_domination_packing_statement -> g312_hlr_at Pg)].

Theorem g312_hlr_hyp_inhabited : g312_hlr_hyp_claim.
Proof.
split; [exact: g312_connected | exact: g312_subcubic | |].
- exists ([set O10 0; O10 7; O10 8] : {set Pg}), ([set O10 0] : {set Pg}).
  split; [exact: g312_dominating | exact: g312_packing1 |].
  by rewrite cards1; exact: preliminaries.cards3.
- by move=> S; exact: S _ g312_connected g312_subcubic.
Qed.

Definition g312_hlr_strict : Prop :=
  forall G : sgraph, connected [set: G] -> subcubic G ->
    exists D P : {set G}, [/\ dominating D, x312_packing P & #|D| <= 2 * #|P|].

Definition g312_hlr_ntt_claim : Prop :=
  ~ g312_hlr_strict /\ (g312_hlr_strict -> subcubic_domination_packing_statement).

Theorem g312_hlr_not_trivially_true : g312_hlr_ntt_claim.
Proof.
split.
- move=> V; have [D [P [hD hP hle]]] := V Pg g312_connected g312_subcubic.
  have hD2 : #|D| <= 2.
    by apply: leq_trans hle _; rewrite -{2}(muln1 2) leq_mul2l; exact: g312_packing_le1.
  by move: (g312_no_small_dom hD2); rewrite hD.
- move=> V G hc hs; have [D [P [hD hP hle]]] := V G hc hs.
  by exists D, P; split => //; apply: leq_trans hle (leq_addr 1 _).
Qed.

(** ** R2: hyp_inhabited (t = 4, the triangle) and not_trivially_true (t = 3: K_2 forces c_3 >= 1) *)
Definition g312_st_class (t : nat) (G : sgraph) : Prop :=
  [/\ (forall h : seq G, hole h -> odd (size h)), induced_free G x42_diamond & induced_free G 'K_t].

Lemma g312_card_diamond : #|x42_diamond| = 4.
Proof. by rewrite card_sum !card_bool. Qed.

Lemma g312_no_hole (G : sgraph) (h : seq G) : #|G| <= 3 -> ~ hole h.
Proof.
move=> hG [/andP[_ hu] [hs _]].
by move: (leq_trans (max_card (mem h)) hG); rewrite (card_uniqP hu) leqNgt hs.
Qed.

Lemma g312_small_class (t : nat) (G : sgraph) : #|G| <= 3 -> #|G| < t -> g312_st_class t G.
Proof.
move=> h3 ht; split.
- by move=> h /(g312_no_hole h3).
- by apply: induced_free_card; rewrite g312_card_diamond; apply: leq_ltn_trans h3 _.
- by apply: induced_free_card; rewrite card_ord.
Qed.

Definition g312_st_hyp_claim : Prop :=
  [/\ g312_st_class 4 ('K_3), tw_le ('K_3) 2 &
      (even_hole_diamond_kt_free_bounded_treewidth_statement ->
         exists c : nat, forall G : sgraph, g312_st_class 4 G -> tw_le G c)].

Theorem g312_st_hyp_inhabited : g312_st_hyp_claim.
Proof.
split; first by apply: g312_small_class; rewrite card_ord.
- by apply: tw_le_card; rewrite card_ord.
- by move=> S; have [c hc] := S 4; exists c => G [h1 h2 h3]; exact: hc.
Qed.

Definition g312_st_ntt_claim : Prop :=
  [/\ g312_st_class 3 ('K_2),
      (forall c : nat, (forall G : sgraph, g312_st_class 3 G -> tw_le G c) -> 1 <= c)
    & (even_hole_diamond_kt_free_bounded_treewidth_statement ->
         exists2 c : nat, 1 <= c & forall G : sgraph, g312_st_class 3 G -> tw_le G c)].

Theorem g312_st_not_trivially_true : g312_st_ntt_claim.
Proof.
have hK2 : g312_st_class 3 'K_2 by apply: g312_small_class; rewrite card_ord.
have hlb : forall c : nat, (forall G : sgraph, g312_st_class 3 G -> tw_le G c) -> 1 <= c.
  move=> c hc; rewrite lt0n; apply/negP => /eqP c0.
  move: (hc _ hK2); rewrite c0 => tw.
  by move: (tw_le0_edgeless (ord0 : 'K_2) (@Ordinal 2 1 isT) tw).
split=> // S; have [c hc] := S 3.
have hc3 : forall G : sgraph, g312_st_class 3 G -> tw_le G c by move=> G [h1 h2 h3]; exact: hc.
by exists c => //; exact: hlb.
Qed.

(** ** R5: hyp_inhabited (k = 1 on K_2, both disjuncts' witnesses) and not_trivially_true (the variant "every graph
    has two disjoint avoidable P_k" implies the row and fails on K_1 at k = 1) *)
Definition g312_two_paths (G : sgraph) (k : nat) : Prop :=
  exists p q : seq G,
    [/\ size p = k, size q = k, nonempty_induced_path p, nonempty_induced_path q & [disjoint p & q]].

Definition g312_two_avoidable (G : sgraph) (k : nat) : Prop :=
  exists p q : seq G,
    [/\ size p = k, size q = k, x91_avoidable_path p, x91_avoidable_path q & [disjoint p & q]].

(* A single vertex is a non-empty induced path. *)
Lemma g312_single_path (G : sgraph) (a : G) : nonempty_induced_path [:: a].
Proof. by split=> //; split=> // u v; rewrite !inE => /eqP -> /eqP ->; rewrite eqxx. Qed.

(* In a graph with at most two vertices a single vertex is avoidable: it has no induced two-sided extension. *)
Lemma g312_single_avoidable (G : sgraph) (a : G) : #|G| <= 2 -> x91_avoidable_path [:: a].
Proof.
move=> hG; split; first exact: g312_single_path.
move=> u v [hu _]; exfalso; move: (max_card (mem (u :: rcons [:: a] v))).
by rewrite (card_uniqP hu) => /leq_trans /(_ hG).
Qed.

Definition g312_tdap_hyp_claim : Prop :=
  [/\ g312_two_paths 'K_2 1, g312_two_avoidable 'K_2 1 &
      (two_disjoint_avoidable_paths_statement -> ~ g312_two_paths 'K_2 1 \/ g312_two_avoidable 'K_2 1)].

Theorem g312_tdap_hyp_inhabited : g312_tdap_hyp_claim.
Proof.
have hd : [disjoint [:: (ord0 : 'K_2)] & [:: (@Ordinal 2 1 isT : 'K_2)]] by rewrite disjoint_has.
split.
- exists [:: ord0], [:: Ordinal (isT : 1 < 2)]; split=> //; exact: g312_single_path.
- exists [:: ord0], [:: Ordinal (isT : 1 < 2)]; split=> //; apply: g312_single_avoidable; by rewrite card_ord.
- by move=> S; exact: S 1 isT ('K_2).
Qed.

Definition g312_tdap_strict : Prop := forall k : nat, 0 < k -> forall G : sgraph, g312_two_avoidable G k.

Definition g312_tdap_ntt_claim : Prop :=
  ~ g312_tdap_strict /\ (g312_tdap_strict -> two_disjoint_avoidable_paths_statement).

Theorem g312_tdap_not_trivially_true : g312_tdap_ntt_claim.
Proof.
split; last by move=> V k hk G; right; exact: V k hk G.
move=> V; have [p [q [hp hq _ _ hpq]]] := V 1 isT ('K_1).
move: hp hq hpq; case: p => [|a [|? ?]] //; case: q => [|b [|? ?]] // _ _.
by rewrite disjoint_has /= inE (ord1 a) (ord1 b) eqxx.
Qed.

(** * Packing.conjectures.grounding_X294 -- grounding certificates for wave X294 (2026-11-06)

    For the one row (Gruslys' conjecture): hyp_inhabited (the body's hypotheses hold together at a small instance,
    and the statement gives its conclusion there), not_trivially_true (the variant without the divisibility
    hypothesis is false and implies the statement), and helper_sanity for the three local helpers of X294.v.
    - hyp: K_2 is vertex-transitive (every complete graph is: a transposition is an automorphism), a singleton
      induces K_1, and 1 divides 2; every power of every graph has a perfect induced K_1-packing (by singletons).
    - ntt: without "|V(H)| divides |V(G)|" the row is false at G = K_3, H = K_2 (Arthur's O1, a nonempty pattern):
      any two vertices of K_3 induce K_2, and a partition of the 3^n vertices of K_3^n into blocks of two vertices
      would make 3^n even.
    - helpers: transpositions of K_n are automorphisms; K_2 is vertex-transitive, the graph on three vertices
      with one edge is not (an isolated vertex cannot be mapped to an endpoint of the edge); #|G^n| = #|G|^n and
      G^1 is isomorphic to G. *)

From GraphTheory Require Import bij.
From GTBase Require Import base common.
From Packing.conjectures Require Import X294.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Complete graphs are vertex-transitive *)

(** The transposition of x and y on K_n; on K_n every bijection preserves and reflects adjacency. *)
Definition g294_swap (n : nat) (x y : 'K_n) (v : 'K_n) : 'K_n :=
  if v == x then y else if v == y then x else v.

Lemma g294_swapK (n : nat) (x y : 'K_n) : involutive (g294_swap x y).
Proof.
move=> v; rewrite /g294_swap.
case: (eqVneq v x) => [->|vx]; first by rewrite eqxx; case: (eqVneq y x) => [->|yx]; rewrite ?eqxx.
case: (eqVneq v y) => [->|vy]; first by rewrite eqxx.
by rewrite (negPf vx) (negPf vy).
Qed.

Lemma g294_swap_aut (n : nat) (x y : 'K_n) : x294_graph_automorphism (g294_swap x y).
Proof.
split; first exact: inv_bij (g294_swapK x y).
by move=> u v; rewrite /edge_rel /= (inj_eq (inv_inj (g294_swapK x y))).
Qed.

Lemma g294_Kn_vt (n : nat) : x294_vertex_transitive 'K_n.
Proof.
move=> x y; exists (g294_swap x y); split; first exact: g294_swap_aut.
by rewrite /g294_swap eqxx.
Qed.

(** ** Induced copies of K_1 and K_0, and the packing by singletons *)

Lemma g294_singleton_K1 (F : sgraph) (v : F) : inhabited (induced [set v] ≃ 'K_1).
Proof.
have eS : #|induced [set v]| = 1.
  by rewrite card_sig -(cards1 v); apply: eq_card => x; rewrite !inE.
constructor; rewrite -[X in 'K_X]eS; apply: diso_Kn => x y xy; exfalso; move: xy.
have := valP x; have := valP y; rewrite !inE => /eqP ey /eqP ex.
suff -> : x = y by rewrite eqxx.
by apply: val_inj; rewrite ex ey.
Qed.

Lemma g294_singletons_partition (F : sgraph) : partition [set [set v] | v : F] [set: F].
Proof.
apply/and3P; split.
- apply/eqP/setP => v; rewrite inE; apply/bigcupP; exists [set v]; [exact: imset_f | exact: set11].
- apply/trivIsetP => A B /imsetP[a _ ->] /imsetP[b _ ->] ab; rewrite disjoints1 inE.
  by apply/negP => /eqP eab; move: ab; rewrite eab eqxx.
- apply/negP; case/imsetP => v _ e; have := set11 v; by rewrite -e inE.
Qed.

Lemma g294_K1_packing (G : sgraph) (n : nat) :
  exists P : {set {set x294_box_power G n}},
    partition P [set: x294_box_power G n] /\ forall S, S \in P -> inhabited (induced S ≃ 'K_1).
Proof.
exists [set [set v] | v : x294_box_power G n]; split; first exact: g294_singletons_partition.
by move=> S /imsetP[v _ ->]; exact: g294_singleton_K1.
Qed.

(** ** The size of a power *)

Lemma g294_box_power_card (G : sgraph) (n : nat) : #|x294_box_power G n| = (#|G| ^ n)%N.
Proof.
elim: n => [|n IH]; first by rewrite card_ord.
by rewrite /= card_prod IH expnSr.
Qed.

(** ** hyp_inhabited *)

Definition g294_gpip_hyp_claim : Prop :=
  [/\ x294_vertex_transitive ('K_2),
      exists S : {set 'K_2}, inhabited (induced S ≃ 'K_1),
      (#|'K_1| %| #|'K_2|)%N &
      (gruslys_perfect_induced_packing_statement ->
       exists n : nat, (0 < n)%N /\
         exists P : {set {set x294_box_power 'K_2 n}},
           partition P [set: x294_box_power 'K_2 n] /\
           forall S, S \in P -> inhabited (induced S ≃ 'K_1))].

Theorem g294_gpip_hyp_inhabited : g294_gpip_hyp_claim.
Proof.
have ind : exists S : {set 'K_2}, inhabited (induced S ≃ 'K_1).
  by exists [set ord0]; exact: g294_singleton_K1.
split; [exact: g294_Kn_vt | exact: ind | by rewrite !card_ord dvd1n | ].
by move=> st; apply: st; [exact: g294_Kn_vt | exact: ind | rewrite !card_ord dvd1n].
Qed.

(** ** not_trivially_true *)

(** The row without the divisibility hypothesis. *)
Definition g294_gpip_no_divisibility : Prop :=
  forall G H : sgraph,
    x294_vertex_transitive G ->
    (exists S : {set G}, inhabited (induced S ≃ H)) ->
    exists n : nat, (0 < n)%N /\
      exists P : {set {set x294_box_power G n}},
        partition P [set: x294_box_power G n] /\
        forall S, S \in P -> inhabited (induced S ≃ H).

(** K_2 is induced in K_3: any two vertices of a complete graph. *)
Lemma g294_K2_in_K3 : exists S : {set 'K_3}, inhabited (induced S ≃ 'K_2).
Proof.
exists [set~ ord0]; have eS : #|induced [set~ (ord0 : 'K_3)]| = 2.
  have e : #|[set~ (ord0 : 'K_3)]| = 2 by rewrite cardsC1 card_ord.
  by rewrite card_sig -[RHS]e; apply: eq_card => x; rewrite !inE.
constructor; rewrite -[X in _ ≃ 'K_X]eS; apply: diso_Kn => x y xy.
by move: xy; rewrite -(inj_eq val_inj).
Qed.

(** No power of K_3 has a perfect induced K_2-packing: its 3^n vertices are odd in number. *)
Lemma g294_K3_K2_no_packing (n : nat) :
  ~ exists P : {set {set x294_box_power 'K_3 n}},
      partition P [set: x294_box_power 'K_3 n] /\ forall S, S \in P -> inhabited (induced S ≃ 'K_2).
Proof.
case=> P [pP copies].
have card2 : forall S, S \in P -> #|S| = 2.
  move=> S SP; case: (copies S SP) => i; have e := card_bij (diso_v i); rewrite card_ord in e.
  by rewrite -[RHS]e card_sig; apply: eq_card => x; rewrite inE.
have := card_partition pP; rewrite cardsT g294_box_power_card card_ord.
rewrite (eq_bigr (fun _ => 2)) // sum_nat_const => e3.
have : odd (3 ^ n) by rewrite oddX orbC.
by rewrite e3 oddM andbF.
Qed.

Definition g294_gpip_ntt_claim : Prop :=
  ~ g294_gpip_no_divisibility /\
  (g294_gpip_no_divisibility -> gruslys_perfect_induced_packing_statement).

Theorem g294_gpip_not_trivially_true : g294_gpip_ntt_claim.
Proof.
split; last by move=> h G H vt ind _; exact: h G H vt ind.
move=> h; have [n [_ [P [pP copies]]]] := h 'K_3 'K_2 (@g294_Kn_vt 3) g294_K2_in_K3.
by apply: (@g294_K3_K2_no_packing n); exists P.
Qed.

(** ** helper_sanity *)

(** The graph on 'I_3 whose one edge joins 1 and 2 (vertex 0 is isolated). *)
Definition g294_K1K2_rel : rel 'I_3 := fun u v => (val u + val v == 3)%N.

Lemma g294_K1K2_sym : symmetric g294_K1K2_rel.
Proof. by move=> u v; rewrite /g294_K1K2_rel addnC. Qed.

Lemma g294_K1K2_irrefl : irreflexive g294_K1K2_rel.
Proof. by move=> u; rewrite /g294_K1K2_rel addnn; case: (val u) => [|[|k]]. Qed.

Definition g294_K1K2 : sgraph := SGraph g294_K1K2_sym g294_K1K2_irrefl.

Lemma g294_K1K2_not_vt : ~ x294_vertex_transitive g294_K1K2.
Proof.
move=> vt; case: (vt ord0 (inord 1)) => f [[[g fK gK] fe] f0].
have e12 : (inord 1 : g294_K1K2) -- inord 2 by rewrite /edge_rel /= /g294_K1K2_rel /= !inordK.
have := fe ord0 (g (inord 2)); rewrite f0 gK e12 /edge_rel /= /g294_K1K2_rel /= => /esym/eqP h3.
by move: (ltn_ord (g (inord 2))); rewrite add0n in h3; rewrite h3 ltnn.
Qed.

Lemma g294_box_power1 (G : sgraph) : inhabited (x294_box_power G 1 ≃ G).
Proof.
pose f : x294_box_power G 1 -> G := snd.
pose g : G -> x294_box_power G 1 := fun x => (ord0, x).
have fK : cancel f g by case=> a x; rewrite /f /g /= (ord1 a).
have gK : cancel g f by [].
constructor; apply: (@Diso' (x294_box_power G 1) G f g fK gK) => -[a x] [b y].
by rewrite /edge_rel /= /box_rel /= (ord1 a) (ord1 b) eqxx /= andbF orbF.
Qed.

Definition g294_helper_claim : Prop :=
  [/\ forall (n : nat) (x y : 'K_n), x294_graph_automorphism (g294_swap x y),
      x294_vertex_transitive ('K_2),
      ~ x294_vertex_transitive g294_K1K2,
      forall (G : sgraph) (n : nat), #|x294_box_power G n| = (#|G| ^ n)%N &
      forall G : sgraph, inhabited (x294_box_power G 1 ≃ G)].

Theorem g294_helper_sanity : g294_helper_claim.
Proof.
split; [exact: g294_swap_aut | exact: g294_Kn_vt | exact: g294_K1K2_not_vt
       | exact: g294_box_power_card | exact: g294_box_power1].
Qed.

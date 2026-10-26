(** * Spectral.foundations.triangle_free_srg -- the seven known triangle-free strongly regular graphs

    The OPG problem "Is there an eighth triangle free strongly regular graph?" names seven graphs: the five-cycle,
    the Petersen, Clebsch, Hoffman-Singleton, Gewirtz and Higman-Sims graphs, and the (77,16,0,4) subgraph of the
    Higman-Sims graph (the M22 graph).  This file gives each one as an explicit graph and checks in the kernel that it
    is triangle-free with its strongly regular parameters (GTBase.strongly_regular.strongly_regular_parameters).
    - [ord_graph n conn]: the graph on ['I_n] whose adjacency is [(x != y) && conn (val x) (val y)] for a symmetric
      natural relation [conn]; [srg_checkP] and [tf_checkP] reflect Boolean checks over [iota 0 n] (evaluated with
      [vm_compute]) into the parameters and triangle-freeness, for every graph on ['I_n] with that adjacency.
    - C5 (5,2,0,1); Petersen = GTBase.petersen.petersen_ord (10,3,0,1); Clebsch = the folded 5-cube (16,5,0,2);
      Hoffman-Singleton = Robertson's pentagons and pentagrams (50,7,0,1).
    - [s3622_hexads]: the 77 blocks of the Steiner system S(3,6,22), with the Steiner property checked
      ([s3622_steiner]); M22 = the hexads adjacent when disjoint (77,16,0,4); Gewirtz = the 56 hexads avoiding one
      point (56,10,0,2); Higman-Sims = a new point, the 22 points and the 77 hexads (100,22,0,6).
    - [known_triangle_free_srg : 'I_7 -> sgraph] lists them in that order; the seven vertex counts are distinct.
    The hexad table was generated off-line from the extended binary Golay code; the kernel checks below are what
    certify it.  Used by D5's [triangle_free_strongly_regular_graphs_statement] (an eighth graph). *)
From mathcomp Require Import all_boot.
From GraphTheory Require Import sgraph.
From GTBase Require Import base strongly_regular petersen.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section OrdGraph.
Variables (n : nat) (conn : nat -> nat -> bool).
Hypothesis connC : forall a b, conn a b = conn b a.

Definition ord_adj (x y : 'I_n) : bool := (x != y) && conn (val x) (val y).

Lemma ord_adj_sym : symmetric ord_adj.
Proof. by move=> x y; rewrite /ord_adj eq_sym connC. Qed.

Lemma ord_adj_irrefl : irreflexive ord_adj.
Proof. by move=> x; rewrite /ord_adj eqxx. Qed.

Definition ord_graph : sgraph := SGraph ord_adj_sym ord_adj_irrefl.

(** Natural-number adjacency, with the inequality built in. *)
Definition nadj (a b : nat) : bool := (a != b) && conn a b.

Lemma iota_ord (x : 'I_n) : val x \in iota 0 n.
Proof. by rewrite mem_iota /= add0n ltn_ord. Qed.

(** The number of [w < n] satisfying a natural predicate is a count over [iota 0 n]. *)
Lemma card_ord_pred (p : pred nat) : #|[set w : 'I_n | p (val w)]| = count p (iota 0 n).
Proof.
rewrite cardsE cardE -size_filter /enum_mem -enumT /=.
by rewrite !size_filter -val_enum_ord count_map.
Qed.

Lemma ord_adjE (x y : 'I_n) : ord_adj x y = (x != y) && conn (val x) (val y).
Proof. by []. Qed.

Section Rel.
Variables (r : rel 'I_n) (rsym : symmetric r) (rirr : irreflexive r).
Hypothesis rE : forall x y, r x y = (x != y) && conn (val x) (val y).

Lemma ord_graph_card_nbr (x : SGraph rsym rirr) : #|N(x)| = count (nadj (val x)) (iota 0 n).
Proof.
rewrite -card_ord_pred; apply: eq_card => y; rewrite !inE.
exact: rE.
Qed.

Lemma ord_graph_card_common (x y : SGraph rsym rirr) :
  #|common_nbr x y| = count (fun w => nadj (val x) w && nadj (val y) w) (iota 0 n).
Proof.
rewrite -card_ord_pred; apply: eq_card => z; rewrite !inE.
by rewrite /edge_rel /= !rE.
Qed.

(** The Boolean check, over natural numbers below [n] only. *)
Definition srg_check (k lam mu : nat) : bool :=
  all (fun a => count (nadj a) (iota 0 n) == k) (iota 0 n) &&
  all (fun a => all (fun b =>
         (a == b) || (count (fun w => nadj a w && nadj b w) (iota 0 n) == if conn a b then lam else mu))
       (iota 0 n)) (iota 0 n).

Lemma srg_checkP k lam mu : srg_check k lam mu -> strongly_regular_parameters (SGraph rsym rirr) k lam mu.
Proof.
case/andP=> /allP hk /allP hp; split.
- move=> x; rewrite ord_graph_card_nbr; apply/eqP/hk.
  by rewrite mem_iota /= add0n ltn_ord.
- move=> x y xy; rewrite ord_graph_card_common.
  have /allP := hp (val x) (iota_ord _).
  move=> /(_ (val y) (iota_ord _)).
  move: xy; rewrite /edge_rel /= rE => /andP[xy ->].
  by rewrite (inj_eq val_inj) (negbTE xy) /= => /eqP.
- move=> x y xy nxy; rewrite ord_graph_card_common.
  have /allP := hp (val x) (iota_ord _).
  move=> /(_ (val y) (iota_ord _)).
  move: nxy; rewrite /edge_rel /= rE xy /= => /negbTE ->.
  by rewrite (inj_eq val_inj) (negbTE xy) /= => /eqP.
Qed.

Definition tf_check : bool :=
  all (fun a => all (fun b => ~~ nadj a b || ~~ has (fun w => nadj a w && nadj b w) (iota 0 n))
       (iota 0 n)) (iota 0 n).

Lemma tf_checkP : tf_check -> triangle_free (SGraph rsym rirr).
Proof.
move=> /allP h x y z xy yz zx.
have /allP := h (val x) (iota_ord _).
move=> /(_ (val y) (iota_ord _)).
have nxy : nadj (val x) (val y) by move: xy; rewrite /edge_rel /= rE /nadj.
rewrite nxy /= => /hasPn /(_ (val z) (iota_ord _)).
rewrite /nadj.
move: zx yz; rewrite /edge_rel /= !rE => /andP[zx czx] /andP[yz cyz].
by rewrite !(inj_eq val_inj) eq_sym zx connC czx yz cyz.
Qed.

End Rel.

End OrdGraph.
(** ** C5: the five-cycle, (5,2,0,1). *)
Definition c5_conn (a b : nat) : bool := (b == (a.+1 %% 5)) || (a == (b.+1 %% 5)).
Lemma c5_connC a b : c5_conn a b = c5_conn b a.
Proof. by rewrite /c5_conn orbC. Qed.
Definition c5_graph : sgraph := ord_graph 5 c5_connC.
Lemma c5_srg : strongly_regular_parameters c5_graph 2 0 1.
Proof. by apply: (srg_checkP _ _ (ord_adjE _)); vm_compute. Qed.
Lemma c5_tf : triangle_free c5_graph.
Proof. by apply: (tf_checkP c5_connC (ord_adjE _)); vm_compute. Qed.

(** ** Clebsch (the folded 5-cube): 4-bit words, adjacent at Hamming distance 1 or 4, (16,5,0,2). *)
Definition hamming4 (a b : nat) : nat := count (fun i => odd (a %/ 2 ^ i) != odd (b %/ 2 ^ i)) (iota 0 4).
Definition clebsch_conn (a b : nat) : bool := (hamming4 a b == 1) || (hamming4 a b == 4).
Lemma clebsch_connC a b : clebsch_conn a b = clebsch_conn b a.
Proof.
rewrite /clebsch_conn; suff -> : hamming4 a b = hamming4 b a by [].
by apply: eq_count => i; rewrite eq_sym.
Qed.
Definition clebsch_graph : sgraph := ord_graph 16 clebsch_connC.
Lemma clebsch_srg : strongly_regular_parameters clebsch_graph 5 0 2.
Proof. by apply: (srg_checkP _ _ (ord_adjE _)); vm_compute. Qed.
Lemma clebsch_tf : triangle_free clebsch_graph.
Proof. by apply: (tf_checkP clebsch_connC (ord_adjE _)); vm_compute. Qed.

(** ** Hoffman-Singleton (Robertson): vertex 25 t + 5 h + j is the j-th vertex of the pentagon P_h (t = 0) or of the
    pentagram Q_h (t = 1); P_h^j ~ P_h^(j+-1), Q_i^j ~ Q_i^(j+-2), P_h^j ~ Q_i^(h i + j), all indices mod 5.
    (50,7,0,1). *)
Definition hs_dir (a b : nat) : bool :=
  let ta := a %/ 25 in let ha := (a %% 25) %/ 5 in let ja := a %% 5 in
  let tb := b %/ 25 in let hb := (b %% 25) %/ 5 in let jb := b %% 5 in
  [|| [&& ta == 0, tb == 0, ha == hb & jb == (ja + 1) %% 5],
      [&& ta == 1, tb == 1, ha == hb & jb == (ja + 2) %% 5]
    | [&& ta == 0, tb == 1 & jb == (ha * hb + ja) %% 5]].
Definition hs_conn (a b : nat) : bool := hs_dir a b || hs_dir b a.
Lemma hs_connC a b : hs_conn a b = hs_conn b a.
Proof. by rewrite /hs_conn orbC. Qed.
Definition hoffman_singleton_graph : sgraph := ord_graph 50 hs_connC.
Lemma hoffman_singleton_srg : strongly_regular_parameters hoffman_singleton_graph 7 0 1.
Proof. by apply: (srg_checkP _ _ (ord_adjE _)); vm_compute. Qed.
Lemma hoffman_singleton_tf : triangle_free hoffman_singleton_graph.
Proof. by apply: (tf_checkP hs_connC (ord_adjE _)); vm_compute. Qed.

(** ** Petersen: GTBase.petersen.petersen_ord, (10,3,0,1). *)
Lemma petersen_ord_relE (x y : 'I_10) : petersen_ord_adj x y = (x != y) && petersen_conn (val x) (val y).
Proof. by []. Qed.
Lemma petersen_srg : strongly_regular_parameters petersen_ord 3 0 1.
Proof. by apply: (srg_checkP _ _ petersen_ord_relE); vm_compute. Qed.
Lemma petersen_tf : triangle_free petersen_ord.
Proof. by apply: (tf_checkP petersen_connC petersen_ord_relE); vm_compute. Qed.

(** ** The Steiner system S(3,6,22): 77 hexads on the points 0..21 (generated off-line from the extended Golay
    code: the octads through two fixed coordinates, without them; verified below). *)
Definition s3622_hexads : seq (seq nat) :=
  [:: [:: 0; 1; 2; 4; 13; 16];
      [:: 0; 1; 3; 12; 15; 21];
      [:: 0; 1; 5; 6; 18; 20];
      [:: 0; 1; 7; 10; 11; 17];
      [:: 0; 1; 8; 9; 14; 19];
      [:: 0; 2; 3; 10; 18; 19];
      [:: 0; 2; 5; 7; 9; 12];
      [:: 0; 2; 6; 8; 15; 17];
      [:: 0; 2; 11; 14; 20; 21];
      [:: 0; 3; 4; 6; 7; 14];
      [:: 0; 3; 5; 8; 11; 16];
      [:: 0; 3; 9; 13; 17; 20];
      [:: 0; 4; 5; 17; 19; 21];
      [:: 0; 4; 8; 10; 12; 20];
      [:: 0; 4; 9; 11; 15; 18];
      [:: 0; 5; 10; 13; 14; 15];
      [:: 0; 6; 9; 10; 16; 21];
      [:: 0; 6; 11; 12; 13; 19];
      [:: 0; 7; 8; 13; 18; 21];
      [:: 0; 7; 15; 16; 19; 20];
      [:: 0; 12; 14; 16; 17; 18];
      [:: 1; 2; 3; 7; 8; 20];
      [:: 1; 2; 5; 11; 15; 19];
      [:: 1; 2; 6; 10; 12; 14];
      [:: 1; 2; 9; 17; 18; 21];
      [:: 1; 3; 4; 5; 9; 10];
      [:: 1; 3; 6; 16; 17; 19];
      [:: 1; 3; 11; 13; 14; 18];
      [:: 1; 4; 6; 8; 11; 21];
      [:: 1; 4; 7; 12; 18; 19];
      [:: 1; 4; 14; 15; 17; 20];
      [:: 1; 5; 7; 14; 16; 21];
      [:: 1; 5; 8; 12; 13; 17];
      [:: 1; 6; 7; 9; 13; 15];
      [:: 1; 8; 10; 15; 16; 18];
      [:: 1; 9; 11; 12; 16; 20];
      [:: 1; 10; 13; 19; 20; 21];
      [:: 2; 3; 4; 11; 12; 17];
      [:: 2; 3; 5; 6; 13; 21];
      [:: 2; 3; 9; 14; 15; 16];
      [:: 2; 4; 5; 8; 14; 18];
      [:: 2; 4; 6; 9; 19; 20];
      [:: 2; 4; 7; 10; 15; 21];
      [:: 2; 5; 10; 16; 17; 20];
      [:: 2; 6; 7; 11; 16; 18];
      [:: 2; 7; 13; 14; 17; 19];
      [:: 2; 8; 9; 10; 11; 13];
      [:: 2; 8; 12; 16; 19; 21];
      [:: 2; 12; 13; 15; 18; 20];
      [:: 3; 4; 8; 13; 15; 19];
      [:: 3; 4; 16; 18; 20; 21];
      [:: 3; 5; 7; 15; 17; 18];
      [:: 3; 5; 12; 14; 19; 20];
      [:: 3; 6; 8; 9; 12; 18];
      [:: 3; 6; 10; 11; 15; 20];
      [:: 3; 7; 9; 11; 19; 21];
      [:: 3; 7; 10; 12; 13; 16];
      [:: 3; 8; 10; 14; 17; 21];
      [:: 4; 5; 6; 12; 15; 16];
      [:: 4; 5; 7; 11; 13; 20];
      [:: 4; 6; 10; 13; 17; 18];
      [:: 4; 7; 8; 9; 16; 17];
      [:: 4; 9; 12; 13; 14; 21];
      [:: 4; 10; 11; 14; 16; 19];
      [:: 5; 6; 7; 8; 10; 19];
      [:: 5; 6; 9; 11; 14; 17];
      [:: 5; 8; 9; 15; 20; 21];
      [:: 5; 9; 13; 16; 18; 19];
      [:: 5; 10; 11; 12; 18; 21];
      [:: 6; 7; 12; 17; 20; 21];
      [:: 6; 8; 13; 14; 16; 20];
      [:: 6; 14; 15; 18; 19; 21];
      [:: 7; 8; 11; 12; 14; 15];
      [:: 7; 9; 10; 14; 18; 20];
      [:: 8; 11; 17; 18; 19; 20];
      [:: 9; 10; 12; 15; 17; 19];
      [:: 11; 13; 15; 16; 17; 21]].

Definition hexad (i : nat) : seq nat := nth [::] s3622_hexads i.

(** Every hexad is a 6-subset of {0..21}, and every 3-subset of {0..21} lies in exactly one hexad. *)
Lemma s3622_steiner :
  [&& size s3622_hexads == 77,
      all (fun h => (size h == 6) && uniq h && all (fun p => p < 22) h) s3622_hexads &
      all (fun a => all (fun b => all (fun c =>
             (a < b < c) ==> (count (fun h => [&& a \in h, b \in h & c \in h]) s3622_hexads == 1))
           (iota 0 22)) (iota 0 22)) (iota 0 22)].
Proof. by vm_compute. Qed.

Definition hexads_disjoint (i j : nat) : bool := ~~ has (mem (hexad j)) (hexad i).
Lemma hexads_disjointC i j : hexads_disjoint i j = hexads_disjoint j i.
Proof. by rewrite /hexads_disjoint has_sym. Qed.

(** ** M22 graph: the 77 hexads, adjacent when disjoint, (77,16,0,4). *)
Definition m22_graph : sgraph := ord_graph 77 hexads_disjointC.
Lemma m22_srg : strongly_regular_parameters m22_graph 16 0 4.
Proof. by apply: (srg_checkP _ _ (ord_adjE _)); vm_compute. Qed.

(** Parameters with [lam = 0] give triangle-freeness. *)
Lemma srg_lam0_tf (G : sgraph) k mu : strongly_regular_parameters G k 0 mu -> triangle_free G.
Proof.
case=> _ hl _ x y z xy yz zx.
have := hl x y xy; move/eqP; rewrite cards_eq0 => /eqP/setP/(_ z).
by rewrite !inE (sg_sym x z) zx yz.
Qed.

Lemma m22_tf : triangle_free m22_graph.
Proof. exact: srg_lam0_tf m22_srg. Qed.

(** ** Gewirtz: the 56 hexads avoiding the point 0, adjacent when disjoint, (56,10,0,2).  In the sorted table the
    hexads through 0 are exactly the first 21. *)
Lemma s3622_point0 : all (fun i => (0 \notin hexad i) == (21 <= i)) (iota 0 77).
Proof. by vm_compute. Qed.
Definition gewirtz_conn (a b : nat) : bool := hexads_disjoint (a + 21) (b + 21).
Lemma gewirtz_connC a b : gewirtz_conn a b = gewirtz_conn b a.
Proof. by rewrite /gewirtz_conn hexads_disjointC. Qed.
Definition gewirtz_graph : sgraph := ord_graph 56 gewirtz_connC.
Lemma gewirtz_srg : strongly_regular_parameters gewirtz_graph 10 0 2.
Proof. by apply: (srg_checkP _ _ (ord_adjE _)); vm_compute. Qed.

(** ** Higman-Sims: vertex 0 is a new point, 1..22 are the points 0..21, 23..99 the hexads; the new point is
    adjacent to every point, a point to the hexads through it, two hexads when disjoint, (100,22,0,6). *)
Definition hisi_dir (a b : nat) : bool :=
  [|| (a == 0) && (1 <= b <= 22),
      [&& 1 <= a <= 22, 23 <= b & a.-1 \in hexad (b - 23)]
    | [&& 23 <= a, 23 <= b & hexads_disjoint (a - 23) (b - 23)]].
Definition hisi_conn (a b : nat) : bool := hisi_dir a b || hisi_dir b a.
Lemma hisi_connC a b : hisi_conn a b = hisi_conn b a.
Proof. by rewrite /hisi_conn orbC. Qed.
Definition higman_sims_graph : sgraph := ord_graph 100 hisi_connC.
Lemma higman_sims_srg : strongly_regular_parameters higman_sims_graph 22 0 6.
Proof. by apply: (srg_checkP _ _ (ord_adjE _)); vm_compute. Qed.


Lemma gewirtz_tf : triangle_free gewirtz_graph.
Proof. exact: srg_lam0_tf gewirtz_srg. Qed.

Lemma higman_sims_tf : triangle_free higman_sims_graph.
Proof. exact: srg_lam0_tf higman_sims_srg. Qed.

(** ** The list of the seven known graphs *)
Definition known_triangle_free_srg (i : 'I_7) : sgraph :=
  match val i with
  | 0 => c5_graph
  | 1 => petersen_ord
  | 2 => clebsch_graph
  | 3 => hoffman_singleton_graph
  | 4 => gewirtz_graph
  | 5 => m22_graph
  | _ => higman_sims_graph
  end.

(** Each is triangle-free and strongly regular with [lam = 0] and [0 < mu < k]. *)
Lemma known_triangle_free_srg_spec (i : 'I_7) :
  triangle_free (known_triangle_free_srg i) /\
  exists k mu, [/\ strongly_regular_parameters (known_triangle_free_srg i) k 0 mu, 0 < mu & mu < k].
Proof.
case: i => [[|[|[|[|[|[|[|//]]]]]]]] ? /=.
- by split; [exact: c5_tf | exists 2, 1; split => //; exact: c5_srg].
- by split; [exact: petersen_tf | exists 3, 1; split => //; exact: petersen_srg].
- by split; [exact: clebsch_tf | exists 5, 2; split => //; exact: clebsch_srg].
- by split; [exact: hoffman_singleton_tf | exists 7, 1; split => //; exact: hoffman_singleton_srg].
- by split; [exact: gewirtz_tf | exists 10, 2; split => //; exact: gewirtz_srg].
- by split; [exact: m22_tf | exists 16, 4; split => //; exact: m22_srg].
- by split; [exact: higman_sims_tf | exists 22, 6; split => //; exact: higman_sims_srg].
Qed.

(** Their vertex counts are 5, 10, 16, 50, 56, 77 and 100, so they are pairwise non-isomorphic. *)
Lemma known_triangle_free_srg_card (i : 'I_7) :
  #|known_triangle_free_srg i| = nth 0 [:: 5; 10; 16; 50; 56; 77; 100] i.
Proof. by case: i => [[|[|[|[|[|[|[|//]]]]]]]] ? /=; rewrite card_ord. Qed.

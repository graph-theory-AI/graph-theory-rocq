(** * GTBase.path_graphs — the path graph P_n on the ordinals 'I_n

    Library migration B21, family [ordinal-path] (meta/library_primitives/ordinal-path.json).  The
    canonical constructor is [ordinal_path n], the simple graph on ['I_n] whose edges join
    consecutive indices in either order: [ordinal_path_rel i j := ((val i).+1 == val j) ||
    ((val j).+1 == val i)], packaged with upstream [SGraph] from the symmetry and irreflexivity
    proofs below.  The migrated sources are the relations [Packing.conjectures.X18.x18_path_rel],
    [Packing.conjectures.X226.x226_path_rel], [Hom.conjectures.U3.pth_rel] and
    [Chromatic.conjectures.X170.x170_p4_edge] (the case n = 4) and the constructors
    [Packing.conjectures.X18.x18_path_graph], [Packing.conjectures.X226.x226_path_graph] and
    [Hom.conjectures.U3.path_graph].  The two Packing relations carry an [i != j] guard, redundant
    because consecutive indices are distinct ([ordinal_path_rel_guardedE], a pointwise equality, not a
    conversion); the Hom and X170 relations are the raw one.  A constructor built from any pointwise
    equal relation and its own symmetry/irreflexivity proofs is isomorphic to the canonical graph
    through upstream [eq_diso] ([eq_ordinal_path_diso], [guarded_ordinal_path_diso]). The frozen legacy
    constructors are not convertible to the canonical graph, as checked by the independent negative probes.

    Contract kept exactly: [n] vertices ([card_ordinal_path]), the empty graph for n = 0, no edge for
    n = 1, one edge for n = 2, no loop, no modular wrap (the first and last vertices of P_n, n >= 3,
    are not adjacent: [ordinal_path_ends]) and no positivity premise.  Bridges: P_n has maximum
    degree at most two ([ordinal_path_Delta]), is connected ([ordinal_path_connected]) and is a forest
    ([ordinal_path_is_forest], through upstream [K3_free_forest]: the branch sets of a K_3 minor map
    would be three pairwise adjacent intervals of 'I_n, and the middle one separates the other two),
    hence a tree ([ordinal_path_is_tree]) and a B9 [path_tree] ([ordinal_path_path_tree]).

    Distinct, untouched: the cyclic [GTBase.base.cyc_rel] / [cycle_graph] (modular successor), the
    join constructor [Minor.conjectures.X198.x198_join_path_rel] on a sum carrier, sequence paths and
    path indices, and B9's predicate [path_tree] itself.  This module imports [GTBase.base] and
    [GTBase.path_trees] and is not re-exported by [base]. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph minor.
From GTBase Require Import base path_trees.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section OrdinalPath.
Variable n : nat.
Implicit Types i j k : 'I_n.

(** Consecutive indices in either order: the raw relation, with no guard. *)
Definition ordinal_path_rel (i j : 'I_n) : bool :=
  ((val i).+1 == val j) || ((val j).+1 == val i).

Lemma ordinal_path_rel_sym : symmetric ordinal_path_rel.
Proof. by move=> i j; rewrite /ordinal_path_rel orbC. Qed.

Lemma ordinal_path_rel_irrefl : irreflexive ordinal_path_rel.
Proof. by move=> i; rewrite /ordinal_path_rel orbb (gtn_eqF (ltnSn _)). Qed.

(** The path graph P_n. *)
Definition ordinal_path : sgraph := SGraph ordinal_path_rel_sym ordinal_path_rel_irrefl.

Lemma ordinal_path_edgeE (i j : ordinal_path) :
  (i -- j) = ((val i).+1 == val j) || ((val j).+1 == val i).
Proof. by []. Qed.

Lemma ordinal_path_relP i j :
  reflect (val j = (val i).+1 \/ val i = (val j).+1) (ordinal_path_rel i j).
Proof.
apply: (iffP orP) => [[/eqP e | /eqP e] | [e | e]].
- by left; rewrite e.
- by right; rewrite e.
- by left; apply/eqP; rewrite e.
- by right; apply/eqP; rewrite e.
Qed.

(** The Packing guard [i != j] is redundant: consecutive indices are distinct.  This is a
    pointwise equality of Boolean relations, the whole content of the guarded/unguarded bridge. *)
Lemma ordinal_path_rel_guardedE i j :
  (i != j) && ordinal_path_rel i j = ordinal_path_rel i j.
Proof. by case: (eqVneq i j) => [-> | //]; rewrite ordinal_path_rel_irrefl. Qed.

Lemma ordinal_path_edge_guardedE (i j : ordinal_path) :
  (i -- j) = (i != j) && (((val i).+1 == val j) || ((val j).+1 == val i)).
Proof. exact: esym (ordinal_path_rel_guardedE i j). Qed.

Lemma card_ordinal_path : #|ordinal_path| = n.
Proof. exact: card_ord. Qed.

Lemma ordinal_path_no_loop (i : ordinal_path) : ~~ (i -- i).
Proof. by rewrite ordinal_path_edgeE orbb (gtn_eqF (ltnSn _)). Qed.

(** Each vertex has at most two neighbours: its predecessor and its successor. *)
Lemma ordinal_path_degree (i : ordinal_path) : #|N(i)| <= 2.
Proof.
pose A := [set j : 'I_n | val j == (val i).+1].
pose B := [set j : 'I_n | (val j).+1 == val i].
have le1 (S : {set 'I_n}) : (forall j k, j \in S -> k \in S -> val j = val k) -> #|S| <= 1.
  by move=> h; apply/card_le1_eqP => j k jS kS; apply: val_inj; exact: h.
have sub : N(i) \subset A :|: B.
  apply/subsetP => j; rewrite !inE ordinal_path_edgeE => /orP[/eqP e | /eqP e].
  - by rewrite e eqxx.
  - by rewrite e eqxx orbT.
have hA : #|A| <= 1.
  by apply: le1 => j k; rewrite !inE => /eqP ej /eqP ek; rewrite ej ek.
have hB : #|B| <= 1.
  by apply: le1 => j k; rewrite !inE => /eqP ej /eqP ek; apply: succn_inj; rewrite ej ek.
apply: leq_trans (subset_leq_card sub) _.
apply: leq_trans (leq_card_setU _ _) _.
exact: leq_add hA hB.
Qed.

End OrdinalPath.

Lemma ordinal_path_Delta n : Delta (ordinal_path n) <= 2.
Proof. by apply/bigmax_leqP => i _; exact: ordinal_path_degree. Qed.

(** ** Small cases and the no-wrap contract *)

(** P_0 has no vertex. *)
Lemma ordinal_path0_empty : #|ordinal_path 0| = 0.
Proof. exact: card_ord. Qed.

(** P_1 has one vertex and no edge. *)
Lemma ordinal_path1_edgeless (i j : ordinal_path 1) : ~~ (i -- j).
Proof. by rewrite ordinal_path_edgeE (fintype.ord1 i) (fintype.ord1 j). Qed.

(** P_2 is the single edge 0 -- 1. *)
Lemma ordinal_path2_edge : (ord0 : ordinal_path 2) -- ord_max.
Proof. by rewrite ordinal_path_edgeE. Qed.

(** No modular wrap: for n >= 3 the first and the last vertex are not adjacent. *)
Lemma ordinal_path_ends n (i j : ordinal_path n) :
  2 < n -> val i = 0 -> val j = n.-1 -> ~~ (i -- j).
Proof.
case: n i j => [|[|[|n]]] // i j _ i0 jn.
by rewrite ordinal_path_edgeE i0 jn.
Qed.

Lemma ordinal_path3_no_wrap : ~~ ((ord0 : ordinal_path 3) -- ord_max).
Proof. by rewrite ordinal_path_edgeE. Qed.

(** The four-vertex path P_4 (the X170 specialisation). *)
Lemma ordinal_path4_edgeE (i j : ordinal_path 4) :
  (i -- j) = ((val i).+1 == val j) || ((val j).+1 == val i).
Proof. exact: ordinal_path_edgeE. Qed.

(** ** Graph compatibility of other constructors (upstream [eq_diso]) *)

(** Any constructor from a pointwise equal relation is isomorphic to P_n (the identity map). *)
Lemma eq_ordinal_path_diso n (r : rel 'I_n) (rs : symmetric r) (ri : irreflexive r) :
  (forall i j : 'I_n, r i j = ordinal_path_rel i j) -> SGraph rs ri ≃ ordinal_path n.
Proof. by move=> rE; apply: eq_diso => i j; rewrite rE. Qed.

(** In particular the guarded Packing constructors. *)
Lemma guarded_ordinal_path_diso n (r : rel 'I_n) (rs : symmetric r) (ri : irreflexive r) :
  (forall i j : 'I_n, r i j = (i != j) && ordinal_path_rel i j) -> SGraph rs ri ≃ ordinal_path n.
Proof. by move=> rE; apply: eq_ordinal_path_diso => i j; rewrite rE ordinal_path_rel_guardedE. Qed.

(** ** Connectivity *)

Lemma ordinal_path_connect_add n (k : nat) (i j : ordinal_path n) :
  val i + k = val j -> connect (--) i j.
Proof.
elim: k i j => [|k IH] i j e.
  by have -> : i = j by apply/val_inj; rewrite -e addn0.
have lt : val i + k < n by apply: leq_ltn_trans (ltn_ord j); rewrite -e addnS.
apply: connect_trans (IH i (Ordinal lt) erefl) _.
by apply: connect1; rewrite ordinal_path_edgeE /= -e addnS eqxx.
Qed.

Lemma ordinal_path_connected n : connected [set: ordinal_path n].
Proof.
apply: connectedTI => i j; have [le | lt] := leqP (val i) (val j).
  by apply: (@ordinal_path_connect_add n (val j - val i) i j); rewrite subnKC.
by rewrite sconnect_sym; apply: (@ordinal_path_connect_add n (val i - val j) j i); rewrite subnKC // ltnW.
Qed.

(** ** P_n is a forest: no K_3 minor *)

Section PathForest.
Variable n : nat.
Local Notation P := (ordinal_path n).

Lemma ordinal_path_disj_mem (A B : {set P}) (u : P) :
  [disjoint A & B] -> u \in A -> u \in B -> False.
Proof.
rewrite -setI_eq0 => /eqP/setP/(_ u); rewrite !inE => H uA uB.
by move: H; rewrite uA uB.
Qed.

(** A path inside [S] from [i] to a vertex beyond [k] passes through [k]. *)
Lemma ordinal_path_between (S : {set P}) (k : P) (p : seq P) :
  forall i : P, path (restrict S (--)) i p ->
  i \in S -> val i <= val k -> val k <= val (last i p) -> k \in S.
Proof.
elim: p => [|z p IH] i /=.
  move=> _ iS lik lki.
  by have -> : k = i by apply: val_inj; apply/eqP; rewrite eqn_leq lki lik.
case/andP => /andP[/andP[_ zS] iz] pth iS lik lkj.
have [ki | ki] := eqVneq (val k) (val i).
  by have -> : k = i by apply: val_inj.
have lik' : val i < val k by rewrite ltn_neqAle eq_sym ki lik.
apply: (IH z pth zS) => //.
move: iz; rewrite ordinal_path_edgeE => /orP[/eqP ez | /eqP ez].
  by rewrite -ez.
by apply: leq_trans (ltnW lik'); rewrite -ez.
Qed.

(** Connected vertex sets of P_n are intervals of 'I_n. *)
Lemma ordinal_path_interval (S : {set P}) (i j k : P) :
  connected S -> i \in S -> j \in S -> val i <= val k -> val k <= val j -> k \in S.
Proof.
move=> cS iS jS lik lkj.
have /connectP[p pth lst] := cS i j iS jS.
by apply: (ordinal_path_between pth iS lik); rewrite -lst.
Qed.

(** [A] lies entirely below [B]. *)
Definition ordinal_path_lt_set (A B : {set P}) : Prop :=
  forall a b : P, a \in A -> b \in B -> val a < val b.

Lemma ordinal_path_sep (A B : {set P}) (x y : P) :
  connected A -> connected B -> [disjoint A & B] ->
  x \in A -> y \in B -> val x < val y -> ordinal_path_lt_set A B.
Proof.
move=> cA cB dAB xA yB lxy a b aA bB.
have step1 : val a < val y.
  rewrite ltnNge; apply/negP => lya.
  have yA : y \in A by apply: (ordinal_path_interval cA xA aA (ltnW lxy) lya).
  exact: (ordinal_path_disj_mem dAB yA yB).
rewrite ltnNge; apply/negP => lba.
have aB : a \in B by apply: (ordinal_path_interval cB bB yB lba (ltnW step1)).
exact: (ordinal_path_disj_mem dAB aA aB).
Qed.

(** Two disjoint nonempty connected sets are linearly ordered. *)
Lemma ordinal_path_lt_total (A B : {set P}) :
  connected A -> connected B -> [disjoint A & B] -> A != set0 -> B != set0 ->
  ordinal_path_lt_set A B \/ ordinal_path_lt_set B A.
Proof.
move=> cA cB dAB /set0Pn[x xA] /set0Pn[y yB].
have nxy : val x != val y.
  apply/eqP => e; apply: (ordinal_path_disj_mem dAB xA).
  by have -> : x = y by apply: val_inj.
have [lxy | lyx] := ltnP (val x) (val y).
  by left; exact: (ordinal_path_sep cA cB dAB xA yB lxy).
right; apply: (ordinal_path_sep cB cA _ yB xA) => //.
  by rewrite disjoint_sym.
by rewrite ltn_neqAle eq_sym nxy lyx.
Qed.

(** Three pairwise adjacent intervals cannot exist: the middle one separates the others. *)
Lemma ordinal_path_K3_free : ~ minor P 'K_3.
Proof.
case/minorRE => phi [phi0 phiC phiD phiN].
have mid : forall i j k : ('K_3),
    ordinal_path_lt_set (phi i) (phi j) -> ordinal_path_lt_set (phi j) (phi k) ->
    i != k -> False.
  move=> i j k lij ljk ik.
  have /neighborP[u [w [uA wC uw]]] : neighbor (phi i) (phi k) by exact: phiN ik.
  have /set0Pn[m mB] := phi0 j.
  have l1 := lij u m uA mB.
  have l2 := ljk m w mB wC.
  move: uw; rewrite ordinal_path_edgeE => /orP[/eqP e | /eqP e].
    have h2 : (val u).+1 < val w by apply: leq_ltn_trans l2.
    by rewrite -e ltnn in h2.
  have h2 : val u < val w by apply: ltn_trans l1 l2.
  have h3 : val w < val u by rewrite -e.
  by move: (ltn_trans h2 h3); rewrite ltnn.
have D : forall i j : ('K_3),
    i != j -> ordinal_path_lt_set (phi i) (phi j) \/ ordinal_path_lt_set (phi j) (phi i).
  move=> i j ij; apply: ordinal_path_lt_total; by [exact: phiC | exact: phiD ij | exact: phi0].
pose k0 : 'K_3 := ord0.
pose k1 : 'K_3 := @Ordinal 3 1 isT.
pose k2 : 'K_3 := @Ordinal 3 2 isT.
case: (D k0 k1 isT) => d01; case: (D k0 k2 isT) => d02; case: (D k1 k2 isT) => d12.
- exact: (mid k0 k1 k2 d01 d12 isT).
- exact: (mid k0 k2 k1 d02 d12 isT).
- exact: (mid k0 k1 k2 d01 d12 isT).
- exact: (mid k2 k0 k1 d02 d01 isT).
- exact: (mid k1 k0 k2 d01 d02 isT).
- exact: (mid k1 k0 k2 d01 d02 isT).
- exact: (mid k1 k2 k0 d12 d02 isT).
- exact: (mid k2 k1 k0 d12 d01 isT).
Qed.

Lemma ordinal_path_is_forest : is_forest [set: P].
Proof. exact: (proj1 (K3_free_forest _) ordinal_path_K3_free). Qed.

End PathForest.

(** ** Tree and path-tree bridges *)

Lemma ordinal_path_is_tree n : is_tree [set: ordinal_path n].
Proof. by split; [exact: ordinal_path_is_forest | exact: ordinal_path_connected]. Qed.

(** P_n is a B9 path tree: a tree of maximum degree at most two, for every n (P_0 included). *)
Lemma ordinal_path_path_tree n : path_tree (ordinal_path n).
Proof. by split; [exact: ordinal_path_is_tree | exact: ordinal_path_Delta]. Qed.

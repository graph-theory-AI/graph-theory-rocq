(** * Atlas.foundations.tree_decompositions -- X47/X48 <-> X212 vocabulary bridge

    Bridges the packing rows' encodings ([x47_edge_set], cut-form
    [x47_edge_connected], [x47_min_degree_at_least], list decompositions whose
    parts sharing an edge are equal) and the cycle row's encodings ([E(G)],
    edge-deletion [k_edge_connected] of GTBase.common, exact-count
    [x212_decomposition_into_copies]). *)

From GTBase Require Import base common.
From Packing.conjectures Require Import X47.
From Cycle.conjectures Require Import X212.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The X47 edge comprehension is the library's [E(G)]. *)
Lemma x47_edge_setE (G : sgraph) : x47_edge_set G = E(G).
Proof. by rewrite sg_edge_setE. Qed.

(** A walk leaving [S] uses an edge with one end in [S] and one outside. *)
Lemma connect_crossing (V : finType) (r : rel V) (S : {set V}) (x y : V) :
  connect r x y -> x \in S -> y \notin S ->
  exists u v, [/\ r u v, u \in S & v \notin S].
Proof.
case/connectP => p pth ->; elim: p x pth => [|z p IH] x /= pth xS; first by rewrite xS.
case/andP: pth => xz pth.
case: (boolP (z \in S)) => zS; last by exists x, z.
exact: IH pth zS.
Qed.

(** A [k]-edge-connected graph (GTBase.common, edge-deletion form) has at least
    [k] edges across every nonempty proper vertex set (X47's cut form). *)
Lemma k_edge_connected_cut (G : sgraph) (k : nat) (S : {set G}) :
  k_edge_connected G k -> S != set0 -> S != [set: G] ->
  k <= #|x47_crossing_edges S|.
Proof.
case=> _ H S0 ST; rewrite leqNgt; apply/negP => lt.
have C := connectedTE (H _ lt).
have [x xS] := set0Pn _ S0.
have [y yS] : exists y, y \notin S.
  by apply/existsP; move: ST; apply: contraNT; rewrite negb_exists => /forallP h;
     apply/eqP/setP => z; rewrite inE; move: (h z); rewrite negbK.
have [u [v [uv uS vS]]] := connect_crossing (C x y) xS yS.
move: uv; rewrite /edge_rel /= /del_es_rel /= => /andP [uv]; apply/negP; rewrite negbK.
rewrite inE x47_edge_setE in_edges uv /=; apply/andP; split; apply/set0Pn.
  by exists u; rewrite !inE eqxx uS.
by exists v; rewrite !inE eqxx orbT vS.
Qed.

(** ... and minimum degree at least [k]. *)
Lemma k_edge_connected_deg (G : sgraph) (k : nat) (v : G) :
  k_edge_connected G k -> k <= #|N(v)|.
Proof.
move=> kc; have [G1 _] := kc.
have [w vw] : exists w, w != v.
  have [a [b [_ _ ab]]] := card_gt1P G1.
  by case: (eqVneq a v) => [e|av]; [subst a; exists b; rewrite eq_sym | exists a].
apply: leq_trans (k_edge_connected_cut (S := [set v]) kc _ _) _.
- by apply/set0Pn; exists v; rewrite inE.
- by apply/eqP => /setP /(_ w); rewrite !inE (negbTE vw).
apply: leq_trans (leq_imset_card (fun u => [set v; u]) N(v)); apply: subset_leq_card.
apply/subsetP => e; rewrite inE x47_edge_setE => /andP [/edgesP [a [b [-> ab]]] /andP [m1 m2]].
apply/imsetP.
have [c [cin cv]] : exists c, c \in [set a; b] /\ c != v.
  have [c cm] := set0Pn _ m2; move: cm; rewrite !inE => /andP [cin cv]; exists c; split => //.
  by rewrite !inE.
have [d dm] := set0Pn _ m1; move: dm; rewrite !inE => /andP [dab /eqP dv]; subst d.
move: cin; rewrite !inE => /orP [] /eqP ?; subst c; move: dab => /orP [] /eqP ?; subst v;
  rewrite ?eqxx // in cv.
- by exists a; rewrite ?inE ?(sg_sym b a) // setUC.
- by exists b; rewrite ?inE.
Qed.

(** An X47 decomposition (parts sharing an edge are equal, repetitions allowed)
    yields an X212 decomposition (exact-count form): drop the repetitions. *)
Lemma x47_decomposition_x212 (G T : sgraph) :
  x47_tree_decomposition_by_copies G T ->
  exists D : seq {set {set G}}, x212_decomposition_into_copies T D.
Proof.
case=> parts [Hcopy [Hsub [Hcov Hdis]]].
exists (undup parts); split.
- move=> A; rewrite mem_undup => Ap.
  have Asub := Hsub A Ap.
  have [f [finj eA]] := Hcopy A Ap.
  rewrite eA in Asub *.
  exists f; split => //.
  + move=> x y xy; have := subsetP Asub [set f x; f y].
    rewrite x47_edge_setE in_edges; apply; rewrite inE.
    by apply/existsP; exists x; apply/existsP; exists y; rewrite xy eqxx.
  + apply/setP => e; rewrite !inE; apply/existsP/existsP.
    * by case=> x /existsP [y] h; exists (x, y).
    * by case=> [[x y]] /= h; exists x; apply/existsP; exists y.
- move=> e; case: (boolP (e \in E(G))) => eE /=.
  + have eE' : e \in x47_edge_set G by rewrite x47_edge_setE.
    have [F [Fp eF]] := Hcov e eE'.
    rewrite (@eq_in_count _ _ (pred1 F)) ?count_uniq_mem ?undup_uniq ?mem_undup ?Fp //.
    move=> A; rewrite mem_undup => Ap /=.
    apply/idP/eqP => [eA|->//]; exact: Hdis Ap Fp eA eF.
  + apply/eqP; rewrite -leqn0 leqNgt -has_count; apply/negP => /hasP [A].
    rewrite mem_undup => Ap eA.
    by move: eE; rewrite -x47_edge_setE (subsetP (Hsub A Ap) e eA).
Qed.

(** A tree on at least two vertices has an edge. *)
Lemma tree_has_edge (T : sgraph) : 1 < #|T| -> is_tree [set: T] -> 0 < #|x47_edge_set T|.
Proof.
move=> T1 [_ con].
have [a [b [_ _ ab]]] := card_gt1P T1.
have [u [v uv]] : exists u v : T, u -- v.
  have := connectedTE con a b; case/connectP => p pth la.
  case: p pth la => [|z p] /= ; first by move=> _ e; rewrite e eqxx in ab.
  by case/andP => az _ _; exists a, z.
by apply/card_gt0P; exists [set u; v]; rewrite x47_edge_setE in_edges.
Qed.

(** The one-vertex tree: only edgeless graphs have [0 %| #|E(G)|]. *)
Lemma trivial_tree_decomposition (G T : sgraph) :
  #|E(G)| = 0 -> exists D : seq {set {set G}}, x212_decomposition_into_copies T D.
Proof.
move=> /eqP; rewrite cards_eq0 => /eqP E0; exists [::]; split => // e.
by rewrite E0 inE.
Qed.

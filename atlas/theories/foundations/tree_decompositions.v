(** * Atlas.foundations.tree_decompositions -- X47/X48 <-> X212 vocabulary bridge

    Bridges the packing rows' encodings ([x47_edge_set], cut-form
    [x47_edge_connected], [x47_min_degree_at_least], list decompositions whose
    parts sharing an edge are equal) and the cycle row's encodings ([E(G)],
    edge-deletion [k_edge_connected] of GTBase.common, exact-count
    [x212_decomposition_into_copies]).
    Since the edge-copy library migration this module imports no conjecture file:
    the seven declarations keep their names and are stated over the public owners
    [E(G)], [GTBase.simple_cuts.cut_edges] and [GTBase.edge_copies]'s
    [edge_decomposition_by_equal_parts] / [edge_decomposition_exact], of which the
    X47 and X212 names are aliases; their types differ from the former ones only by
    conversion. *)

From GTBase Require Import base common.
From GTBase Require simple_cuts edge_copies.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The X47 edge comprehension is the library's [E(G)]. *)
Lemma x47_edge_setE (G : sgraph) : sg_edge_set G = E(G).
Proof. by []. Qed.
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
  k <= #|GTBase.simple_cuts.cut_edges S|.
Proof.
move=> kc S0 ST.
exact: (@GTBase.simple_cuts.k_edge_connected_cut G k kc S S0 ST).
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
apply/subsetP => e; rewrite GTBase.simple_cuts.cut_edgesE => /andP [/edgesP [a [b [-> ab]]] /andP [m1 m2]].
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
  GTBase.edge_copies.edge_decomposition_by_equal_parts G T ->
  exists D : seq {set {set G}}, GTBase.edge_copies.edge_decomposition_exact T D.
Proof. exact: GTBase.edge_copies.edge_decomposition_equal_parts_exact. Qed.

(** A tree on at least two vertices has an edge. *)
Lemma tree_has_edge (T : sgraph) : 1 < #|T| -> is_tree [set: T] -> 0 < #|E(T)|.
Proof. exact: GTBase.edge_copies.tree_has_edge. Qed.

(** The one-vertex tree: only edgeless graphs have [0 %| #|E(G)|]. *)
Lemma trivial_tree_decomposition (G T : sgraph) :
  #|E(G)| = 0 -> exists D : seq {set {set G}}, GTBase.edge_copies.edge_decomposition_exact T D.
Proof.
move=> /eqP; rewrite cards_eq0 => /eqP E0; exists [::].
exact: GTBase.edge_copies.edge_decomposition_exact_nil E0.
Qed.

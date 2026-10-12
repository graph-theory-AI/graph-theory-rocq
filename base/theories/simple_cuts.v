(** * GTBase.simple_cuts -- cuts of finite simple graphs

    [cut_edges S] contains the edges meeting both [S] and its complement.
    The empty and full sides have empty cuts; no side or graph nonemptiness
    is imposed. Its cardinality is the existing [common.cut_size S].

    [cut_connected G k] bounds every nonempty proper cut below by [k].
    This is vacuous on graphs of order at most one, unlike the deletion
    definition [common.k_edge_connected], which requires at least two
    vertices. No unconditional identification of those predicates is made. *)

From GTBase Require Import base common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition cut_edges (G : sgraph) (S : {set G}) : {set {set G}} :=
  [set e in E(G) | (e :&: S != set0) && (e :&: (~: S) != set0)].

Definition cut_connected (G : sgraph) (k : nat) : Prop :=
  forall S : {set G}, S != set0 -> S != [set: G] -> k <= #|cut_edges S|.

Lemma cut_edgesE (G : sgraph) (S : {set G}) (e : {set G}) :
  (e \in cut_edges S) =
  ((e \in E(G)) && ((e :&: S != set0) && (e :&: (~: S) != set0))).
Proof. by rewrite /cut_edges inE. Qed.

Lemma cut_edges_sub (G : sgraph) (S : {set G}) : cut_edges S \subset E(G).
Proof. by apply/subsetP => e; rewrite cut_edgesE => /andP []. Qed.

Lemma cut_edges0 (G : sgraph) : cut_edges (set0 : {set G}) = set0.
Proof. by apply/setP => e; rewrite cut_edgesE inE setI0 eqxx /= andbF. Qed.

Lemma cut_edgesC (G : sgraph) (S : {set G}) : cut_edges (~: S) = cut_edges S.
Proof.
by apply/setP => e; rewrite !cut_edgesE setCK (andbC (e :&: ~: S != set0)).
Qed.

Lemma cut_edgesT (G : sgraph) : cut_edges [set: G] = set0.
Proof. by rewrite -setC0 cut_edgesC cut_edges0. Qed.

Lemma card_cut_edges (G : sgraph) (S : {set G}) : #|cut_edges S| = cut_size S.
Proof.
rewrite /cut_edges /cut_size; apply: eq_card => e; rewrite !inE !setI_eq0.
by rewrite [[disjoint e & ~: S]]disjoints_subset setCK.
Qed.

(** On a simple edge, meeting both sides is exactly meeting [S] once.
    The graph-edge restriction is essential for this equality. *)
Lemma cut_edges_count1 (G : sgraph) (S : {set G}) :
  cut_edges S = [set e in E(G) | #|e :&: S| == 1].
Proof.
apply/setP => e; rewrite cut_edgesE inE.
case: (boolP (e \in E(G))) => eE //=.
have e2 : #|e| = 2.
  by move/edgesP: eE => [x [y [-> xy]]]; rewrite cards2 (sg_edgeNeq xy).
have parts : #|e :&: S| + #|e :&: ~: S| = 2.
  by rewrite -setDE cardsID e2.
rewrite -!cards_eq0.
move: parts; case: #|e :&: S| => [|[|a]]; case: #|e :&: ~: S| => [|b] //=.
by rewrite addnS !addSn.
Qed.

Lemma cut_connected0 (G : sgraph) : cut_connected G 0.
Proof. by move=> S _ _; exact: leq0n. Qed.

Lemma cut_connected_leq (G : sgraph) (k k' : nat) :
  k <= k' -> cut_connected G k' -> cut_connected G k.
Proof. by move=> kk' H S S0 ST; exact: leq_trans kk' (H S S0 ST). Qed.

Lemma cut_connected_small (G : sgraph) (k : nat) :
  #|G| <= 1 -> cut_connected G k.
Proof.
move=> G1 S S0 ST; have [x xS] := set0Pn _ S0.
have full : S = [set: G].
  apply/setP => y; rewrite inE.
  have yx : y = x by move/card_le1_eqP: G1; apply.
  by rewrite yx xS.
by rewrite full eqxx in ST.
Qed.

(** A walk leaving a vertex set crosses its boundary. *)
Lemma connect_crossing (V : finType) (r : rel V) (S : {set V}) (x y : V) :
  connect r x y -> x \in S -> y \notin S ->
  exists u v, [/\ r u v, u \in S & v \notin S].
Proof.
case/connectP => p pth ->; elim: p x pth => [|z p IH] x /= pth xS; first by rewrite xS.
case/andP: pth => xz pth.
case: (boolP (z \in S)) => zS; last by exists x, z.
exact: IH pth zS.
Qed.

(** The deletion definition implies the cut bound, with all its original guards. *)
Lemma k_edge_connected_cut (G : sgraph) (k : nat) :
  k_edge_connected G k -> cut_connected G k.
Proof.
case=> _ H S S0 ST; rewrite leqNgt; apply/negP => lt.
have C := connectedTE (H _ lt).
have [x xS] := set0Pn _ S0.
have [y yS] : exists y, y \notin S.
  by apply/existsP; move: ST; apply: contraNT; rewrite negb_exists => /forallP h;
     apply/eqP/setP => z; rewrite inE; move: (h z); rewrite negbK.
have [u [v [uv uS vS]]] := connect_crossing (C x y) xS yS.
move: uv; rewrite /edge_rel /= /del_es_rel /= => /andP [uv]; apply/negP; rewrite negbK.
rewrite cut_edgesE in_edges uv /=; apply/andP; split; apply/set0Pn.
  by exists u; rewrite !inE eqxx uS.
by exists v; rewrite !inE eqxx orbT vS.
Qed.

(** * Packing.conjectures.grounding_X214 — grounding lemmas for wave X214.

    Qed-closed, axiom-free sanity results for the single X214 node
    [spanning_k_connected_bipartite_subgraph_statement] (Thomassen's spanning
    k-connected bipartite subgraph conjecture, corpus row [bm:bm-025]).  These
    validate the STATEMENT, they do not attack the conjecture.

    X214 introduces no new vocabulary: it is built entirely from [k_connected]
    and [bipartite] (GTBase.base) and [del_edge_set] (GTBase.common), each of
    which already carries its own sanity lemmas in base.  What is grounded here
    is therefore the way the statement combines them:

      NON-VACUITY   [k_connected_K3_2]: K_3 really is 2-connected, so the
                    hypothesis of the k = 1 instance is satisfiable;
                    [x214_conclusion_attainable] exhibits, for that instance, an
                    explicit F (one deleted edge) whose deletion leaves a
                    bipartite 1-connected spanning subgraph of the NON-bipartite
                    K_3 — the conclusion is attainable.
      TEETH         [not_k_connected_K1_2]: the hypothesis excludes graphs
                    (K_1 is not 2-connected); [not_bipartite_K3]: a 2k-connected
                    graph need NOT itself be bipartite, so edges must really be
                    deleted; [bipartite_del_edge_setT] + [not_k_connected_del_all_K3]:
                    the bipartite half alone is free (delete every edge) but that
                    free witness fails the connectivity half, so the two
                    requirements of the conclusion genuinely interact.
      SETTLED CASE  [spanning_bipartite_of_bipartite]: the conjecture holds, from
                    its own definitions, for every already-bipartite 2k-connected
                    graph (take F = set0).  The source's recorded partial results
                    (Delcourt–Ferber 2015, Yuster 2024: connectivity
                    O(k^2 log n) suffices) are asymptotic in |V(G)| and are not
                    expressible against this finite statement, so they are not
                    grounded here. *)

From GTBase Require Import base.
From Packing.conjectures Require Import X214.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ============================================================================
    Generic helpers.
    ========================================================================== *)

(** Every vertex set of a complete graph is connected (any two distinct
    vertices are adjacent). *)
Lemma connected_complete (n : nat) (A : {set 'K_n}) : connected A.
Proof.
move=> x y xA yA; have [->|xy] := eqVneq x y; first exact: connect0.
by apply: connect1; rewrite /= xA yA /edge_rel /= xy.
Qed.

(** [k_connected] is antitone in [k]. *)
Lemma k_connected_leq (G : sgraph) (j k : nat) :
  j <= k -> k_connected G k -> k_connected G j.
Proof.
move=> jk [cG hG]; split; first exact: leq_ltn_trans jk cG.
by move=> S sS; apply: hG; apply: leq_trans sS jk.
Qed.

(** Deleting no edge preserves k-connectivity. *)
Lemma k_connected_del_edge_set0 (G : sgraph) (k : nat) :
  k_connected G k -> k_connected (del_edge_set G set0) k.
Proof.
case=> cG hG; split => // S sS.
by apply/connected_del_edge_set0; apply: hG.
Qed.

(** A graph without edges connects no two distinct vertices. *)
Lemma connect_edgeless (G : sgraph) (x y : G) :
  (forall u v : G, ~~ (u -- v)) -> connect (--) x y -> x = y.
Proof.
move=> noe /connectP [p]; case: p => [_ -> //|z p /= /andP[r _] _].
by move: r; rewrite (negbTE (noe x z)).
Qed.

(** ============================================================================
    Non-vacuity: the hypothesis is satisfiable, the conclusion attainable.
    ========================================================================== *)

(** K_3 is 2-connected: the k = 1 instance of the conjecture has a witness. *)
Lemma k_connected_K3_2 : k_connected 'K_3 2.
Proof. by split; [rewrite card_ord | move=> S _; exact: connected_complete]. Qed.

Lemma x214_hypothesis_satisfiable :
  exists (k : nat) (G : sgraph), 0 < k /\ k_connected G (2 * k).
Proof. by exists 1, 'K_3; split; [|rewrite muln1; exact: k_connected_K3_2]. Qed.

(** *** An explicit witness for the k = 1 instance.

    Deleting ONE edge of K_3 leaves the path 0 - 2 - 1, which is bipartite and
    1-connected: the conclusion of the conjecture is attainable on a graph that
    is itself NOT bipartite. *)

Notation v0 := (@ord0 2).
Notation v1 := (@Ordinal 3 1 isT).
Notation v2 := (@Ordinal 3 2 isT).

(** The single deleted edge {0,1}. *)
Definition x214_F3 : {set {set 'K_3}} := [set [set v0; v1]].
Notation H3 := (del_edge_set 'K_3 x214_F3).

Lemma x214_H3_edge (x y : H3) : (x -- y) = (x != y) && ([set x; y] != [set v0; v1]).
Proof. by rewrite /edge_rel /= /del_es_rel /= inE. Qed.

Lemma x214_I3_cases (x : 'I_3) : ((x == v0) || (x == v1)) || (x == v2).
Proof. by case: x => -[|[|[|n]]] H. Qed.

(** Every edge of H3 has exactly one end equal to the centre 2. *)
Lemma x214_K3_split (x y : 'I_3) :
  x != y -> [set x; y] != [set v0; v1] -> (x == v2) != (y == v2).
Proof.
move=> xy nF; have [x2|x2] := boolP (x == v2).
  have [y2|y2] := boolP (y == v2); last by [].
  by move: xy; rewrite (eqP x2) (eqP y2) eqxx.
have [y2|y2] := boolP (y == v2); first by [].
case/negP: nF; apply/eqP; move: xy.
have := x214_I3_cases x; rewrite (negbTE x2) orbF => /orP[/eqP->|/eqP->];
have := x214_I3_cases y; rewrite (negbTE y2) orbF => /orP[/eqP->|/eqP->].
- by rewrite eqxx.
- by move=> _.
- by move=> _; rewrite setUC.
- by rewrite eqxx.
Qed.

Lemma x214_bipartite_H3 : bipartite H3.
Proof.
by exists (fun i : H3 => i == v2) => x y;
   rewrite x214_H3_edge => /andP[]; exact: x214_K3_split.
Qed.

Lemma x214_e02 : (v0 : H3) -- v2.
Proof.
by rewrite x214_H3_edge; apply/andP; split => //;
   apply/eqP => /setP/(_ v2); rewrite !inE eqxx orbT.
Qed.

Lemma x214_e12 : (v1 : H3) -- v2.
Proof.
by rewrite x214_H3_edge; apply/andP; split => //;
   apply/eqP => /setP/(_ v2); rewrite !inE eqxx orbT.
Qed.

Lemma x214_k_connected_H3 : k_connected H3 1.
Proof.
apply/k_connected1; split; first by rewrite card_ord.
apply: connectedTI => x y.
have C : forall z : H3, connect (--) z v2.
  move=> z; have := x214_I3_cases z; case/orP => [/orP[]|] /eqP->;
    [exact: connect1 x214_e02|exact: connect1 x214_e12|exact: connect0].
by apply: connect_trans (C x) _; rewrite sconnect_sym; exact: C.
Qed.

(** The conclusion is attainable (non-vacuity of the conclusion). *)
Lemma x214_conclusion_attainable :
  exists F : {set {set 'K_3}},
    bipartite (del_edge_set 'K_3 F) /\ k_connected (del_edge_set 'K_3 F) 1.
Proof. by exists x214_F3; split; [exact: x214_bipartite_H3|exact: x214_k_connected_H3]. Qed.

(** ============================================================================
    Guard has teeth.
    ========================================================================== *)

(** The one-vertex graph is not 2-connected: the hypothesis excludes graphs. *)
Lemma not_k_connected_K1_2 : ~ k_connected 'K_1 2.
Proof. by case; rewrite card_ord. Qed.

(** A 2k-connected graph need not itself be bipartite: K_3 is 2-connected
    (above) but has no proper 2-colouring, so the conclusion's [F] cannot
    always be taken empty. *)
Lemma not_bipartite_K3 : ~ bipartite 'K_3.
Proof.
case=> f Hf.
have E i j : i != j :> 'I_3 -> f i != f j by move=> ij; apply: Hf; rewrite /edge_rel.
have n01 := E ord0 (Ordinal (isT : 1 < 3)) isT.
have n02 := E ord0 (Ordinal (isT : 2 < 3)) isT.
have n12 := E (Ordinal (isT : 1 < 3)) (Ordinal (isT : 2 < 3)) isT.
by case: (f ord0) n01 n02 n12; case: (f (Ordinal (isT : 1 < 3)));
   case: (f (Ordinal (isT : 2 < 3))).
Qed.

(** The bipartite half of the conclusion is free: deleting EVERY edge always
    leaves a bipartite spanning subgraph. *)
Lemma bipartite_del_edge_setT (G : sgraph) : bipartite (del_edge_set G E(G)).
Proof.
exists (fun _ => true) => x y /andP[xy].
by rewrite in_sg_edge_set; case/negP; apply/existsP; exists x; apply/existsP; exists y;
   rewrite xy eqxx.
Qed.

(** ... but that free witness is worthless: on K_3 it is not even 1-connected,
    so the two halves of the conclusion must be met simultaneously. *)
Lemma not_k_connected_del_all_K3 :
  ~ k_connected (del_edge_set 'K_3 E('K_3)) 1.
Proof.
move/k_connected1 => [_ /connectedTE cT].
have noe (u v : del_edge_set 'K_3 E('K_3)) : ~~ (u -- v).
  apply/negP => /andP[uv]; rewrite in_sg_edge_set; case/negP.
  by apply/existsP; exists u; apply/existsP; exists v; rewrite uv eqxx.
have := connect_edgeless noe (cT ord0 (Ordinal (isT : 1 < 3))).
by move/(congr1 (@nat_of_ord 3)).
Qed.

(** ============================================================================
    Settled case: already-bipartite graphs satisfy the conjecture.
    ========================================================================== *)

Lemma spanning_bipartite_of_bipartite (k : nat) (G : sgraph) :
  bipartite G -> k_connected G (2 * k) ->
  exists F : {set {set G}},
    bipartite (del_edge_set G F) /\ k_connected (del_edge_set G F) k.
Proof.
move=> [f Hf] kc; exists set0; split.
- by exists f => x y /andP[xy _]; apply: Hf.
- apply: k_connected_del_edge_set0; apply: k_connected_leq kc.
  by rewrite mul2n -addnn leq_addl.
Qed.

(** ============================================================================
    Axiom audit.
    ========================================================================== *)

Print Assumptions k_connected_K3_2.
Print Assumptions not_bipartite_K3.
Print Assumptions bipartite_del_edge_setT.
Print Assumptions not_k_connected_del_all_K3.
Print Assumptions x214_conclusion_attainable.
Print Assumptions spanning_bipartite_of_bipartite.

(** * GTBase.common — the shared conjecture vocabulary (WP4b)

    Notions that recur in the conjecture statements of several packages and are
    absent from coq-graph-theory 0.9.7.  EVERY definition here is built on the
    library vocabulary — [sgraph.v] ([E(G)], [subgraph], [induced], ['K_n],
    ['K_n,m], [connected], [diso]), [digraph.v] ([diGraph], [x -- y], [connect]),
    [connectivity.v] ([matching]) and MathComp's [path.v] ([cycleb]/[ucycleb],
    [sorted]) — so that a statement never has to re-encode them.

    Exported by [GTBase.base]; see the header of [base.v] for the full list of
    names a statement is expected to use.

    Cycle convention (n >= 3).  A Hamilton cycle is a [seq] of vertices [c] with
    [ucycleb (--) c] (consecutive adjacency, closing edge [last -> head], and all
    vertices distinct) and [size c = #|G|] — the encoding already used by
    hamiltonicity-theory/U2.  Two degenerate sizes must be kept in mind:
    - [size c = 1] is impossible ([ucycleb (--) [:: x]] is [x -- x], false in a
      simple graph), so [hamiltonian] is FALSE for [#|G| = 1]
      (see [not_hamiltonian_K1]);
    - [size c = 2] IS accepted: [ucycleb (--) [:: x; y]] unfolds to
      [x -- y && y -- x && uniq], which holds for any edge, i.e. the "digon"
      [x -> y -> x].  So [hamiltonian 'K_2] is TRUE (see [hamiltonian_K2]).
    A statement about genuine Hamilton cycles therefore carries a [2 < #|G|]
    (or [2 < size c]) guard, exactly as base's [girth_geq] does. *)

From mathcomp Require Export all_boot.
From GraphTheory Require Export digraph sgraph connectivity.
(* [preliminaries] is IMPORTED, not exported: [common.v] only needs its [restrict]
   notation and [bij]'s [card_bij] in proofs; downstream packages keep the vocabulary of [base.v]. *)
From GraphTheory Require Import preliminaries bij.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Edge sets

    There is deliberately NO [edge_set] here: the edge set of a SIMPLE graph is
    the library's [E(G)] ([sgraph.sg_edge_set]), and the name [edge_set] is
    already taken by [mgraph.edge_set] (the edges of a MULTIgraph inside a vertex
    set, used e.g. by chromatic-theory/U5) — defining it here would shadow that.
    The 31 local [*_edge_set] copies in [*/theories/conjectures] all use the
    boolean comprehension below; [sg_edge_setE] is the one rewrite that turns
    such a local copy into [E(G)]. *)

(** The boolean-comprehension presentation of [E(G)] used by the local copies. *)
Lemma sg_edge_setE (G : sgraph) :
  E(G) = [set e : {set G} | [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].
Proof.
apply/setP => e; rewrite inE; apply/idP/existsP.
- by case/edgesP => x [y] [-> xy]; exists x; apply/existsP; exists y; rewrite xy eqxx.
- by case=> x /existsP[y] /andP[xy /eqP ->]; rewrite in_edges.
Qed.

(** Membership in [E(G)], in the form the local copies reason with. *)
Lemma in_sg_edge_set (G : sgraph) (e : {set G}) :
  (e \in E(G)) = [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]].
Proof. by rewrite sg_edge_setE inE. Qed.

(** Two edge sets are edge-disjoint when they share no edge. *)
Definition edge_disjoint (G : sgraph) (A B : {set {set G}}) : bool := [disjoint A & B].

(** ** Matchings *)

(** A PERFECT matching: a [connectivity.matching] covering every vertex. *)
Definition perfect_matching (G : sgraph) (M : {set {set G}}) : Prop :=
  matching M /\ cover M = [set: G].

(** ** Hamiltonicity *)

(** A Hamilton cycle: a closed simple spanning walk, as a [seq] of vertices. *)
Definition hamiltonian_cycle (G : sgraph) (c : seq G) : bool :=
  ucycleb (--) c && (size c == #|G|).
Arguments hamiltonian_cycle : clear implicits.

(** [G] is Hamiltonian iff it has a Hamilton cycle. *)
Definition hamiltonian (G : sgraph) : Prop :=
  exists c : seq G, hamiltonian_cycle G c.

(** A Hamilton path: a simple spanning (open) walk, as a [seq] of vertices. *)
Definition hamiltonian_path (G : sgraph) (s : seq G) : bool :=
  [&& sorted (--) s, uniq s & size s == #|G|].
Arguments hamiltonian_path : clear implicits.

(** [G] is traceable iff it has a Hamilton path. *)
Definition traceable (G : sgraph) : Prop :=
  exists s : seq G, hamiltonian_path G s.

(** ** Edge deletion and edge connectivity *)

Section DelEdgeSet.
Variables (G : sgraph) (F : {set {set G}}).

Definition del_es_rel : rel G := [rel x y : G | (x -- y) && ([set x; y] \notin F)].

Lemma del_es_sym : symmetric del_es_rel.
Proof. by move=> x y; rewrite /del_es_rel /= sg_sym setUC. Qed.

Lemma del_es_irrefl : irreflexive del_es_rel.
Proof. by move=> x; rewrite /del_es_rel /= sg_irrefl. Qed.

(** [del_edge_set G F]: [G] with the edges of [F] removed (vertices unchanged). *)
Definition del_edge_set : sgraph := SGraph del_es_sym del_es_irrefl.
End DelEdgeSet.
Arguments del_edge_set : clear implicits.

(** k-edge-connectivity: at least two vertices, and deleting fewer than [k]
    edges always leaves the graph connected (the edge analogue of base's
    Whitney-form [k_connected]). *)
Definition k_edge_connected (G : sgraph) (k : nat) : Prop :=
  (1 < #|G|) /\
  forall F : {set {set G}}, #|F| < k -> connected [set: del_edge_set G F].

(** ** Subgraph containment *)

(** [G] contains [H] as a (not necessarily induced) subgraph. *)
Definition has_subgraph (G H : sgraph) : Prop := subgraph H G.

(** [G] has no INDUCED subgraph isomorphic to [H] ("[H]-free"). *)
Definition induced_free (G H : sgraph) : Prop :=
  forall S : {set G}, diso (induced S) H -> False.

(** ** Complete bipartite graphs *)

(** [G] is complete bipartite with parts [A] and [~: A]: two vertices are
    adjacent exactly when they lie on opposite sides.  (Taking [x = y] the
    right-hand side is [false], so irreflexivity is automatic, and [K_n,m] is
    the instance [A = the left part] — see [complete_bipartite_KB].) *)
Definition complete_bipartite (G : sgraph) (A : {set G}) : Prop :=
  forall x y : G, (x -- y) = (x \in A) (+) (y \in A).

(** ** Directed vocabulary (digraph.v) *)

(** An ORIENTED digraph: no pair of opposite arcs (hence no loops either). *)
Definition oriented (D : diGraph) : Prop :=
  forall x y : D, x -- y -> ~~ (y -- x).

(** A TOURNAMENT: loopless, and exactly one arc between any two distinct
    vertices (the [Prop] form of coq-digraph's [DiGraph_IsTournament]). *)
Definition tournament (D : diGraph) : Prop :=
  irreflexive (@edge_rel D) /\ forall x y : D, (x != y) = (x -- y) (+) (y -- x).

(** ACYCLIC: no directed cycle, i.e. no arc lies on a directed closed walk. *)
Definition acyclic (D : diGraph) : Prop :=
  forall x y : D, x -- y -> ~~ connect (--) y x.

(** ** Sanity lemmas ******************************************************

    Non-vacuity (each notion has a witness) and guard-has-teeth (the obvious
    degenerate candidate is rejected) for every notion introduced above. *)

(** *** edge sets *)

(** [K_3] has exactly three edges (non-vacuity). *)
Lemma card_sg_edge_set_K3 : #|E('K_3)| = 3.
Proof. by rewrite card_edge_Kn. Qed.

(** [K_1] has no edge. *)
Lemma sg_edge_set_K1 : E('K_1) = set0.
Proof. by apply/eqP; rewrite -cards_eq0 card_edge_Kn. Qed.

(** Guard has teeth, in the local copies' comprehension form: no 2-set of
    vertices of [K_1] is an edge. *)
Lemma no_sg_edge_K1 (e : {set 'K_1}) :
  ~~ [exists x : ('K_1), [exists y : ('K_1), (x -- y) && (e == [set x; y])]].
Proof. by rewrite -in_sg_edge_set sg_edge_set_K1 inE. Qed.

(** *** perfect_matching *)

(** The single edge of [K_2] is a perfect matching (non-vacuity). *)
Lemma perfect_matching_K2 : perfect_matching (G := 'K_2) [set [set: 'K_2]].
Proof.
have eT : [set: 'K_2] = [set (@Ordinal 2 0 isT : 'K_2);
                             (@Ordinal 2 1 isT : 'K_2)].
  by apply/setP => z; rewrite !inE; case: z => -[|[|z]] zP //=; apply/eqP/val_inj.
split; last by rewrite /cover big_set1.
split=> [e|e1 e2]; rewrite !inE.
- by move/eqP->; rewrite eT in_edges.
- by move=> /eqP-> /eqP->.
Qed.

(** An empty matching never covers a nonempty graph (guard has teeth). *)
Lemma not_perfect_matching0 (G : sgraph) : 0 < #|G| -> ~ perfect_matching (G := G) set0.
Proof.
move=> /card_gt0P[x _] [_]; rewrite /cover big_set0 => /setP/(_ x).
by rewrite !inE.
Qed.

(** *** hamiltonian / traceable *)

(** [K_3] is Hamiltonian (non-vacuity). *)
Lemma hamiltonian_K3 : hamiltonian 'K_3.
Proof.
exists [:: (@Ordinal 3 0 isT : 'K_3);
           (@Ordinal 3 1 isT : 'K_3);
           (@Ordinal 3 2 isT : 'K_3)].
by rewrite /hamiltonian_cycle /ucycleb /= card_ord.
Qed.

(** [K_1] is NOT Hamiltonian: the only spanning seq is a loop (guard has teeth,
    and it pins down the n >= 3 convention). *)
Lemma not_hamiltonian_K1 : ~ hamiltonian 'K_1.
Proof.
case=> -[|x [|y c]]; rewrite /hamiltonian_cycle /= card_ord //=.
- by rewrite /ucycleb /= sg_irrefl.
- by rewrite andbF.
Qed.

(** A one-vertex seq is a Hamilton PATH of [K_1] (non-vacuity; note the
    contrast with [not_hamiltonian_K1]). *)
Lemma traceable_K1 : traceable 'K_1.
Proof.
by exists [:: (@Ordinal 1 0 isT : 'K_1)]; rewrite /hamiltonian_path /= card_ord.
Qed.

(** A Hamilton cycle is spanning (structural law, shared with [hamiltonian_path]). *)
Lemma hamiltonian_cycle_size (G : sgraph) (c : seq G) :
  hamiltonian_cycle G c -> size c = #|G|.
Proof. by case/andP => _ /eqP. Qed.

(** The n >= 3 caveat, made explicit: the two-vertex "digon" passes
    [hamiltonian_cycle], so Hamiltonicity statements must guard with [2 < #|G|]. *)
Lemma hamiltonian_K2 : hamiltonian 'K_2.
Proof.
exists [:: (@Ordinal 2 0 isT : 'K_2); (@Ordinal 2 1 isT : 'K_2)].
by rewrite /hamiltonian_cycle /ucycleb /= card_ord.
Qed.

(** *** edge_disjoint *)

(** Edge-disjointness is symmetric, and an edge set is edge-disjoint from [set0]. *)
Lemma edge_disjointC (G : sgraph) (A B : {set {set G}}) :
  edge_disjoint A B = edge_disjoint B A.
Proof. exact: disjoint_sym. Qed.

Lemma edge_disjoint0 (G : sgraph) (A : {set {set G}}) : edge_disjoint A set0.
Proof. by rewrite /edge_disjoint disjoints_subset subsetC sub0set. Qed.

(** Guard has teeth: a nonempty edge set is not edge-disjoint from itself. *)
Lemma not_edge_disjoint_self (G : sgraph) (A : {set {set G}}) :
  A != set0 -> ~~ edge_disjoint A A.
Proof. by case/set0Pn => e eA; apply/pred0Pn; exists e; rewrite /= eA. Qed.

(** *** del_edge_set / k_edge_connected *)

(** Deleting no edge changes nothing. *)
Lemma del_edge_set0 (G : sgraph) : @edge_rel (del_edge_set G set0) =2 @edge_rel G.
Proof. by move=> x y; rewrite /edge_rel /= /del_es_rel /= inE andbT. Qed.

(** Consistency: 1-edge-connected = at least two vertices and connected. *)
Lemma connected_del_edge_set0 (G : sgraph) (A : {set G}) :
  @connected (del_edge_set G set0) A <-> @connected G A.
Proof.
have E : restrict A (@edge_rel (del_edge_set G set0)) =2 restrict A (@edge_rel G).
  by move=> x y; rewrite /restrict_mem /= del_edge_set0.
by split => H x y xA yA; move: (H x y xA yA); rewrite (eq_connect E).
Qed.

Lemma k_edge_connected1 (G : sgraph) :
  k_edge_connected G 1 <-> (1 < #|G|) /\ connected [set: G].
Proof.
split=> -[cG hG]; split => //.
- by apply/connected_del_edge_set0; apply: hG; rewrite cards0.
- by move=> F; rewrite ltnS leqn0 cards_eq0 => /eqP ->; apply/connected_del_edge_set0.
Qed.

(** [K_2] is connected (helper for the [k_edge_connected] witness). *)
Lemma connected_K2 : connected [set: 'K_2].
Proof.
apply: connectedTI => x y; have [->|xy] := eqVneq x y; first exact: connect0.
by apply: connect1; rewrite /edge_rel.
Qed.

(** [K_2] is 1-edge-connected (non-vacuity). *)
Lemma k_edge_connected_K2 : k_edge_connected 'K_2 1.
Proof. by apply/k_edge_connected1; split; [rewrite card_ord|exact: connected_K2]. Qed.

(** A one-vertex graph is not 1-edge-connected (guard has teeth). *)
Lemma not_k_edge_connected_K1 : ~ k_edge_connected 'K_1 1.
Proof. by case; rewrite card_ord. Qed.

(** *** subgraph containment *)

(** Every graph contains itself (non-vacuity). *)
Lemma has_subgraph_refl (G : sgraph) : has_subgraph G G.
Proof. by exists id. Qed.

(** [K_n] contains every graph on at most [n] vertices. *)
Lemma has_subgraph_Kn n (G : sgraph) : #|G| <= n -> has_subgraph 'K_n G.
Proof. exact: sub_Kn. Qed.

(** A graph has no induced copy of a strictly bigger graph (guard has teeth). *)
Lemma induced_free_card (G H : sgraph) : #|G| < #|H| -> induced_free G H.
Proof.
move=> ltGH S h; have := card_bij (diso_v h).
rewrite card_sig => eqS; move: ltGH; rewrite -eqS.
by rewrite ltnNge => /negP; apply; rewrite -cardsT subset_leq_card ?subsetT.
Qed.

(** *** complete_bipartite *)

(** ['K_n,m] is complete bipartite with the left part as one side (non-vacuity). *)
Lemma complete_bipartite_KB n m :
  complete_bipartite (G := 'K_n,m) [set x : 'K_n,m | is_inl x].
Proof. by move=> x y; rewrite /edge_rel /= !inE. Qed.

(** Guard has teeth: ['K_3] is not complete bipartite for any part (an odd
    cycle has no bipartition), witnessed here for its three vertices. *)
Lemma not_complete_bipartite_K3 (A : {set 'K_3}) : ~ complete_bipartite A.
Proof.
move=> cb; have E := fun x y : 'K_3 => cb x y.
pose v0 := (@Ordinal 3 0 isT : 'K_3).
pose v1 := (@Ordinal 3 1 isT : 'K_3).
pose v2 := (@Ordinal 3 2 isT : 'K_3).
have e01 := E v0 v1; have e12 := E v1 v2; have e02 := E v0 v2.
have a01 : v0 -- v1 by rewrite /edge_rel.
have a12 : v1 -- v2 by rewrite /edge_rel.
have a02 : v0 -- v2 by rewrite /edge_rel.
rewrite a01 in e01; rewrite a12 in e12; rewrite a02 in e02.
by move: e01 e12 e02; case: (v0 \in A); case: (v1 \in A); case: (v2 \in A).
Qed.

(** *** tournament / oriented / acyclic *)

Section C3_di.
(** The cyclically oriented triangle [0 -> 1 -> 2 -> 0]. *)
Definition c3_di_rel : rel 'I_3 := fun i j => ((val i).+1 %% 3 == val j)%N.
(* NB: not [C3] — [sgraph.C3] is the UNDIRECTED triangle ['K_3]. *)
Definition C3_di : diGraph := DiGraph c3_di_rel.
End C3_di.

(** The oriented triangle is a tournament (non-vacuity). *)
Lemma tournament_C3_di : tournament C3_di.
Proof.
split=> [x|x y]; first by case: x => -[|[|[|x]]] xP.
by case: x => -[|[|[|x]]] xP //; case: y => -[|[|[|y]]] yP.
Qed.

(** Every tournament is oriented (consistency). *)
Lemma tournament_oriented (D : diGraph) : tournament D -> oriented D.
Proof.
case=> irrD totD x y xy; apply/negP => yx.
move: (totD x y); rewrite xy yx addbb => /negbFE/eqP eqxy.
by move: xy; rewrite eqxy irrD.
Qed.

(** The oriented triangle is oriented. *)
Lemma oriented_C3_di : oriented C3_di.
Proof. exact/tournament_oriented/tournament_C3_di. Qed.

(** ... but NOT acyclic (guard has teeth). *)
Lemma not_acyclic_C3_di : ~ acyclic C3_di.
Proof.
move=> ac; have := ac (@Ordinal 3 0 isT) (@Ordinal 3 1 isT) isT.
apply/negP; rewrite negbK; apply/connectP.
by exists [:: (@Ordinal 3 2 isT : C3_di); (@Ordinal 3 0 isT : C3_di)].
Qed.

(** The edgeless digraph on one vertex is acyclic (non-vacuity). *)
Lemma acyclic_triv : acyclic (DiGraph [rel _ _ : 'I_1 | false]).
Proof. by move=> x y. Qed.

(** Acyclic digraphs have no loops (structural law). *)
Lemma acyclic_irrefl (D : diGraph) : acyclic D -> irreflexive (@edge_rel D).
Proof. by move=> ac x; apply/negP => xx; move: (ac x x xx); rewrite connect0. Qed.

(** ** Axiom audit ********************************************************

    Every lemma above was checked with [Print Assumptions] and reported
    "Closed under the global context": [sg_edge_setE], [in_sg_edge_set],
    [card_sg_edge_set_K3], [sg_edge_set_K1], [no_sg_edge_K1], [perfect_matching_K2],
    [not_perfect_matching0], [hamiltonian_K3], [not_hamiltonian_K1],
    [traceable_K1], [hamiltonian_cycle_size], [hamiltonian_K2], [edge_disjointC], [edge_disjoint0],
    [not_edge_disjoint_self], [del_edge_set0], [connected_del_edge_set0],
    [k_edge_connected1], [connected_K2], [k_edge_connected_K2],
    [not_k_edge_connected_K1], [has_subgraph_refl], [has_subgraph_Kn],
    [induced_free_card], [complete_bipartite_KB], [not_complete_bipartite_K3],
    [tournament_C3_di], [tournament_oriented], [oriented_C3_di], [not_acyclic_C3_di],
    [acyclic_triv], [acyclic_irrefl]. *)

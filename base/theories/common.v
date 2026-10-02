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
(* [coloring] is IMPORTED only to state [chi_diso]; [base.v] exports it. *)
From GraphTheory Require Import coloring.

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

(** The two-element-clique presentation of [E(G)] used by two local copies
    (X100, X102): an edge is exactly a two-element clique. *)
Lemma sg_edge_set_cliqueE (G : sgraph) :
  E(G) = [set e : {set G} | (#|e| == 2) && cliqueb e].
Proof.
apply/setP=> e; rewrite in_sg_edge_set inE.
apply/existsP/andP.
- move=> [x]; move/existsP=> [y]; move/andP=> [xy /eqP ->].
  split; first by rewrite cards2 (sg_edgeNeq xy).
  apply/cliqueP=> u v /set2P[]-> /set2P[]-> //;
    rewrite ?eqxx // => _; by rewrite sgP.
- move=> [/cards2P [x [y [xDy ->]]] /cliqueP clique_xy].
  exists x; apply/existsP; exists y; apply/andP; split.
  + have x_in : x \in [set x; y] by rewrite !inE eqxx.
    have y_in : y \in [set x; y] by rewrite !inE eqxx orbT.
    exact: clique_xy x_in y_in xDy.
  + by rewrite eqxx.
Qed.

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

(** [del_edge_set G F]: [G] with the edges of [F] removed (vertices unchanged).

    Contract: the vertex type is that of [G], and [x -- y] holds exactly when
    [x -- y] holds in [G] and the pair [[set x; y]] is not in [F]
    ([del_edge_setE]).  [F] is an arbitrary family of vertex sets.  Members
    that are not edges of [G] (non-adjacent pairs, singletons, sets of three or
    more vertices) have no effect ([del_edge_set_nonedges]), and the edge set
    of the result is exactly [E(G) :\: F] ([edges_del_edge_set]).  Corner
    cases: [F = set0] deletes nothing ([del_edge_set0]), [F = E(G)] deletes
    every edge ([del_edge_setT]), and [F = [set e]] deletes the single pair [e]
    ([del_edge_set1]).  A simple graph on the same vertex type whose adjacency
    agrees pointwise with [del_es_rel F] is isomorphic to [del_edge_set G F]
    through the identity ([del_edge_set_eq_diso]); properties then transfer
    along that isomorphism, the chromatic number by [chi_diso]. *)
Definition del_edge_set : sgraph := SGraph del_es_sym del_es_irrefl.
End DelEdgeSet.
Arguments del_edge_set : clear implicits.

(** Adjacency in [del_edge_set G F], in the form the local copies used. *)
Lemma del_edge_setE (G : sgraph) (F : {set {set G}}) (x y : G) :
  @edge_rel (del_edge_set G F) x y = (x -- y) && ([set x; y] \notin F).
Proof. by []. Qed.

(** Deleting the one-element family [[set e]] removes exactly the pair [e]. *)
Lemma del_edge_set1 (G : sgraph) (e : {set G}) (x y : G) :
  @edge_rel (del_edge_set G [set e]) x y = (x -- y) && ([set x; y] != e).
Proof. by rewrite del_edge_setE inE. Qed.

(** The edges of [del_edge_set G F] are exactly the edges of [G] outside [F]. *)
Lemma edges_del_edge_set (G : sgraph) (F : {set {set G}}) :
  E(del_edge_set G F) = E(G) :\: F.
Proof.
apply/setP=> e; rewrite inE; apply/edgesP/andP.
- case=> x [y] [-> /andP[xy xyF]]; split=> //.
  by rewrite in_edges.
- case=> eF /edgesP[x [y [exy xy]]]; exists x, y; split=> //.
  by rewrite del_edge_setE xy -exy eF.
Qed.

(** Members of [F] that are not edges of [G] have no effect. *)
Lemma del_edge_set_nonedges (G : sgraph) (F : {set {set G}}) :
  [disjoint F & E(G)] -> @edge_rel (del_edge_set G F) =2 @edge_rel G.
Proof.
move=> dis x y; rewrite del_edge_setE.
case xy: (@edge_rel G x y) => //=; apply/negP => xyF.
move: dis; rewrite disjoints_subset => /subsetP/(_ _ xyF).
by rewrite inE in_edges xy.
Qed.

(** Same-carrier transport: a simple graph on [G] with the adjacency of
    [del_edge_set G F] is isomorphic to it through the identity. *)
Lemma del_edge_set_eq_diso (G : sgraph) (F : {set {set G}}) (r : rel G)
    (r_sym : symmetric r) (r_irrefl : irreflexive r) :
  r =2 del_es_rel F -> diso (SGraph r_sym r_irrefl) (del_edge_set G F).
Proof. by move=> rE; apply: eq_diso. Qed.

(** The chromatic number is invariant under isomorphism (upstream states this
    as [coloring.diso_chi] but leaves it unproved). *)
Lemma chi_diso (F G : sgraph) : diso F G -> χ([set: F]) = χ([set: G]).
Proof.
move=> i; rewrite (chi_isubgraph (iso_isubgraph i)).
suff -> : [set iso_isubgraph i x | x in [set: F]] = [set: G] by [].
apply/setP=> y; rewrite inE; apply/imsetP; exists (i^-1 y) => //=.
by rewrite bijK'.
Qed.

(** k-edge-connectivity: at least two vertices, and deleting fewer than [k]
    edges always leaves the graph connected (the edge analogue of base's
    Whitney-form [k_connected]). *)
Definition k_edge_connected (G : sgraph) (k : nat) : Prop :=
  (1 < #|G|) /\
  forall F : {set {set G}}, #|F| < k -> connected [set: del_edge_set G F].

(** ** Subgraph containment *)

(** [G] contains [H] as a (not necessarily induced) subgraph. *)
Definition has_subgraph (G H : sgraph) : Prop := subgraph H G.

(** [G] has no INDUCED subgraph isomorphic to [H] ("[H]-free").

    Contract, host [G] first and pattern [H] second: no vertex set [S] of [G]
    induces a graph isomorphic to [H].  [S] ranges over ALL vertex sets, the
    empty set and [[set: G]] included, and isomorphism is the library's [diso]
    (written [≃]): a bijection that preserves and reflects adjacency.  [diso]
    lands in [Type], so the definition negates it directly; the
    [~ inhabited (induced S ≃ H)] form used by the local copies is
    [induced_free_inhabited], and only the isomorphism type of [H] matters
    ([induced_free_diso]).  Degenerate cases:
    - an empty pattern is induced by [S = set0], so NO graph, the empty one
      included, is free of it ([not_induced_free_pattern0]);
    - the empty host is free of exactly the nonempty patterns
      ([induced_free_host0]); in particular [K_1]-free means empty
      ([induced_free_K1]);
    - a pattern with more vertices than the host is always excluded
      ([induced_free_card]), and no graph is free of itself
      ([not_induced_free_self]). *)
Definition induced_free (G H : sgraph) : Prop :=
  forall S : {set G}, diso (induced S) H -> False.

(** The presentation used by the local copies, which negate [inhabited]. *)
Lemma induced_free_inhabited (G H : sgraph) :
  induced_free G H <-> forall S : {set G}, ~ inhabited (induced S ≃ H).
Proof.
by split=> free S; [case; exact: free S | move=> i; exact: free S (inhabits i)].
Qed.

(** Only the isomorphism type of the pattern matters. *)
Lemma induced_free_diso (G H H' : sgraph) :
  diso H H' -> induced_free G H -> induced_free G H'.
Proof. by move=> i free S j; apply: (free S); exact: diso_comp j (diso_sym i). Qed.

(** An isomorphism of hosts carries induced copies, with their size: an induced
    copy of [H] on [S] in [G] gives one on a vertex set of the same size in [G']. *)
Lemma induced_copy_host_diso (G G' H : sgraph) (i : diso G G') (S : {set G}) :
  diso (induced S) H -> exists S' : {set G'}, #|S'| = #|S| /\ inhabited (induced S' ≃ H).
Proof.
move=> j; pose k : H ⇀ G' :=
  isubgraph_comp (iso_isubgraph (diso_sym j)) (isubgraph_comp (induced_isubgraph S) (iso_isubgraph i)).
exists [set x in codom k]; split; last by split; exact: diso_sym (isubgraph_induced k).
have kinj : injective k by exact: isubgraph_inj.
have e1 : #|[set x in codom k]| = #|H| by rewrite cardsE card_codom.
have e2 : #|induced S| = #|S| by rewrite card_sig; apply: eq_card => x; rewrite !inE.
by rewrite e1 -e2 (card_bij (diso_v j)).
Qed.

(** Only the isomorphism type of the host matters either. *)
Lemma induced_free_host_diso (G G' H : sgraph) :
  diso G G' -> induced_free G H -> induced_free G' H.
Proof.
move=> i free S' j; pose k : H ⇀ G :=
  isubgraph_comp (iso_isubgraph (diso_sym j))
    (isubgraph_comp (induced_isubgraph S') (iso_isubgraph (diso_sym i))).
exact: free _ (diso_sym (isubgraph_induced k)).
Qed.

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

(** Deleting edges never changes the vertex type, hence the vertex count. *)
Lemma card_del_edge_set (G : sgraph) (F : {set {set G}}) :
  #|del_edge_set G F| = #|G|.
Proof. by []. Qed.

(** Deleting every edge leaves no edge (guard has teeth). *)
Lemma del_edge_setT (G : sgraph) (x y : G) :
  ~~ @edge_rel (del_edge_set G E(G)) x y.
Proof. by rewrite del_edge_setE in_edges; case: (x -- y). Qed.

(** Grounding on the triangle: deleting the pair [{0, 2}] removes exactly that
    edge, the edge [{0, 1}] survives. *)
Lemma del_edge_set_K3 :
  let T := del_edge_set 'K_3 [set [set ord0; ord_max]] in
  ~~ @edge_rel T ord0 ord_max /\ @edge_rel T ord0 (@Ordinal 3 1 isT).
Proof.
split; rewrite del_edge_set1 ?eqxx ?andbF //=.
by apply/eqP => /setP/(_ (@Ordinal 3 1 isT)); rewrite !inE.
Qed.

(** *** Single-edge deletion [del_edge_set G [set e]] *)

(** A real edge is removed. *)
Lemma del_edge_set1_edge (G : sgraph) (x y : G) :
  ~~ @edge_rel (del_edge_set G [set [set x; y]]) x y.
Proof. by rewrite del_edge_set1 eqxx andbF. Qed.

(** Every other pair keeps its adjacency. *)
Lemma del_edge_set1_other (G : sgraph) (e : {set G}) (x y : G) :
  [set x; y] != e -> @edge_rel (del_edge_set G [set e]) x y = x -- y.
Proof. by move=> xye; rewrite del_edge_set1 xye andbT. Qed.

(** Corner case: a pair [e] that is not a two-element set (empty, a singleton,
    or three or more vertices) deletes nothing. *)
Lemma del_edge_set1_invalid (G : sgraph) (e : {set G}) :
  #|e| != 2 -> @edge_rel (del_edge_set G [set e]) =2 @edge_rel G.
Proof.
move=> e2 x y; rewrite del_edge_set1.
case xy: (@edge_rel G x y) => //=; apply: contra e2 => /eqP <-.
by rewrite cards2 (sg_edgeNeq xy).
Qed.

(** Deleting the same pair twice is deleting it once. *)
Lemma del_edge_set1_twice (G : sgraph) (e : {set G}) :
  @edge_rel (del_edge_set (del_edge_set G [set e]) [set e]) =2
  @edge_rel (del_edge_set G [set e]).
Proof. by move=> x y; rewrite !del_edge_set1 -andbA andbb. Qed.

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

(** No graph is free of itself (guard has teeth). *)
Lemma not_induced_free_self (G : sgraph) : ~ induced_free G G.
Proof.
move=> free; have i : G ⇀ G := iso_isubgraph diso_id.
exact: free _ (diso_sym (isubgraph_induced i)).
Qed.

(** Degenerate case: the empty pattern is induced by [S = set0], so no graph,
    not even the empty one, is free of it. *)
Lemma not_induced_free_pattern0 (G H : sgraph) : #|H| = 0 -> ~ induced_free G H.
Proof.
move=> H0 free; apply: (free set0).
have e0 : #|induced (set0 : {set G})| = 0 by rewrite card_sig; apply: eq_card0 => x; rewrite !inE.
have i0 : diso (induced (set0 : {set G})) 'K_0.
  by rewrite -[X in 'K_X]e0; apply: diso_Kn => x; have := valP x; rewrite inE.
have iH : diso H 'K_0.
  by rewrite -[X in 'K_X]H0; apply: diso_Kn => x; move: (card0_eq H0 x); rewrite !inE.
exact: diso_comp i0 (diso_sym iH).
Qed.

(** Degenerate case: the empty host is free of exactly the nonempty patterns. *)
Lemma induced_free_host0 (G H : sgraph) :
  #|G| = 0 -> induced_free G H <-> 0 < #|H|.
Proof.
move=> G0; split=> [free|H0]; last by apply: induced_free_card; rewrite G0.
by rewrite lt0n; apply/negP => /eqP H0; exact: not_induced_free_pattern0 H0 free.
Qed.

(** Every clique on [n] vertices induces a copy of ['K_n] (negative family). *)
Lemma not_induced_free_clique (G : sgraph) (S : {set G}) :
  clique S -> ~ induced_free G 'K_#|S|.
Proof.
move=> cS free; apply: (free S).
have eS : #|induced S| = #|S| by rewrite card_sig; apply: eq_card => x; rewrite !inE.
rewrite -[X in 'K_X]eS; apply: diso_Kn => x y xy.
by apply: cS (valP x) (valP y) _; rewrite (inj_eq val_inj).
Qed.

(** [K_1]-free means empty. *)
Lemma induced_free_K1 (G : sgraph) : induced_free G 'K_1 <-> #|G| = 0.
Proof.
split=> [free|G0]; last by apply: induced_free_card; rewrite G0 card_ord.
apply/eqP; rewrite -leqn0 leqNgt; apply/negP => /card_gt0P[x _].
have := @not_induced_free_clique G [set x]; rewrite cards1; apply; last exact: free.
by move=> u v /set1P-> /set1P->; rewrite eqxx.
Qed.

(** Complete graphs are free of every pattern with a non-edge (positive family). *)
Lemma induced_free_Kn (n : nat) (H : sgraph) (x y : H) :
  x != y -> ~~ (x -- y) -> induced_free 'K_n H.
Proof.
move=> xy /negP nxy S i; apply: nxy; rewrite -(edge_diso' i) induced_edge.
by rewrite /edge_rel /= (inj_eq val_inj) (inj_eq (can_inj (bijK' i))).
Qed.

(** Positive example that cardinality does not decide: [K_4] is claw-free. *)
Lemma induced_free_K4_claw : induced_free 'K_4 'K_1,3.
Proof. by apply: (@induced_free_Kn 4 'K_1,3 (inr ord0) (inr (@Ordinal 3 1 isT))). Qed.

(** Negative example: an edge of the triangle is an induced [K_2]. *)
Lemma not_induced_free_K3_K2 : ~ induced_free 'K_3 'K_2.
Proof.
have := @not_induced_free_clique 'K_3 [set ord0; @Ordinal 3 1 isT].
by rewrite cards2; apply => u v _ _.
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
    [not_edge_disjoint_self], [del_edge_setE], [del_edge_set1],
    [edges_del_edge_set], [del_edge_set_nonedges], [del_edge_set_eq_diso],
    [chi_diso], [card_del_edge_set], [del_edge_setT], [del_edge_set_K3],
    [del_edge_set0], [connected_del_edge_set0],
    [k_edge_connected1], [connected_K2], [k_edge_connected_K2],
    [not_k_edge_connected_K1], [has_subgraph_refl], [has_subgraph_Kn],
    [induced_free_inhabited], [induced_free_diso], [induced_free_card],
    [not_induced_free_self], [not_induced_free_pattern0], [induced_free_host0],
    [not_induced_free_clique], [induced_free_K1], [induced_free_Kn],
    [induced_free_K4_claw], [not_induced_free_K3_K2],
    [complete_bipartite_KB], [not_complete_bipartite_K3],
    [tournament_C3_di], [tournament_oriented], [oriented_C3_di], [not_acyclic_C3_di],
    [acyclic_triv], [acyclic_irrefl]. *)

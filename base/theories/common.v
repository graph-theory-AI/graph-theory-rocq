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
From GTBase Require monochromatic.
From GTBase Require incidence.

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

(** ** Edge count

    [edge_count G] is the number of edges of the simple graph [G], [#|E(G)|]: unordered pairs of
    adjacent vertices.  Corpus-local copies also count the adjacent ORDERED pairs [(x, y)] with
    [enum_rank x < enum_rank y], one orientation per edge; [edge_count_rank] proves that count equal
    to [edge_count G], unconditionally (adjacent vertices are distinct, and the rank order picks
    exactly one orientation).  Counting both orientations gives twice as much and is a different
    quantity.  Grounding: [edge_count_Kn] ([K_0] and [K_1] have none, [K_2] one, [K_3] three) and
    invariance under isomorphism ([edge_count_diso]). *)
Definition edge_count (G : sgraph) : nat := #|E(G)|.

Lemma edge_count_rank (G : sgraph) :
  #|[set p : G * G | (p.1 -- p.2) && (enum_rank p.1 < enum_rank p.2)%N]| = edge_count G.
Proof.
set S := [set p : G * G | _].
have inS (p : G * G) : (p \in S) = (p.1 -- p.2) && (enum_rank p.1 < enum_rank p.2)%N by rewrite inE.
have inj : {in S &, injective (fun p : G * G => [set p.1; p.2])}.
  move=> [a b] [c d]; rewrite !inS => /andP[ab rab] /andP[cd rcd] /= eq.
  have cE : c \in [set a; b] by rewrite eq !inE eqxx.
  have dE : d \in [set a; b] by rewrite eq !inE eqxx orbT.
  move: cE dE; rewrite !inE => /orP[/eqP ca|/eqP cb] /orP[/eqP da|/eqP db].
  - by move: (sg_edgeNeq cd); rewrite ca da eqxx.
  - by rewrite ca db.
  - by move: rcd; rewrite cb da => /(ltn_trans rab); rewrite ltnn.
  - by move: (sg_edgeNeq cd); rewrite cb db eqxx.
rewrite /edge_count -(card_in_imset inj); apply: eq_card => e.
apply/imsetP/edgesP => [[[a b]]|[x [y [-> xy]]]].
- by rewrite inS => /andP[ab _] ->; exists a, b.
- have [rxy|ryx|exy] := ltngtP (enum_rank x) (enum_rank y).
  + by exists (x, y); first by rewrite inS xy rxy.
  + exists (y, x); first by rewrite inS sgP xy ryx.
    by rewrite setUC.
  + by move/val_inj/enum_rank_inj: exy => exy; move: xy; rewrite exy sg_irrefl.
Qed.

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

(** ** Ordered pairs between two vertex sets

    [edges_between A B] is the number of ORDERED pairs [(a, b)] with [a \in A], [b \in B] and
    [a -- b]; [nonedges_between A B] counts those with [~~ (a -- b)].  [A] and [B] are arbitrary:
    they may be empty or overlap.  A vertex [x] of [A :&: B] gives the diagonal pair [(x, x)],
    which is a NON-edge (adjacency is irreflexive), and an edge inside [A :&: B] is counted in
    both orientations.  The two counts partition [A x B] ([edges_nonedges_between]), and swapping
    [A] and [B] keeps each of them ([edges_between_sym], [nonedges_between_sym]).  On DISJOINT
    [A] and [B] the counts agree with the number of edges of [E(G)] meeting both sets
    ([edges_between_cross]) and with the number of edges of the complement between the sets
    ([nonedges_between_compl]).  With overlap these readings can fail (a shared vertex is a
    non-edge pair but no complement edge: [nonedges_between_compl_overlap]).  The edge-count
    reading may still agree for overlapping sets, for example when G is K1 and A = B is its full
    vertex set; the ordered non-edge count is then 1 and the complement count 0.
    Grounding: empty sets, a singleton ([edges_between_set1], [nonedges_between_set1]) and
    complete graphs, where exactly the diagonal pairs are non-edges ([nonedges_between_Kn],
    [edges_between_Kn], [edges_between_K2]). *)
Definition edges_between (G : sgraph) (A B : {set G}) : nat :=
  #|[set p : G * G | [&& p.1 \in A, p.2 \in B & p.1 -- p.2]]|.

Definition nonedges_between (G : sgraph) (A B : {set G}) : nat :=
  #|[set p : G * G | [&& p.1 \in A, p.2 \in B & ~~ (p.1 -- p.2)]]|.

(** ** Edge cuts

    [cut_size A] is the number of edges of [G] with one end in [A] and the other outside: the sets
    [e] of [E(G)] that meet [A] ([~~ [disjoint e & A]]) and are not contained in [A].  [A] is any
    vertex set; the empty and the full side have no cut edge ([cut_size_set0], [cut_size_setT]) and
    a side and its complement have the same cut ([cut_sizeC]).  The cut is the number of
    non-monochromatic edges under membership in [A] ([cut_size_non_monochromatic], with
    [GTBase.monochromatic.non_monochromatic_count]), and the ordered edge count between the two
    (disjoint) sides [A] and [~: A] ([cut_size_edges_between]).  Counting the non-monochromatic
    members of an ARBITRARY supplied family under an arbitrary colour map is the separate,
    graph-free [GTBase.monochromatic.non_monochromatic_count]. *)
Definition cut_size (G : sgraph) (A : {set G}) : nat :=
  #|[set e in E(G) | ~~ [disjoint e & A] && ~~ (e \subset A)]|.

(** ** Incidence degree

    The number of members of a SUPPLIED finite family containing a vertex is the graph-free
    [GTBase.incidence.incidence_degree] (exported by [base.v]); the family need not consist of
    edges.  At the edge set [E(G)] it is the graph degree [#|N(v)|] ([incidence_degree_edges]). *)

(** ** Matchings *)

(** A PERFECT matching: a [connectivity.matching] covering every vertex.

    Contract: [M] is a set of edges of [G] in which two members through a
    common vertex are equal ([matching M]), and every vertex lies in a member
    ([cover M = [set: G]]).  Equivalently ([perfect_matching_exactly_oneP]),
    in the presentation of the corpus-local copies, every member is an edge
    and every vertex lies in EXACTLY one member.  Degenerate cases: on the
    empty graph [set0] is a perfect matching ([perfect_matching0_K0]), on a
    nonempty graph it is not ([not_perfect_matching0]); a family with a member
    that is not an edge, such as a loop [[set x]], is never one
    ([not_perfect_matching_loop]); the members pair the vertices up, so
    [#|G| = 2 * #|M|] ([card_perfect_matching]) and a graph of odd order has
    none ([not_perfect_matching_odd], for instance [K_3]:
    [not_perfect_matching_K3]); the edge of [K_2] is one
    ([perfect_matching_K2]). *)
Definition perfect_matching (G : sgraph) (M : {set {set G}}) : Prop :=
  matching M /\ cover M = [set: G].

Lemma perfect_matching_matching (G : sgraph) (M : {set {set G}}) :
  perfect_matching M -> matching M.
Proof. by case. Qed.

Lemma perfect_matching_cover (G : sgraph) (M : {set {set G}}) :
  perfect_matching M -> cover M = [set: G].
Proof. by case. Qed.

(** Every member is an edge. *)
Lemma perfect_matching_edge (G : sgraph) (M : {set {set G}}) (e : {set G}) :
  perfect_matching M -> e \in M -> e \in E(G).
Proof. by move=> [[MS _] _] /MS. Qed.

(** The presentation of the corpus-local copies (X18, X24, X25): every member
    is an edge and every vertex lies in exactly one member. *)
Lemma perfect_matching_exactly_oneP (G : sgraph) (M : {set {set G}}) :
  perfect_matching M <->
  M \subset E(G) /\ forall v : G, #|[set e in M | v \in e]| = 1.
Proof.
split=> [[[MS M1] covM]|[MS M1]].
- split=> [|v]; first exact/subsetP.
  apply/eqP; rewrite eqn_leq; apply/andP; split.
  + apply/card_le1_eqP => e1 e2; rewrite !inE => /andP[e1M ve1] /andP[e2M ve2].
    exact: (M1 _ _ e2M e1M v ve2 ve1).
  + rewrite card_gt0; apply/set0Pn.
    have: v \in cover M by rewrite covM inE.
    by case/bigcupP=> e eM ve; exists e; rewrite inE eM ve.
- split.
  + split=> [e /(subsetP MS) //|e1 e2 e1M e2M x xe1 xe2].
    have /card_le1_eqP H : #|[set e in M | x \in e]| <= 1 by rewrite M1.
    symmetry; apply: H; rewrite !inE.
    * by rewrite e1M xe1.
    * by rewrite e2M xe2.
  + apply/setP => v; rewrite in_setT; apply/bigcupP.
    have: 0 < #|[set e in M | v \in e]| by rewrite M1.
    by rewrite card_gt0 => /set0Pn[e]; rewrite inE => /andP[eM ve]; exists e.
Qed.

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

(** [G] contains [H] as a (not necessarily induced) subgraph.

    Contract: the HOST [G] comes first and the PATTERN [H] second (the corpus-local
    [subgraph_of H G] copies take them the other way round).  [has_subgraph G H]
    holds iff some injective map [H -> G] sends every edge of [H] to an edge of [G]
    ([has_subgraphP]); non-edges of [H] may land on edges of [G].  So this is
    ordinary containment: it is neither an induced copy ([induced_free], upstream
    [isubgraph]), which also preserves non-edges ([has_subgraph_not_induced]), nor a
    minor.  Upstream [subgraph] asks only for [hom_s], which constrains edges with
    distinct images; injectivity and irreflexivity make that premise automatic, so
    the characterization needs no guard.  Degenerate cases: every host contains the
    empty pattern ([has_subgraph0], [has_subgraph_K0]); the empty host contains
    exactly the empty patterns ([has_subgraph_K0_host]); a pattern never has more
    vertices than its host ([has_subgraph_card]). *)
Definition has_subgraph (G H : sgraph) : Prop := subgraph H G.

(** The witness presentation of the corpus-local copies: an injective map that
    preserves adjacency.  Unconditional. *)
Lemma has_subgraphP (G H : sgraph) :
  has_subgraph G H <->
  exists f : H -> G, injective f /\ forall x y : H, x -- y -> f x -- f y.
Proof.
split=> [[f inj_f hom_f]|[f [inj_f hom_f]]].
- exists f; split=> // x y xy.
  have fxy : f x != f y by rewrite (inj_eq inj_f) (sg_edgeNeq xy).
  exact: hom_f xy fxy.
- by exists f => // x y xy _; exact: hom_f.
Qed.

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

(** The empty family is a perfect matching of the empty graph. *)
Lemma perfect_matching0_K0 : perfect_matching (G := 'K_0) set0.
Proof.
split; first by split=> [e|e1 e2]; rewrite inE.
by apply/setP => v; have := ltn_ord v; rewrite ltn0.
Qed.

(** A loop [[set x]] is never a member (members are edges). *)
Lemma not_perfect_matching_loop (G : sgraph) (M : {set {set G}}) (x : G) :
  [set x] \in M -> ~ perfect_matching M.
Proof.
move=> xM pm; have /edgesP[y [z [eq yz]]] := perfect_matching_edge pm xM.
by have := cards1 x; rewrite eq cards2 (sg_edgeNeq yz).
Qed.

(** The members pair the vertices up. *)
Lemma card_perfect_matching (G : sgraph) (M : {set {set G}}) :
  perfect_matching M -> #|G| = 2 * #|M|.
Proof.
move=> [[MS M1] covM].
have e2 : forall e, e \in M -> #|e| = 2.
  by move=> e /MS /edgesP[x [y [-> xy]]]; rewrite cards2 (sg_edgeNeq xy).
have part : partition M [set: G].
  rewrite /partition covM eqxx /=; apply/andP; split.
  - apply/trivIsetP => e1 e2' e1M e2M' e12; rewrite -setI_eq0; apply/eqP/setP => x.
    rewrite !inE; apply/negbTE/negP => /andP[xe1 xe2].
    by move: e12; rewrite (M1 _ _ e1M e2M' x xe1 xe2) eqxx.
  - by apply/negP => /e2; rewrite cards0.
by rewrite -cardsT (card_partition part) (eq_bigr (fun _ => 2) e2) sum_nat_const mulnC.
Qed.

(** Hence a graph of odd order has no perfect matching. *)
Lemma not_perfect_matching_odd (G : sgraph) (M : {set {set G}}) :
  odd #|G| -> ~ perfect_matching M.
Proof. by move=> oddG pm; move: oddG; rewrite (card_perfect_matching pm) oddM. Qed.

(** [K_3]: three vertices cannot be paired up. *)
Lemma not_perfect_matching_K3 (M : {set {set 'K_3}}) : ~ perfect_matching M.
Proof. by apply: not_perfect_matching_odd; rewrite card_ord. Qed.

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

(** *** edge count *)

Lemma edge_count_Kn (n : nat) : edge_count 'K_n = 'C(n, 2).
Proof. exact: card_edge_Kn. Qed.

Lemma edge_count_K0_K1 : edge_count 'K_0 = 0 /\ edge_count 'K_1 = 0.
Proof. by rewrite !edge_count_Kn. Qed.

Lemma edge_count_K2 : edge_count 'K_2 = 1.
Proof. by rewrite edge_count_Kn. Qed.

Lemma edge_count_K3 : edge_count 'K_3 = 3.
Proof. by rewrite edge_count_Kn. Qed.

Lemma edge_count_diso (G H : sgraph) : G ≃ H -> edge_count G = edge_count H.
Proof. exact: diso_card_edge. Qed.

(** *** graph complement

    The canonical complement is upstream [GraphTheory.sgraph.compl G], with relation
    [compl_rel]: same vertices, two DISTINCT vertices are adjacent iff they are not
    adjacent in [G], and there are no loops ([compl_adjE]).  Empty and one-vertex graphs
    are valid inputs.  Upstream [diso_compl] gives [compl (compl G) ≃ G]; a graph built
    with [SGraph] from a relation pointwise equal to [compl_rel] is related to [compl G]
    by the identity isomorphism ([compl_eq_diso]), which does not equate the opaque
    symmetry/irreflexivity proofs. *)

Lemma compl_adjE (G : sgraph) (x y : G) :
  @edge_rel (compl G) x y = (x != y) && ~~ (x -- y).
Proof. by []. Qed.

Lemma compl_eq_diso (G : sgraph) (r : rel G) (r_sym : symmetric r) (r_irrefl : irreflexive r) :
  r =2 @compl_rel G -> diso (SGraph r_sym r_irrefl) (compl G).
Proof. by move=> rE; apply: eq_diso => x y; rewrite rE. Qed.

(** Off the diagonal, the complement negates adjacency. *)
Lemma compl_adj_offdiag (G : sgraph) (x y : G) :
  x != y -> @edge_rel (compl G) x y = ~~ (x -- y).
Proof. by move=> xy; rewrite compl_adjE xy. Qed.

(** No loops, even though [x -- x] is false in [G]. *)
Lemma compl_noloop (G : sgraph) (x : G) : ~~ @edge_rel (compl G) x x.
Proof. by rewrite compl_adjE eqxx. Qed.

(** The complement of a complete graph has no edges (in particular [K_0] and [K_1]). *)
Lemma compl_Kn_edgeless (n : nat) (x y : 'K_n) : ~~ @edge_rel (compl 'K_n) x y.
Proof. by rewrite compl_adjE /= andbN. Qed.

(** Double complement, up to isomorphism (upstream). *)
Lemma compl_compl_diso (G : sgraph) : compl (compl G) ≃ G.
Proof. exact: diso_compl. Qed.

(** *** ordered pairs between two vertex sets *)

Lemma edges_between_sym (G : sgraph) (A B : {set G}) : edges_between A B = edges_between B A.
Proof.
rewrite /edges_between -(card_imset _ (can_inj (@swap_pairK G G))); apply: eq_card => -[x y].
rewrite [in RHS]inE; apply/imsetP/and3P => [[[a b]]|[/= xB yA xy]].
- by rewrite inE /= => /and3P[aA bB ab] [-> ->]; split; rewrite //= sg_sym.
- by exists (y, x); rewrite // inE /= yA xB sg_sym.
Qed.

Lemma nonedges_between_sym (G : sgraph) (A B : {set G}) :
  nonedges_between A B = nonedges_between B A.
Proof.
rewrite /nonedges_between -(card_imset _ (can_inj (@swap_pairK G G))); apply: eq_card => -[x y].
rewrite [in RHS]inE; apply/imsetP/and3P => [[[a b]]|[/= xB yA xy]].
- by rewrite inE /= => /and3P[aA bB ab] [-> ->]; split; rewrite //= sg_sym.
- by exists (y, x); rewrite // inE /= yA xB sg_sym.
Qed.

(** Each pair of [A x B] is an edge or a non-edge. *)
Lemma edges_nonedges_between (G : sgraph) (A B : {set G}) :
  edges_between A B + nonedges_between A B = #|A| * #|B|.
Proof.
rewrite -cardsX -(cardsID [set p : G * G | p.1 -- p.2] (setX A B)) /edges_between /nonedges_between.
by congr (_ + _); apply: eq_card => p; rewrite !inE;
  case: (p.1 \in A); case: (p.2 \in B); case: (p.1 -- p.2).
Qed.

Lemma edges_between_set0 (G : sgraph) (B : {set G}) : edges_between set0 B = 0.
Proof. by apply/eqP; rewrite cards_eq0; apply/eqP/setP => p; rewrite !inE. Qed.

Lemma edges_between0 (G : sgraph) (A : {set G}) : edges_between A set0 = 0.
Proof. by apply/eqP; rewrite cards_eq0; apply/eqP/setP => p; rewrite !inE andbF. Qed.

Lemma nonedges_between_set0 (G : sgraph) (B : {set G}) : nonedges_between set0 B = 0.
Proof. by apply/eqP; rewrite cards_eq0; apply/eqP/setP => p; rewrite !inE. Qed.

Lemma nonedges_between0 (G : sgraph) (A : {set G}) : nonedges_between A set0 = 0.
Proof. by apply/eqP; rewrite cards_eq0; apply/eqP/setP => p; rewrite !inE andbF. Qed.

(** A vertex of [A :&: B] gives the diagonal pair: one non-edge, no edge. *)
Lemma edges_between_set1 (G : sgraph) (x : G) : edges_between [set x] [set x] = 0.
Proof.
apply/eqP; rewrite cards_eq0; apply/eqP/setP => -[a b]; rewrite !inE /=.
by apply/negbTE; apply/and3P => -[/eqP-> /eqP->]; rewrite sg_irrefl.
Qed.

Lemma nonedges_between_set1 (G : sgraph) (x : G) : nonedges_between [set x] [set x] = 1.
Proof.
apply: (@eq_card1 _ (x, x)) => -[a b]; rewrite !inE /= xpair_eqE.
by apply/and3P/andP => [[/eqP-> /eqP-> _]|[/eqP-> /eqP->]]; rewrite ?sg_irrefl ?eqxx.
Qed.

(** In a complete graph exactly the diagonal pairs are non-edges. *)
Lemma nonedges_between_Kn (n : nat) (A B : {set 'K_n}) : nonedges_between A B = #|A :&: B|.
Proof.
have inj : injective (fun x : 'K_n => (x, x)) by move=> x y [].
rewrite -(card_imset _ inj) /nonedges_between; apply: eq_card => -[x y].
rewrite [in LHS]inE /=; apply/and3P/imsetP => [[xA yB]|[z]].
- rewrite negbK => /eqP exy; exists x; last by rewrite exy.
  by rewrite inE xA /= exy.
- rewrite inE => /andP[zA zB] [-> ->]; split=> //.
  by rewrite /= negbK eqxx.
Qed.

Lemma edges_between_Kn (n : nat) (A B : {set 'K_n}) :
  edges_between A B = #|A| * #|B| - #|A :&: B|.
Proof. by rewrite -nonedges_between_Kn -edges_nonedges_between addnK. Qed.

(** Two ordered edges in [K_2] taken whole. *)
Lemma edges_between_K2 : edges_between [set: 'K_2] [set: 'K_2] = 2.
Proof. by rewrite edges_between_Kn setIid cardsT card_ord. Qed.

(** On DISJOINT sets: the edges of [E(G)] meeting both sets. *)
Lemma edges_between_cross (G : sgraph) (A B : {set G}) : [disjoint A & B] ->
  edges_between A B = #|[set e in E(G) | (e :&: A != set0) && (e :&: B != set0)]|.
Proof.
move=> dAB.
have Dne (x y : G) : x \in A -> y \in B -> x != y.
  move=> xA yB; apply/eqP => exy.
  by move: (disjointFr dAB xA); rewrite exy yB.
have key : [set e in E(G) | (e :&: A != set0) && (e :&: B != set0)]
         = (fun p : G * G => [set p.1; p.2])
             @: [set p : G * G | [&& p.1 \in A, p.2 \in B & p.1 -- p.2]].
  apply/setP => e; rewrite !inE; apply/idP/imsetP => [|[p]].
  - case/andP => eE /andP[/set0Pn[a]]; rewrite inE => /andP[ae aA].
    case/set0Pn => b; rewrite inE => /andP[be bB].
    have ab : a != b by exact: Dne.
    move: eE => /edgesP[x [y] [exy xy]].
    rewrite exy !inE in ae be.
    case/orP: ae => /eqP ax; case/orP: be => /eqP bxy.
    + by rewrite ax bxy eqxx in ab.
    + exists (a, b); last by rewrite /= exy ax bxy.
      by rewrite inE /= aA bB ax bxy.
    + exists (a, b); last by rewrite /= exy ax bxy setUC.
      by rewrite inE /= aA bB ax bxy sg_sym.
    + by rewrite ax bxy eqxx in ab.
  - rewrite inE => /and3P[p1 p2 p12] ->.
    apply/andP; split.
      by rewrite in_sg_edge_set; apply/existsP; exists p.1;
         apply/existsP; exists p.2; rewrite p12 eqxx.
    apply/andP; split; apply/set0Pn.
    + by exists p.1; rewrite !inE eqxx p1.
    + by exists p.2; rewrite !inE eqxx orbT p2.
rewrite /edges_between key card_in_imset //.
move=> p q; rewrite !inE => /and3P[p1 p2 _] /and3P[q1 q2 _] eqpq.
have H1 : p.1 = q.1.
  move: eqpq => /setP /(_ p.1); rewrite !inE eqxx => /esym/orP[/eqP//|/eqP pq2].
  by move: (Dne _ _ p1 q2); rewrite pq2 eqxx.
have H2 : p.2 = q.2.
  move: eqpq => /setP /(_ q.2); rewrite !inE eqxx orbT => /orP[/eqP q2p1|/eqP //].
  by move: (Dne _ _ p1 q2); rewrite -q2p1 eqxx.
clear eqpq p1 p2 q1 q2; case: p H1 H2 => a b /= -> ->; by case: q.
Qed.

(** On DISJOINT sets: the edges of the complement between the sets. *)
Lemma nonedges_between_compl (G : sgraph) (A B : {set G}) : [disjoint A & B] ->
  nonedges_between A B = @edges_between (compl G) A B.
Proof.
move=> dAB; apply: eq_card => -[x y]; rewrite !inE /= compl_adjE.
case xA: (x \in A); case yB: (y \in B) => //=.
suff -> : x != y by [].
by apply/eqP => exy; move: (disjointFr dAB xA); rewrite exy yB.
Qed.

(** The guard has teeth: a shared vertex is a non-edge pair but no complement edge. *)
Lemma nonedges_between_compl_overlap (G : sgraph) (x : G) :
  nonedges_between [set x] [set x] = 1 /\ @edges_between (compl G) [set x] [set x] = 0.
Proof.
split; first exact: nonedges_between_set1.
apply/eqP; rewrite cards_eq0; apply/eqP/setP => -[a b]; rewrite !inE /=.
by apply/negbTE; apply/and3P => -[/eqP-> /eqP->]; rewrite ?compl_adjE eqxx.
Qed.

(** *** edge cuts *)

Lemma cut_sizeC (G : sgraph) (A : {set G}) : cut_size (~: A) = cut_size A.
Proof.
apply: eq_card => e; rewrite !inE; congr (_ && _).
by rewrite andbC [[disjoint e & ~: A]]disjoints_subset setCK -disjoints_subset.
Qed.

Lemma cut_size_set0 (G : sgraph) : cut_size (set0 : {set G}) = 0.
Proof. by apply/eqP; rewrite cards_eq0; apply/eqP/setP => e; rewrite !inE disjoints_subset setC0 subsetT /= andbF. Qed.

Lemma cut_size_setT (G : sgraph) : cut_size [set: G] = 0.
Proof. by apply/eqP; rewrite cards_eq0; apply/eqP/setP => e; rewrite !inE subsetT /= !andbF. Qed.

(** The cut is the count of non-monochromatic edges under membership in [A]. *)
Lemma cut_size_non_monochromatic (G : sgraph) (A : {set G}) :
  cut_size A = GTBase.monochromatic.non_monochromatic_count E(G) (fun x : G => x \in A).
Proof.
apply: eq_card => e; rewrite !inE; case: (e \in E(G)) => //=.
rewrite -setI_eq0; apply/andP/GTBase.monochromatic.non_monochromatic_onP.
  case=> /set0Pn[x /setIP[xe xA]] /subsetPn[y ye yA].
  by exists x, y; rewrite xA (negbTE yA).
case=> x [y [xe ye xy]].
have [xA|xA] := boolP (x \in A); have [yA|yA] := boolP (y \in A).
- by move: xy; rewrite xA yA.
- by split; [apply/set0Pn; exists x; rewrite inE xe xA | apply/subsetPn; exists y].
- by split; [apply/set0Pn; exists y; rewrite inE ye yA | apply/subsetPn; exists x].
- by move: xy; rewrite (negbTE xA) (negbTE yA).
Qed.

(** On the two sides [A] and [~: A] (disjoint), the cut is the ordered edge count. *)
Lemma cut_size_edges_between (G : sgraph) (A : {set G}) : cut_size A = edges_between A (~: A).
Proof.
have dA : [disjoint A & ~: A] by rewrite disjoints_subset setCK.
rewrite edges_between_cross //; apply: eq_card => e; rewrite !inE; congr (_ && _).
by rewrite !setI_eq0 [[disjoint e & ~: A]]disjoints_subset setCK.
Qed.

(** *** incidence degree *)

(** At the edge set, the incidence degree is the graph degree: the edges at [v] are the
    [[set v; w]] for the neighbours [w] of [v]. *)
Lemma incidence_degree_edges (G : sgraph) (v : G) :
  GTBase.incidence.incidence_degree E(G) v = #|N(v)|.
Proof.
have inj : {in N(v) &, injective (fun w : G => [set v; w])}.
  move=> w1 w2 vw1 _ /= h.
  have : w1 \in [set v; w2] by rewrite -h set22.
  rewrite !inE => /orP[/eqP w1v|/eqP //].
  by move: vw1; rewrite in_opn w1v sg_irrefl.
rewrite /GTBase.incidence.incidence_degree -(card_in_imset inj); apply: eq_card => e.
rewrite !inE; apply/andP/imsetP => [[/edgesP[x [y [-> xy]]]]|[w vw ->]].
- rewrite !inE => /orP[/eqP vx|/eqP vy].
  + by exists y; rewrite vx // in_opn.
  + by exists x; [rewrite in_opn vy sgP | rewrite vy setUC].
- by rewrite in_edges -in_opn vw !inE eqxx.
Qed.

(** *** subgraph containment *)

(** Every graph contains itself (non-vacuity). *)
Lemma has_subgraph_refl (G : sgraph) : has_subgraph G G.
Proof. by exists id. Qed.

(** [K_n] contains every graph on at most [n] vertices. *)
Lemma has_subgraph_Kn n (G : sgraph) : #|G| <= n -> has_subgraph 'K_n G.
Proof. exact: sub_Kn. Qed.

(** Containment is transitive. *)
Lemma has_subgraph_trans (G H K : sgraph) :
  has_subgraph G H -> has_subgraph H K -> has_subgraph G K.
Proof.
move=> /has_subgraphP[f [inj_f hom_f]] /has_subgraphP[g [inj_g hom_g]].
apply/has_subgraphP; exists (f \o g); split; first exact: inj_comp.
by move=> x y xy; apply: hom_f; exact: hom_g.
Qed.

(** A pattern never has more vertices than its host. *)
Lemma has_subgraph_card (G H : sgraph) : has_subgraph G H -> #|H| <= #|G|.
Proof. by case=> f inj_f _; exact: leq_card inj_f. Qed.

(** Every host contains every empty pattern. *)
Lemma has_subgraph0 (G H : sgraph) : #|H| = 0 -> has_subgraph G H.
Proof.
move=> H0; have no (x : H) : False.
  by move/eqP: H0; rewrite -leqn0 leqNgt => /negP; apply; apply/card_gt0P; exists x.
apply/has_subgraphP; exists (fun x => match no x with end).
by split=> [x|x]; case: (no x).
Qed.

Lemma has_subgraph_K0 (G : sgraph) : has_subgraph G 'K_0.
Proof. by apply: has_subgraph0; rewrite card_ord. Qed.

(** The empty host contains exactly the empty patterns. *)
Lemma has_subgraph_K0_host (H : sgraph) : has_subgraph 'K_0 H <-> #|H| = 0.
Proof.
split=> [/has_subgraph_card|/has_subgraph0 //].
by rewrite card_ord leqn0 => /eqP.
Qed.

(** Deleting edges leaves a subgraph of the host (the identity embedding). *)
Lemma has_subgraph_del_edge_set (G : sgraph) (F : {set {set G}}) :
  has_subgraph G (del_edge_set G F).
Proof.
apply/has_subgraphP; exists (fun x : del_edge_set G F => x : G); split=> // x y.
by rewrite del_edge_setE => /andP[].
Qed.

(** An isomorphism of hosts carries a contained pattern. *)
Lemma has_subgraph_host_diso (G G' H : sgraph) :
  diso G G' -> has_subgraph G H -> has_subgraph G' H.
Proof.
move=> i /has_subgraphP[f [inj_f hom_f]]; apply/has_subgraphP.
exists (fun x => i (f x)); split.
- by move=> x y /(@bij_injective _ _ (diso_v i)) /inj_f.
- by move=> x y xy; rewrite edge_diso; exact: hom_f.
Qed.

(** Ordinary containment is not induced containment: the two-vertex graph without
    edges is a subgraph of [K_2], but no induced subgraph of [K_2] is isomorphic to
    it, since the only two-vertex induced subgraph of [K_2] keeps its edge. *)
Lemma has_subgraph_not_induced :
  has_subgraph 'K_2 (del_edge_set 'K_2 [set [set: 'K_2]]) /\
  induced_free 'K_2 (del_edge_set 'K_2 [set [set: 'K_2]]).
Proof.
split; first exact: has_subgraph_del_edge_set.
have noE (x y : 'K_2) : ~~ @edge_rel (del_edge_set 'K_2 [set [set: 'K_2]]) x y.
  rewrite del_edge_set1; have [->|xy] := eqVneq x y; first by rewrite sg_irrefl.
  by rewrite eqEcard subsetT cards2 xy cardsT card_ord andbF.
move=> S h.
have cS : #|S| = 2 by rewrite -card_sig (card_bij (diso_v h)) card_ord.
have ST : S = setT by apply/eqP; rewrite eqEcard subsetT cS cardsT card_ord.
have a0 : (ord0 : 'K_2) \in S by rewrite ST inE.
have a1 : (ord_max : 'K_2) \in S by rewrite ST inE.
have := edge_diso h (Sub ord0 a0) (Sub ord_max a1).
by rewrite (negbTE (noE _ _)).
Qed.

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
    [not_perfect_matching0], [perfect_matching_exactly_oneP], [perfect_matching0_K0],
    [not_perfect_matching_loop], [card_perfect_matching], [not_perfect_matching_odd],
    [not_perfect_matching_K3], [hamiltonian_K3], [not_hamiltonian_K1],
    [traceable_K1], [hamiltonian_cycle_size], [hamiltonian_K2], [edge_disjointC], [edge_disjoint0],
    [not_edge_disjoint_self], [del_edge_setE], [del_edge_set1],
    [edges_del_edge_set], [del_edge_set_nonedges], [del_edge_set_eq_diso],
    [chi_diso], [card_del_edge_set], [del_edge_setT], [del_edge_set_K3],
    [del_edge_set0], [connected_del_edge_set0],
    [k_edge_connected1], [connected_K2], [k_edge_connected_K2],
    [not_k_edge_connected_K1], [has_subgraph_refl], [has_subgraph_Kn],
    [has_subgraphP], [has_subgraph_trans], [has_subgraph_card], [has_subgraph0],
    [has_subgraph_K0], [has_subgraph_K0_host], [has_subgraph_del_edge_set],
    [has_subgraph_not_induced], [has_subgraph_host_diso], [compl_adjE], [compl_eq_diso],
    [compl_adj_offdiag], [compl_noloop], [compl_Kn_edgeless], [compl_compl_diso],
    [edge_count_rank], [edge_count_Kn], [edge_count_K0_K1], [edge_count_K2], [edge_count_K3],
    [edge_count_diso], [edges_between_sym], [nonedges_between_sym], [edges_nonedges_between],
    [edges_between_set0], [edges_between0], [nonedges_between_set0], [nonedges_between0],
    [edges_between_set1], [nonedges_between_set1], [nonedges_between_Kn], [edges_between_Kn],
    [edges_between_K2], [edges_between_cross], [nonedges_between_compl],
    [nonedges_between_compl_overlap],
    [cut_sizeC], [cut_size_set0], [cut_size_setT], [cut_size_non_monochromatic],
    [cut_size_edges_between], [incidence_degree_edges],
    [induced_free_inhabited], [induced_free_diso], [induced_free_card],
    [not_induced_free_self], [not_induced_free_pattern0], [induced_free_host0],
    [not_induced_free_clique], [induced_free_K1], [induced_free_Kn],
    [induced_free_K4_claw], [not_induced_free_K3_K2],
    [complete_bipartite_KB], [not_complete_bipartite_K3],
    [tournament_C3_di], [tournament_oriented], [oriented_C3_di], [not_acyclic_C3_di],
    [acyclic_triv], [acyclic_irrefl]. *)

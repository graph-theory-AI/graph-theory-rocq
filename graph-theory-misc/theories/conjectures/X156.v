(** * GTMisc.conjectures.X156 -- v2 random block-tree diameter row *)

From GTBase Require Export base.
From GraphTheory Require Import bij.
From GTBase Require Import graph_classes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X156 vocabulary ***********************************************)

(** Blocks (McDiarmid and Scott, arXiv:1408.4257, l.151 of the e-print): a block of G is a maximal
    2-connected subgraph, or the subgraph formed by a bridge, or an isolated vertex.  These are the
    maximal vertex sets B such that G[B] is connected without a cut vertex (Diestel's "maximal
    connected subgraph without a cut vertex"); a block is an induced subgraph, so it is its vertex
    set and, as a graph, [induced B].  [x156_no_cut_vertexb G B]: B is nonempty, G[B] is connected
    and stays connected after deleting any one vertex of B (K_1, K_2 or 2-connected). *)
Definition x156_no_cut_vertexb (G : sgraph) (B : {set G}) : bool :=
  [&& B != set0, connectedb B & [forall v in B, connectedb (B :\ v)]].

Definition x156_blockb (G : sgraph) (B : {set G}) : bool :=
  x156_no_cut_vertexb B &&
  [forall B' : {set G}, (B \subset B') && x156_no_cut_vertexb B' ==> (B' == B)].

(** The block tree bt(G) (l.174): a node x_v = [inl v] per vertex, a node y_B = [inr B] per block,
    x_v ~ y_B iff v is in B.  The sets that are not blocks are isolated nodes; they change no
    distance between other nodes and no diameter. *)
Definition x156_block_tree_rel (G : sgraph) : rel (G + {set G})%type :=
  fun p q => match p, q with
             | inl v, inr B => (v \in B) && x156_blockb B
             | _, _ => false
             end.

Definition x156_block_tree (G : sgraph) : sgraph := fg_mk_sgraph (@x156_block_tree_rel G).

(** The diameter is at most d (l.289-290: the maximum distance between two vertices in the same
    component); [graph_dist] is the shortest-path distance on reachable pairs. *)
Definition x156_diameter_leb (T : sgraph) (d : nat) : bool :=
  [forall p : T, forall q : T, connect (--) p q ==> (graph_dist p q <= d)].

(** A block-stable class (l.152-154): closed under isomorphism, and G is in the class iff each
    block of G is. *)
Definition x156_block_stable (A : sgraph -> bool) : Prop :=
  GTBase.graph_classes.iso_closed (fun G : sgraph => A G) /\
  forall G : sgraph, A G <-> (forall B : {set G}, x156_blockb B -> A (induced B)).

(** The connected graphs of the class on the vertex set [n] = 'I_n (l.180), each labelled graph
    once (valid edge sets only). *)
Definition x156_connected_member (A : sgraph -> bool) (n : nat) (E : {set {set 'I_n}}) : bool :=
  [&& fg_valid_labelled_edges E, A (fg_labelled_sgraph E) & connectedb [set: fg_labelled_sgraph E]].

(** With high probability along the n with a positive total weight (l.180: "we implicitly
    consider only integers n such that A_n is non-empty"; l.185: Pr(E_n) -> 1): fg_whp's body with
    its positivity turned into a hypothesis; the guard a <= b keeps the subtraction b - a exact. *)
Definition x156_whp_where_defined
    (T : nat -> finType) (w : forall n : nat, T n -> nat) (P : forall n : nat, pred (T n)) : Prop :=
  forall a b : nat, 0 < a -> a <= b ->
    eventually (fun n =>
      0 < fg_total_weight (w n) ->
      b * fg_event_weight (w n) (P n) >= (b - a) * fg_total_weight (w n)).

(** ** Sanity lemmas ********************************************************)

Lemma x156_graph_dist_refl (G : sgraph) (x : G) : graph_dist x x = 0.
Proof.
rewrite /graph_dist; case: ex_minnP => m hm hmin.
apply/eqP; rewrite -leqn0; apply: hmin.
by rewrite /= inE eqxx.
Qed.

Lemma x156_graph_dist0 (G : sgraph) (x y : G) : graph_dist x y = 0 -> x = y.
Proof.
rewrite /graph_dist; case: ex_minnP => m hm _ m0; move: hm; rewrite m0 /=.
case/orP => [|c0]; first by rewrite inE => /eqP ->.
have pos : 0 < #|G| by apply/card_gt0P; exists x.
by move: pos; rewrite -(eqP c0).
Qed.

Lemma x156_connected_le1 (G : sgraph) (S : {set G}) :
  (forall x y : G, x \in S -> y \in S -> x = y) -> connected S.
Proof.
move=> h.
first [ by move=> x xS y yS; rewrite (h x y xS yS); exact: connect0
      | by move=> x y xS yS; rewrite (h x y xS yS); exact: connect0 ].
Qed.

Lemma x156_blockb_setT (G : sgraph) : x156_no_cut_vertexb [set: G] -> x156_blockb [set: G].
Proof.
move=> h; rewrite /x156_blockb h /=; apply/forallP => B'; apply/implyP => /andP [sub _].
by rewrite eqEsubset subsetT sub.
Qed.

Lemma x156_no_cut_K1 : x156_no_cut_vertexb [set: 'K_1].
Proof.
have e : [set: 'K_1] = [set ord0] by apply/setP => x; rewrite !inE (ord1 x) eqxx.
rewrite e; apply/and3P; split.
- by apply/set0Pn; exists ord0; rewrite inE.
- by apply/connectedP; exact: connected1.
- apply/forall_inP => v _; apply/connectedP; apply: x156_connected_le1 => x y.
  by rewrite (ord1 x) (ord1 y).
Qed.

Lemma x156_no_cut_K2 : x156_no_cut_vertexb [set: 'K_2].
Proof.
apply/and3P; split.
- by apply/set0Pn; exists ord0; rewrite inE.
- by apply/connectedP; exact: connected_K2.
- apply/forall_inP => v _; apply/connectedP; apply: x156_connected_le1 => x y.
  rewrite !in_setD1 => /andP [xv _] /andP [yv _].
  apply/eqP; move: xv yv.
  by case: x => [[|[|?]] ?]; case: y => [[|[|?]] ?]; case: v => [[|[|?]] ?].
Qed.

(** An isolated vertex is a block; a bridge with its two ends is a block. *)
Lemma x156_blockb_K1 : x156_blockb [set: 'K_1].
Proof. exact: x156_blockb_setT x156_no_cut_K1. Qed.

Lemma x156_blockb_K2 : x156_blockb [set: 'K_2].
Proof. exact: x156_blockb_setT x156_no_cut_K2. Qed.

(** A vertex with a neighbour is no block on its own. *)
Lemma x156_K2_vertex_not_block : ~~ x156_blockb [set (ord0 : 'K_2)].
Proof.
apply/negP => /andP [_ /forallP /(_ [set: 'K_2])].
rewrite subsetT x156_no_cut_K2 /= => /eqP e.
by move: (in_setT (ord_max : 'K_2)); rewrite e inE => /eqP /(congr1 val).
Qed.

Lemma x156_block_tree_edge (G : sgraph) (v : G) (B : {set G}) :
  v \in B -> x156_blockb B -> (inl v : x156_block_tree G) -- inr B.
Proof.
move=> vB bB.
have e : (inl v : x156_block_tree G) -- inr B =
         (inl v != inr B :> (G + {set G})%type) && ((v \in B) && x156_blockb B || false) by [].
by rewrite e vB bB.
Qed.

(** The bound is not vacuous: bt(K_2) is the path x_0 - y - x_1, of diameter 2, not 0. *)
Lemma x156_K2_block_tree_not_diameter0 : ~~ x156_diameter_leb (x156_block_tree 'K_2) 0.
Proof.
have pq := x156_block_tree_edge (in_setT (ord0 : 'K_2)) x156_blockb_K2.
apply/negP => /forallP /(_ (inl ord0)) /forallP /(_ (inr [set: 'K_2])) /implyP /(_ (connect1 pq)).
by rewrite leqn0 => /eqP /x156_graph_dist0.
Qed.

(** The class of all graphs is block-stable. *)
Lemma x156_all_graphs_block_stable : x156_block_stable (fun _ : sgraph => true).
Proof.
split; first by move=> G H _ _.
by move=> G; split.
Qed.

Lemma x156_no_cut_pair (G : sgraph) (u v : G) : u -- v -> x156_no_cut_vertexb [set u; v].
Proof.
move=> uv; apply/and3P; split.
- by apply/set0Pn; exists u; rewrite !inE eqxx.
- by apply/connectedP; exact: (connected2 uv).
- apply/forall_inP => w wS; apply/connectedP; apply: x156_connected_le1 => x y.
  rewrite !in_setD1 => /andP [xw xS] /andP [yw yS].
  move: wS xS yS xw yw; rewrite !in_set2.
  by case/orP => /eqP -> /orP [] /eqP -> /orP [] /eqP ->; rewrite ?eqxx.
Qed.

(** Every set without a cut vertex lies in a block (a largest such superset). *)
Lemma x156_block_above (G : sgraph) (S : {set G}) :
  x156_no_cut_vertexb S -> exists2 B, x156_blockb B & S \subset B.
Proof.
move=> hS.
pose P := fun B : {set G} => x156_no_cut_vertexb B && (S \subset B).
have PS : P S by rewrite /P /= hS subxx.
case: (@arg_maxnP _ S P (fun B => #|B|) PS) => B0 PB0 maxB0.
case/andP: PB0 => nc0 sub0; exists B0 => //.
rewrite /x156_blockb nc0 /=; apply/forallP => B'; apply/implyP => /andP [sB nc'].
have PB' : P B' by rewrite /P /= nc' (subset_trans sub0 sB).
rewrite eq_sym eqEcard sB /=; exact: (maxB0 B' PB').
Qed.

(** A non-trivial block-stable class: the edgeless graphs, whose blocks are isolated vertices. *)
Definition x156_edgelessb (G : sgraph) : bool := [forall x : G, forall y : G, ~~ (x -- y)].

Lemma x156_edgeless_block_stable : x156_block_stable x156_edgelessb.
Proof.
split.
  move=> G H /forallP hG i; apply/forallP => x; apply/forallP => y.
  by rewrite -[x](bijK' i) -[y](bijK' i) edge_diso; apply: (forallP (hG _)).
move=> G; split.
  move=> /forallP hG B _; apply/forallP => x; apply/forallP => y.
  by rewrite induced_edge; apply: (forallP (hG _)).
move=> hB; apply/forallP => u; apply/forallP => v; apply/negP => uv.
have [B0 bB0 sub] := x156_block_above (x156_no_cut_pair uv).
have uB : u \in B0 by apply: (subsetP sub); rewrite !inE eqxx.
have vB : v \in B0 by apply: (subsetP sub); rewrite !inE eqxx orbT.
move: (forallP (forallP (hB B0 bB0) (Sub u uB)) (Sub v vB)).
by rewrite induced_edge /= uv.
Qed.

(** The guard on the total weight is load-bearing: the edgeless class has no connected member on
    two or more vertices, so the shared [fg_whp] fails for it at every large n, while
    [x156_whp_where_defined] holds (the source skips those n). *)
Lemma x156_edgeless_no_connected_member (n : nat) (E : {set {set 'I_n.+2}}) :
  ~~ x156_connected_member x156_edgelessb E.
Proof.
apply/negP; rewrite /x156_connected_member /x156_edgelessb => /and3P [_ /forallP el /connectedP con].
have := connectedTE con ord0 ord_max.
case/connectP => -[|z p]; first by move=> _ /(congr1 val).
by case/andP => h _; move: (forallP (el ord0) z); rewrite h.
Qed.

Lemma x156_edgeless_total_weight0 (n : nat) :
  fg_total_weight (fun E : {set {set 'I_n.+2}} => nat_of_bool (x156_connected_member x156_edgelessb E)) = 0.
Proof.
rewrite /fg_total_weight; apply: big1 => E _.
change (nat_of_bool (x156_connected_member x156_edgelessb E) = 0).
by rewrite (negbTE (x156_edgeless_no_connected_member E)).
Qed.

Lemma x156_edgeless_fg_whp_fails (P : forall n : nat, pred {set {set 'I_n}}) :
  ~ @fg_whp (fun n : nat => {set {set 'I_n}})
      (fun n E => nat_of_bool (x156_connected_member x156_edgelessb E)) P.
Proof.
move=> /(_ 1 1 isT isT) [N hN].
case: (hN N.+2 (leqW (leqW (leqnn N)))) => pos _; move: pos.
by first [rewrite x156_edgeless_total_weight0 | rewrite /= x156_edgeless_total_weight0].
Qed.

Lemma x156_edgeless_where_defined (P : forall n : nat, pred {set {set 'I_n}}) :
  @x156_whp_where_defined (fun n : nat => {set {set 'I_n}})
      (fun n E => nat_of_bool (x156_connected_member x156_edgelessb E)) P.
Proof.
move=> a b _ _; exists 2 => -[|[|n]] // _.
by first [rewrite x156_edgeless_total_weight0 | rewrite /= x156_edgeless_total_weight0].
Qed.

(** Where the total weight is eventually positive, [fg_whp] and the guarded form agree; in
    general [fg_whp] implies it. *)
Lemma x156_whp_of_fg_whp (T : nat -> finType) (w : forall n : nat, T n -> nat)
    (P : forall n : nat, pred (T n)) :
  fg_whp w P -> x156_whp_where_defined w P.
Proof.
move=> h a b a0 ab; have ev := h a b a0 ab.
by apply: (eventually_mono ev); move=> n [].
Qed.

(** ** X156 statements *****************************************************)

(** Corpus row: arxiv:1408.4257#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1408.4257__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1408.4257__00.json
    English statement: (McDiarmid and Scott 2014, "Random graphs from a block-stable class",
      arXiv:1408.4257, the conjecture after Theorem 1.2's announcement)
      Let A be a block-stable class of graphs and R_n uniform over the connected graphs of A on
      vertex set [n]. For every function f tending to infinity, with high probability the
      block tree bt(R_n) has diameter at most f(n) sqrt(n): the extra factor sqrt(log n) of
      the bound 5 sqrt(n log n) can be replaced by any function tending to infinity.
    Definitions: [x156_no_cut_vertexb G B] - G[B] is nonempty, connected, and connected after
      deleting any one vertex of B (this file); [x156_blockb G B] - B is a maximal such set, a
      block of G (this file); [x156_block_tree G] - bt(G): vertices and blocks, a vertex
      adjacent to the blocks containing it (this file); [x156_diameter_leb T d] - every two
      nodes in one component are at distance at most d (this file); [x156_block_stable A] - A
      is closed under isomorphism and G is in A iff each block of G is (this file);
      [x156_connected_member A E] - the labelled graph E on 'I_n is a connected member of A
      (this file); [x156_whp_where_defined w P] - with high probability along the n of
      positive total weight, the fg_whp body with the positivity as a hypothesis (this file);
      [iso_closed] (GTBase graph_classes.v); [fg_labelled_sgraph], [fg_valid_labelled_edges],
      [fg_total_weight], [fg_event_weight], [fg_mk_sgraph] (GTBase finite_graph.v);
      [eventually], [sqrt_ceil] (GTBase asymptotics.v); [graph_dist] (GTBase
      graph_metric.v); [connectedb], [induced] (GraphTheory).
    Notes: RE-ENCODED 2026-10-26 (coordination/PROGRAMME.md A1; record
      meta/STATEMENT_IMPROVEMENTS.md; the row is frozen by no migration family; routing by
      Lancelot, design agreed 12:09:55Z; reviewer Marcol, 12:09:13Z).  The source is the
      e-print (sha256 bbace953..., blockclassesrevised-2016-01-13.tex sha256 51349cf0...):
      blocks l.151, block-stable classes closed under isomorphism l.152-154, bt(G) l.174, A_n,
      R_n and "only integers n such that A_n is non-empty" l.180, whp l.185, diameter
      l.289-290, the conjecture l.302-304 (Theorem 1.2, l.306-318, is the weakly block-stable
      form).  The earlier body had four defects: f merely unbounded instead of tending to
      infinity, which made it false (faithfulness audit 2026-07-17); any observed family of
      graphs on n vertices instead of a block-stable class; an existential block-tree
      certificate instead of bt(G) (every nonempty graph has a certificate of diameter at most
      2, a forest one of diameter 0); and fg_whp, which needs a positive total weight at every
      large n.  [x156_blockb] is the standard maximal connected subgraph without a cut vertex,
      equal to l.151's three cases: a no-cut set of three or more vertices is 2-connected;
      {u, v} with u -- v is maximal iff uv lies on no cycle (a cycle's vertex set induces a
      2-connected graph), i.e. iff uv is a bridge; {v} is maximal iff v is isolated.  Classes
      are Boolean predicates: R_n counts the members on [n], which needs a decidable
      membership, and classically every class of graphs is one.  f is natural and the bound
      f n * sqrt_ceil n; this is equivalent to the real form: given a real g tending to
      infinity, f = floor(g/2) tends to infinity and f(n) ceil(sqrt n) <= 2 f(n) sqrt n <=
      g(n) sqrt n for n >= 1; given a natural f, take g = f, as f sqrt n <= f ceil(sqrt n);
      the constant 5 of l.302 is absorbed into f.  The shared [fg_whp] is not used: it
      demands a positive total weight at every large n, which makes the statement false for a
      block-stable class with members on only some n (the edgeless class,
      [x156_edgeless_fg_whp_fails]; the class whose blocks are triangles, odd n only), where
      the source restricts to the n with A_n non-empty; [x156_whp_where_defined] is fg_whp's
      body with that positivity as a guard ([x156_whp_of_fg_whp],
      [x156_edgeless_where_defined]).  The x156_ block and block-tree helpers are
      library-migration candidates.  Sanity: [x156_blockb_K1], [x156_blockb_K2],
      [x156_K2_vertex_not_block], [x156_K2_block_tree_not_diameter0] (the bound is not
      vacuous), [x156_all_graphs_block_stable] and [x156_edgeless_block_stable] (the class
      hypothesis is met by a non-trivial class).  The row's upstream status is solved
      (Addario-Berry and Donderwinkel, arXiv:2201.11773, Theorem 25, per the pinned review);
      no formal resolution is recorded here. *)
Definition block_tree_diameter_bound_improvement_statement : Prop :=
  forall (A : sgraph -> bool) (f : nat -> nat),
    x156_block_stable A ->
    (forall M : nat, eventually (fun n => M <= f n)) ->
    @x156_whp_where_defined (fun n : nat => {set {set 'I_n}})
      (fun n E => nat_of_bool (x156_connected_member A E))
      (fun n E => x156_diameter_leb (x156_block_tree (fg_labelled_sgraph E)) (f n * sqrt_ceil n)).

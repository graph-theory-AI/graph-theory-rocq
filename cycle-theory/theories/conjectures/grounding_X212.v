(** * Cycle.conjectures.grounding_X212 — grounding lemmas for wave X212

    [Qed]-closed, axiom-free sanity results for the eight Bondy–Murty rows of
    [Cycle.conjectures.X212] and for the local [x212_*] vocabulary they
    introduce.  For every row we record

      - a NON-VACUITY lemma: the hypothesis class is inhabited by a concrete
        graph (and, where it is cheap, the conclusion is exhibited on it), so
        the statement is not a disguised [True] over an empty domain;
      - a GUARD-HAS-TEETH lemma: the obvious degenerate witness is rejected by
        the definitions (the empty cover, the empty transversal, the zero
        colouring, a two-element "cycle", ...);
      - for [bm-062] (Kotzig), the SETTLED small case the definitions already
        decide: no graph on at most [k] vertices can have a unique path of
        length [k] between every two distinct vertices.

    Witness models: ['K_1] / ['K_2] / ['K_3] on the simple-graph side; the
    one-vertex multigraph [U] of [grounding_U6] on the multigraph side. *)

From GraphTheory Require Import mgraph.
From GTBase Require Import base.
From Cycle.foundations Require Import connectivity.
From Cycle.conjectures Require Import U6 grounding_U6 X212.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Shared counting helper *)

(** A duplicate-free vertex list is no longer than the vertex set. *)
Lemma x212_uniq_size (G : sgraph) (s : seq G) : uniq s -> size s <= #|G|.
Proof.
move=> u; rewrite cardT; apply: uniq_leq_size => // x _.
by rewrite mem_enum.
Qed.

(** A cycle needs more than two vertices, so a graph with a cycle has more than
    two vertices. *)
Lemma x212_cycle_card (G : sgraph) (c : seq G) : x212_cycle c -> 2 < #|G|.
Proof.
case/andP => /andP[_ uc] sc.
by apply: leq_trans sc _; exact: x212_uniq_size.
Qed.

(** ** bm-011 — Barát–Thomassen *)

(** NON-VACUITY: the empty family decomposes the edge set of the one-vertex
    graph into copies of any tree (the conclusion is inhabited). *)
Lemma x212_decomposition_K1 (T : sgraph) :
  x212_decomposition_into_copies (G := 'K_1) T [::].
Proof. by split => [A|e] //; rewrite /= sg_edge_set_K1 inE. Qed.

(** GUARD HAS TEETH: a decomposition into copies never uses a non-edge. *)
Lemma x212_decomposition_edges (G T : sgraph) (D : seq {set {set G}})
    (e : {set G}) (A : {set {set G}}) :
  x212_decomposition_into_copies T D -> e \notin E(G) -> A \in D -> e \notin A.
Proof.
case=> _ cnt /negbTE eE AD; apply/negP => eA.
have : 0 < count (fun B : {set {set G}} => e \in B) D.
  by rewrite -has_count; apply/hasP; exists A.
by rewrite cnt eE.
Qed.

(** ** bm-013 — Bondy's small cycle double cover *)

(** NON-VACUITY: the one-vertex multigraph satisfies every hypothesis of the row
    and its conclusion, with the empty cover. *)
Lemma x212_small_cdc_unit :
  (0 < #|U|)%N /\ simple_mgraph U /\ bridgeless U /\
  exists L : seq {set edge U}, cdc L /\ (size L <= #|U| - 1)%N.
Proof.
split; first by rewrite card_unit.
split; first exact: simple_mgraph_unit.
split; first exact: bridgeless_unit.
exists [::]; split; last by rewrite card_unit.
by split; [move=> C | move=> e; case: e].
Qed.

(** GUARD HAS TEETH: the empty cover is not a cycle double cover of a graph that
    has an edge. *)
Lemma x212_cdc_nil_teeth (G : mgraph) : (0 < #|edge G|)%N -> ~ cdc (G := G) [::].
Proof.
move=> /card_gt0P[e _] [_ cnt].
by have := cnt e.
Qed.

(** ** bm-016 — linear arboricity *)

(** NON-VACUITY: the hypothesis class is inhabited — the one-vertex simple graph
    is nonempty and 0-regular. *)
Lemma x212_regular_K1 : (0 < #|'K_1|) /\ regular 'K_1 0.
Proof.
split; first by rewrite card_ord.
move=> v; suff -> : N(v) = set0 by rewrite cards0.
by apply/setP => w; rewrite !inE [v]ord1 [w]ord1 sg_irrefl.
Qed.

(** GUARD HAS TEETH: no graph has a linear-forest colouring with zero colours,
    because the colouring is a total map on the (always inhabited) type of
    2-element vertex sets.  Hence the encoded linear arboricity is at least 1
    and the equality asserted by the row is never satisfied by a "zero". *)
Lemma x212_linear_arboricity_at_most0 (G : sgraph) :
  ~ x212_linear_arboricity_at_most G 0.
Proof. by case=> col _; case: (col set0) => m; rewrite ltn0. Qed.

Lemma x212_linear_arboricity_gt0 (G : sgraph) (q : nat) :
  x212_linear_arboricity G q -> 0 < q.
Proof.
case=> ha _; case: q ha => [|q] //.
by move/x212_linear_arboricity_at_most0.
Qed.

(** ** bm-026 — orientable five cycle double cover *)

(** NON-VACUITY: the one-vertex multigraph is 2-edge-connected and carries an
    orientable double cover by five even subgraphs (all of them empty). *)
Lemma x212_orientable_5_unit :
  two_edge_connected U /\ x212_orientable_5_even_double_cover U.
Proof.
split; first by split; [exact: mconnected_unit | exact: bridgeless_unit].
exists (fun _ => set0), (fun _ _ => true); split.
- by move=> i; exact: even_subgraph_set0.
- by move=> i v; congr (#|_|); apply/setP => e; case: e.
- by move=> e; case: e.
- by move=> e; case: e.
Qed.

(** A GENUINELY NONEMPTY witness for the 2-edge-connectedness hypothesis: the
    two-vertex multigraph [G2p] of [grounding_U6], with two parallel edges, is
    connected and bridgeless.  Since [is_bridge] is now stated with the
    UNDIRECTED [uwalk] (see [Cycle.foundations.connectivity]), the reference
    orientation of the two edges is irrelevant: the digon [Gd], whose two edges
    are ANTIPARALLEL, is bridgeless for exactly the same reason.  The sharper
    witnesses -- a simple bridgeless triangle, and a graph with a genuine cut
    edge -- are in the section [The repaired bridge / simplicity notions]
    below. *)
Lemma x212_mconnected_G2p : mconnected G2p.
Proof.
move=> x y; case: x => -[]; case: y => -[].
- by exists [::].
- by exists [:: None].
- by exists [:: None].
- by exists [::].
Qed.

Lemma x212_bridgeless_G2p : bridgeless G2p.
Proof.
move=> e; case: e => [x|] sep.
- move: sep; case: x => [e0|] sep.
  + by move: sep; case: e0 => -[].
  + have [f fE fw] := sep [:: None] isT.
    by move: fE fw; rewrite !inE => /eqP ->.
- have [f fE fw] := sep [:: Some None] isT.
  by move: fE fw; rewrite !inE => /eqP ->.
Qed.

Lemma x212_two_edge_connected_G2p : two_edge_connected G2p.
Proof. by split; [exact: x212_mconnected_G2p | exact: x212_bridgeless_G2p]. Qed.

(** ... and it really has edges, so the hypothesis class of [bm-026] (and of the
    [bridgeless] hypothesis of [bm-013]) is not the edgeless graphs only. *)
Lemma x212_card_edge_G2p : #|edge G2p| = 2.
Proof. by rewrite /G2p /G1 /G0 !card_option card_sum !card_void. Qed.

(** GUARD HAS TEETH: five empty subgraphs do not cover a graph that has an
    edge. *)
Lemma x212_orientable_5_teeth (G : mgraph) :
  (0 < #|edge G|)%N ->
  ~ (forall e : edge G, #|[set i : 'I_5 | e \in (@set0 (edge G))]| = 2).
Proof.
move=> /card_gt0P[e _] cov; move: (cov e).
suff -> : [set i : 'I_5 | e \in (@set0 (edge G))] = set0 by rewrite cards0.
by apply/setP => i; rewrite !inE.
Qed.

(** ** The repaired bridge / simplicity notions behave as intended

    These lemmas pin down the two foundation repairs of 2026-09-23 (see
    meta/X211-X229_faithfulness_audit.md, blockers A and B of the X212 section):

      - [is_bridge] now quantifies over base's UNDIRECTED [uwalk], so "bridge"
        means CUT EDGE.  A cyclically oriented triangle -- the smallest graph the
        previous, directed reading wrongly excluded -- is bridgeless ([Tri]
        below), while a graph with a genuine cut edge is not ([G1]).
      - [U6.simple_mgraph] now bounds the UNDIRECTED multiplicity
        [#|edges x y| + #|edges y x|], so a doubled edge carried by two
        ANTIPARALLEL arcs (the digon [Gd]) is correctly rejected, while a
        genuinely simple graph (the triangle) is accepted. *)

(** *** The cyclically oriented triangle [Tri]

    Three vertices [option bool] cycled by [x212_rot]; one arc per vertex, the
    arc named [v] running from [v] to [x212_rot v].  Every arc therefore has the
    SAME reference orientation around the cycle -- the configuration on which the
    old directed [bridgeless] failed. *)

Definition x212_triV := option bool.

Definition x212_rot (v : x212_triV) : x212_triV :=
  match v with
  | None => Some false | Some false => Some true | Some true => None
  end.

Definition x212_tri_ep (b : bool) (e : x212_triV) : x212_triV :=
  if b then x212_rot e else e.

Definition Tri : mgraph :=
  @Graph unit unit x212_triV x212_triV x212_tri_ep (fun _ => tt) (fun _ => tt).

Lemma x212_rot3 (v : x212_triV) : x212_rot (x212_rot (x212_rot v)) = v.
Proof. by case: v => [[]|]. Qed.

Lemma x212_rot_neq (v : x212_triV) : x212_rot v != v.
Proof. by case: v => [[]|]. Qed.

Lemma x212_rot2_neq (v : x212_triV) : x212_rot (x212_rot v) != v.
Proof. by case: v => [[]|]. Qed.

Lemma x212_src_Tri (e : edge Tri) : source e = e. Proof. by []. Qed.
Lemma x212_tgt_Tri (e : edge Tri) : target e = x212_rot e. Proof. by []. Qed.

Lemma x212_card_Tri : #|Tri| = 3.
Proof. by rewrite /= card_option card_bool. Qed.

Lemma x212_card_edge_Tri : #|edge Tri| = 3.
Proof. by rewrite /= card_option card_bool. Qed.

Lemma x212_loopless_Tri : loopless Tri.
Proof. by move=> e; rewrite x212_src_Tri x212_tgt_Tri eq_sym x212_rot_neq. Qed.

(** The detour around the triangle: the two other arcs, each traversed AGAINST
    its reference orientation. *)
Lemma x212_uwalk_Tri (e : edge Tri) :
  uwalk (source e) (target e) [:: x212_rot (x212_rot e); x212_rot e].
Proof.
apply: uwalk_cons_rev; first by rewrite x212_tgt_Tri x212_rot3 x212_src_Tri.
by apply: uwalk_one_rev; rewrite ?x212_tgt_Tri ?x212_src_Tri.
Qed.

(** THE REPAIR, POSITIVE SIDE: the cyclically oriented triangle IS bridgeless.
    (Under the previous, DIRECTED [is_bridge] it was not: the only arc leaving a
    vertex is the one to be avoided.) *)
Lemma x212_bridgeless_Tri : bridgeless Tri.
Proof.
move=> e; apply: (not_bridge_detour (x212_uwalk_Tri e)).
rewrite mem_seq2 negb_or eq_sym x212_rot2_neq /=.
by rewrite eq_sym x212_rot_neq.
Qed.

Lemma x212_mconnected_Tri : mconnected Tri.
Proof.
move=> x y; case: x => [[]|]; case: y => [[]|].
- by exists [::].
- by exists [:: (Some false : edge Tri)].
- by exists [:: (Some true : edge Tri)].
- by exists [:: (Some false : edge Tri)].
- by exists [::].
- by exists [:: (None : edge Tri)].
- by exists [:: (Some true : edge Tri)].
- by exists [:: (None : edge Tri)].
- by exists [::].
Qed.

Lemma x212_two_edge_connected_Tri : two_edge_connected Tri.
Proof. by split; [exact: x212_mconnected_Tri | exact: x212_bridgeless_Tri]. Qed.

(** ... and it is genuinely SIMPLE for the repaired [simple_mgraph]: between two
    vertices there is at most one arc, counted in BOTH directions. *)
Lemma x212_edges_Tri (x y : Tri) :
  edges x y = if x212_rot x == y then [set (x : edge Tri)] else set0.
Proof.
apply/setP => e; rewrite inE x212_src_Tri x212_tgt_Tri.
case E: (e == x); last by rewrite andFb; case: ifPn => _; rewrite inE ?E.
move/eqP: E => ->; case: ifPn => _.
- by rewrite inE eqxx.
- by rewrite inE.
Qed.

Lemma x212_card_edges_Tri (x y : Tri) :
  #|edges x y| = nat_of_bool (x212_rot x == y).
Proof. by rewrite x212_edges_Tri; case: ifPn => _; rewrite ?cards1 ?cards0. Qed.

Lemma x212_simple_Tri : simple_mgraph Tri.
Proof.
split; first exact: x212_loopless_Tri.
move=> x y; rewrite !x212_card_edges_Tri.
case E: (x212_rot x == y); last by case: (x212_rot y == x).
by move/eqP: E => <-; rewrite (negbTE (x212_rot2_neq x)).
Qed.

(** NON-VACUITY, sharpened: the hypothesis class of [bm-013] (simple +
    bridgeless) and of [bm-026] (2-edge-connected) contains a graph with three
    vertices and three edges, not merely the degenerate corner. *)
Lemma x212_small_cdc_hypotheses_Tri :
  (0 < #|Tri|)%N /\ simple_mgraph Tri /\ bridgeless Tri /\ (0 < #|edge Tri|)%N.
Proof.
split; first by rewrite x212_card_Tri.
split; first exact: x212_simple_Tri.
by split; [exact: x212_bridgeless_Tri | rewrite x212_card_edge_Tri].
Qed.

(** *** A genuine CUT EDGE is a bridge

    [G1] (of [grounding_U6]) is two vertices joined by a single edge; deleting
    that edge separates them, so it is a bridge and [G1] is NOT bridgeless. *)
Lemma x212_is_bridge_G1 (e : edge G1) : is_bridge e.
Proof.
have eN : e = None by case: e => [[[]|[]]|].
apply/is_bridgeP; case=> [|f w]; first by rewrite eN.
by case: f => [[[]|[]]|] _; rewrite eN inE eqxx.
Qed.

Lemma x212_not_bridgeless_G1 : ~ bridgeless G1.
Proof. by move=> bl; apply: (bl None); exact: x212_is_bridge_G1. Qed.

(** *** A DOUBLED edge is not simple

    The digon [Gd] (of [grounding_U6]) carries its two arcs between the same two
    vertices in OPPOSITE reference directions.  The previous [simple_mgraph],
    which bounded the directed count [#|edges x y|] alone, accepted it; the
    repaired one rejects it.  (This is the loophole that made
    [small_cycle_double_cover_statement] refutable:
    meta/probe_hints/small_cycle_double_cover_statement.v.) *)
Lemma x212_not_simple_Gd : ~ simple_mgraph Gd.
Proof.
case=> _ /(_ (inl tt : Gd) (inr tt : Gd)) le.
have h1 : (0 < #|edges (inl tt : Gd) (inr tt : Gd)|)%N.
  by apply/card_gt0P; exists (Some None); rewrite inE /= !eqxx.
have h2 : (0 < #|edges (inr tt : Gd) (inl tt : Gd)|)%N.
  by apply/card_gt0P; exists None; rewrite inE /= !eqxx.
by have := leq_trans (leq_add h1 h2) le.
Qed.

(** *** The LOOP GRAPH [Lp] and the loop-degree repair (2026-09-23)

    [Lp] is the one-vertex, one-loop multigraph -- the SAME construction as
    [grounding_U6.Gloop] and as the [Lp] of the (now stale) refutation hints
    meta/probe_hints/orientable_five_cycle_double_cover_statement.v and
    meta/probe_hints/cycle_double_cover_statement.v, so the three agree
    definitionally.

    Before the degree repair, [connectivity.subdeg] counted the edges INCIDENT
    to a vertex, so the loop had degree 1: [U6.even_subgraph [set: edge Lp]]
    and [is_circuit [set: edge Lp]] both FAILED, while [Lp] is connected and
    bridgeless (a loop is never a cut edge, [connectivity.loop_not_bridge]),
    hence [two_edge_connected].  Its only edge had to lie in exactly two members
    of the cover and no member containing it could be an even subgraph, so
    [orientable_five_cycle_double_cover_statement] (bm-026) and the committed
    [U6.cycle_double_cover_statement] were axiom-free REFUTABLE on this graph.

    [subdeg] now counts ARC ENDS ([connectivity.subdeg], [connectivity.subdegE],
    [connectivity.subdeg_loopless]), so the loop has the textbook degree 2 and
    [Lp] is a genuine instance of both rows -- with the conclusion EXHIBITED
    below: [x212_orientable_5_Lp] is a five-member orientable even double cover
    of [Lp], and [x212_cdc_Lp] a cycle double cover of it. *)

Definition Lp : mgraph := Gloop.

Lemma x212_card_Lp : #|Lp| = 1.
Proof. by rewrite card_unit. Qed.

Lemma x212_card_edge_Lp : #|edge Lp| = 1.
Proof. exact: card_edge_Gloop. Qed.

(** THE POINT OF THE REPAIR: a loop contributes 2, not 1. *)
Lemma x212_mdeg_Lp (v : Lp) : mdeg v = 2.
Proof. exact: mdeg_Gloop. Qed.

Lemma x212_subdeg_Lp (v : Lp) : subdeg [set: edge Lp] v = 2.
Proof. exact: subdeg_Gloop. Qed.

(** ... hence the single loop is an even subgraph, a connected 2-regular edge
    set, and a circuit. *)
Lemma x212_even_subgraph_Lp : even_subgraph (G := Lp) [set: edge Lp].
Proof. exact: even_subgraph_Gloop. Qed.

Lemma x212_subgraph_kregular_Lp :
  subgraph_kregular (G := Lp) [set: edge Lp] 2.
Proof. exact: subgraph_kregular_Gloop. Qed.

Lemma x212_subgraph_connected_Lp :
  subgraph_connected (G := Lp) [set: edge Lp].
Proof. exact: subgraph_connected_Gloop. Qed.

Lemma x212_is_circuit_Lp : is_circuit (G := Lp) [set: edge Lp].
Proof. exact: is_circuit_Gloop. Qed.

(** NON-VACUITY: [Lp] satisfies every hypothesis of [bm-026] (and of the
    [U6.cycle_double_cover_statement] row), so the loop graph is a genuine
    instance of both. *)
Lemma x212_two_edge_connected_Lp : two_edge_connected Lp.
Proof. exact: two_edge_connected_Gloop. Qed.

Lemma x212_orientable_5_hypotheses_Lp :
  (0 < #|Lp|)%N /\ two_edge_connected Lp /\ (0 < #|edge Lp|)%N.
Proof.
split; first by rewrite x212_card_Lp.
by split; [exact: x212_two_edge_connected_Lp | rewrite x212_card_edge_Lp].
Qed.

(** The conclusion of [U6.cycle_double_cover_statement] on [Lp]: cover the loop
    twice. *)
Lemma x212_cdc_Lp : cdc (G := Lp) [:: [set: edge Lp]; [set: edge Lp]].
Proof. exact: cdc_Gloop. Qed.

(** The conclusion of [bm-026] on [Lp]: put the loop in members [ord0] and
    [ord_max], oriented oppositely there, and leave the other three members
    empty.  Every member is an even subgraph (the full set has degree 2, the
    empty set degree 0); every member is balanced because the loop's two ends
    are the same vertex, so it is its own tail and its own head. *)
Definition x212_Lp_cover (i : 'I_5) : {set edge Lp} :=
  if (i == ord0) || (i == ord_max) then [set: edge Lp] else set0.

Definition x212_Lp_dir (i : 'I_5) (e : edge Lp) : bool := (i == ord0).

Lemma x212_Lp_coverE (i : 'I_5) (e : edge Lp) :
  (e \in x212_Lp_cover i) = (i == ord0) || (i == ord_max).
Proof.
by rewrite /x212_Lp_cover; case: ifP => _; rewrite ?in_setT ?in_set0.
Qed.

Lemma x212_Lp_even (i : 'I_5) : even_subgraph (x212_Lp_cover i).
Proof.
rewrite /x212_Lp_cover; case: ifP => _;
  by [exact: x212_even_subgraph_Lp | exact: even_subgraph_set0].
Qed.

Lemma x212_Lp_vertex (v : Lp) : v = tt.
Proof. by case: v. Qed.

(** Balanced: [Lp] has a single vertex, so -- whichever way [x212_Lp_dir]
    orients the loop -- that vertex is both the tail and the head of every
    [Lp]-edge, and the two sets counted by [x212_balanced] coincide.  (On the
    one-element vertex type the two membership conditions reduce to the same
    boolean, which is what [rewrite !inE] exploits; [x212_Lp_vertex] and
    [src_Gloop] / [tgt_Gloop] are the human-readable form of the same fact.) *)
Lemma x212_Lp_balanced (i : 'I_5) :
  x212_balanced (x212_Lp_cover i) (x212_Lp_dir i).
Proof. by move=> v; congr (#|_|); apply/setP => e; rewrite !inE. Qed.

Lemma x212_Lp_cover_card (e : edge Lp) :
  #|[set i : 'I_5 | e \in x212_Lp_cover i]| = 2.
Proof.
have -> : [set i : 'I_5 | e \in x212_Lp_cover i] = [set ord0; ord_max].
  by apply/setP => i; rewrite !inE x212_Lp_coverE.
by rewrite cardsU1 cards1 !inE -val_eqE.
Qed.

Lemma x212_Lp_opposite (e : edge Lp) (i j : 'I_5) :
  i != j -> e \in x212_Lp_cover i -> e \in x212_Lp_cover j ->
  x212_Lp_dir i e != x212_Lp_dir j e.
Proof.
rewrite !x212_Lp_coverE /x212_Lp_dir => ij hi hj.
apply/eqP => dij; case: (boolP (i == ord0)) => i0.
- have j0 : j = ord0 by apply/eqP; rewrite -dij i0.
  by move: ij; rewrite (eqP i0) j0 eqxx.
- have j0 : (j == ord0) = false by rewrite -dij (negbTE i0).
  move: hi hj; rewrite (negbTE i0) j0 /= => /eqP ei /eqP ej.
  by move: ij; rewrite ei ej eqxx.
Qed.

(** THE CONJECTURE HOLDS ON THE LOOP GRAPH: bm-026's conclusion, exhibited. *)
Lemma x212_orientable_5_Lp : x212_orientable_5_even_double_cover Lp.
Proof.
exists x212_Lp_cover, x212_Lp_dir; split.
- exact: x212_Lp_even.
- exact: x212_Lp_balanced.
- exact: x212_Lp_cover_card.
- exact: x212_Lp_opposite.
Qed.

(** The (5,2)-cycle cover row of U6 ([U6.m_n_cycle_covers_statement], guarded
    only by [bridgeless]) was refutable on [Lp] for exactly the same reason as
    bm-026 -- five EVEN SUBGRAPHS, two of them containing the loop.  The same
    two-member trick realises it. *)
Lemma x212_m_n_cover_Lp :
  exists L : seq {set edge Lp},
    [/\ size L = 5,
        (forall C, C \in L -> even_subgraph C)
      & (forall e : edge Lp, count (fun C : {set edge Lp} => e \in C) L = 2)].
Proof.
exists [:: [set: edge Lp]; [set: edge Lp]; set0; set0; set0]; split => //.
- move=> C; rewrite !inE => /orP[|/orP[|/orP[|/orP[|]]]] /eqP ->;
    by [exact: x212_even_subgraph_Lp | exact: even_subgraph_set0].
- by move=> e; rewrite /= !in_setT !in_set0.
Qed.

(** ... so the loop graph, which used to REFUTE the row, now realises it. *)
Lemma x212_orientable_5_loop_instance :
  (0 < #|Lp|)%N /\ two_edge_connected Lp /\
  x212_orientable_5_even_double_cover Lp.
Proof.
split; first by rewrite x212_card_Lp.
by split; [exact: x212_two_edge_connected_Lp | exact: x212_orientable_5_Lp].
Qed.

(** ** bm-062 — Kotzig's unique k-path conjecture *)

(** NON-VACUITY: every edge is a path of length 1 between its ends. *)
Lemma x212_path_len1 (G : sgraph) (x y : G) : x -- y -> x212_path_len 1 x y [:: y].
Proof.
move=> xy; apply/and4P; split; [by rewrite /= xy | by [] | | by []].
by rewrite cons_uniq mem_seq1 /= andbT sg_edgeNeq.
Qed.

(** GUARD HAS TEETH: a path of length [k] uses [k+1] distinct vertices, so it
    only exists in graphs with more than [k] vertices. *)
Lemma x212_path_len_card (G : sgraph) (k : nat) (x y : G) (p : seq G) :
  x212_path_len k x y p -> k < #|G|.
Proof.
case/and4P => _ /eqP sp u _.
by have := x212_uniq_size u; rewrite /= sp.
Qed.

(** SETTLED CASE: Kotzig's conjecture holds for every graph on at most [k]
    vertices — such a graph has no path of length [k] at all, so it cannot have
    a unique one between two distinct vertices. *)
Lemma kotzig_unique_k_path_small (k : nat) (G : sgraph) :
  1 < #|G| -> #|G| <= k ->
  ~ (forall x y : G, x != y -> exists! p : seq G, x212_path_len k x y p).
Proof.
move=> /card_gt1P[x [y [_ _ xy]]] le h.
have [p [pk _]] := h x y xy.
by have := x212_path_len_card pk; rewrite ltnNge le.
Qed.

(** ** bm-064 — Smith's conjecture on longest cycles *)

Definition x212_c3 : seq 'K_3 :=
  [:: (@Ordinal 3 0 isT : 'K_3); (@Ordinal 3 1 isT : 'K_3);
      (@Ordinal 3 2 isT : 'K_3)].

(** NON-VACUITY: the triangle is a cycle, and a longest one. *)
Lemma x212_cycle_c3 : x212_cycle x212_c3.
Proof. by rewrite /x212_cycle /x212_c3 /ucycleb /=. Qed.

Lemma x212_longest_cycle_c3 : x212_longest_cycle x212_c3.
Proof.
split; first exact: x212_cycle_c3.
move=> c' /andP[/andP[_ uc'] _].
by have := x212_uniq_size uc'; rewrite card_ord.
Qed.

(** GUARD HAS TEETH: a two-element [ucycle] — an edge traversed back and forth —
    is not a cycle, which is the [n >= 3] convention of [GTBase.common]. *)
Lemma x212_cycle_not2 (G : sgraph) (x y : G) : ~~ x212_cycle [:: x; y].
Proof. by rewrite /x212_cycle andbF. Qed.

(** ** bm-065 — Bondy's linear-length cycle conjecture *)

(** NON-VACUITY: a graph on fewer than three vertices contains no cycle, hence is
    cyclically [k]-edge-connected for every [k] — the hypothesis class of the row
    is inhabited. *)
Lemma x212_no_cycle_within_K1 (S : {set 'K_1}) : ~ x212_cycle_within S.
Proof.
case=> c [/x212_cycle_card]; rewrite card_ord.
by [].
Qed.

Lemma x212_cyclically_edge_connected_K1 (k : nat) :
  x212_cyclically_edge_connected 'K_1 k.
Proof. by move=> S /x212_no_cycle_within_K1. Qed.

(** GUARD HAS TEETH: the conclusion really asks for a cycle — with positive
    constants, a linear-length bound on a nonempty graph forces a nonempty
    cycle. *)
Lemma x212_linear_length_teeth (G : sgraph) (p q : nat) (c : seq G) :
  0 < p -> 0 < #|G| -> p * #|G| <= q * size c -> 0 < size c.
Proof.
move=> p0 G0 le; rewrite lt0n; apply/negP => /eqP s0.
move: le; rewrite s0 muln0 leqn0 muln_eq0 => /orP[] /eqP z.
- by move: p0; rewrite z.
- by move: G0; rewrite z.
Qed.

(** The trivial bipartition imposes nothing: the cut of the empty vertex set is
    empty, and the empty set contains no cycle. *)
Lemma x212_edge_cut0 (G : sgraph) : x212_edge_cut (G := G) set0 = set0.
Proof.
apply/setP => e; rewrite !inE setI0 cards0 andbF.
by [].
Qed.

(** ** bm-066 — Birmelé's conjecture on long cycles *)

(** NON-VACUITY: on the one-vertex graph the hypothesis holds vacuously and the
    empty set is a transversal, so the row's implication is realised. *)
Lemma x212_birmele_K1 (k : nat) :
  exists S : {set 'K_1},
    #|S| <= k /\
    (forall c : seq ('K_1), x212_cycle c -> k <= size c ->
       exists x : ('K_1), (x \in S) && (x \in c)).
Proof.
exists set0; split; first by rewrite cards0.
move=> c /x212_cycle_card; rewrite card_ord.
by [].
Qed.

(** GUARD HAS TEETH: the empty set is a transversal of the long cycles only when
    there is no long cycle. *)
Lemma x212_transversal0_teeth (G : sgraph) (k : nat) (c : seq G) :
  (forall c' : seq G, x212_cycle c' -> k <= size c' ->
     exists x : G, (x \in (@set0 G)) && (x \in c')) ->
  x212_cycle c -> k <= size c -> False.
Proof. by move=> h /h{}h /h[x]; rewrite inE. Qed.

(** ** Axiom audit ********************************************************* *)

Print Assumptions barat_thomassen_tree_decomposition_statement.
Print Assumptions small_cycle_double_cover_statement.
Print Assumptions linear_arboricity_regular_statement.
Print Assumptions orientable_five_cycle_double_cover_statement.
Print Assumptions kotzig_unique_k_path_statement.
Print Assumptions smith_two_longest_cycles_statement.
Print Assumptions bondy_linear_cycle_cubic_statement.
Print Assumptions birmele_long_cycle_transversal_statement.
Print Assumptions x212_decomposition_K1.
Print Assumptions x212_decomposition_edges.
Print Assumptions x212_small_cdc_unit.
Print Assumptions x212_cdc_nil_teeth.
Print Assumptions x212_regular_K1.
Print Assumptions x212_linear_arboricity_at_most0.
Print Assumptions x212_linear_arboricity_gt0.
Print Assumptions x212_mconnected_G2p.
Print Assumptions x212_bridgeless_G2p.
Print Assumptions x212_two_edge_connected_G2p.
Print Assumptions x212_card_edge_G2p.
Print Assumptions x212_orientable_5_unit.
Print Assumptions x212_orientable_5_teeth.
Print Assumptions x212_rot3.
Print Assumptions x212_loopless_Tri.
Print Assumptions x212_uwalk_Tri.
Print Assumptions x212_bridgeless_Tri.
Print Assumptions x212_mconnected_Tri.
Print Assumptions x212_two_edge_connected_Tri.
Print Assumptions x212_edges_Tri.
Print Assumptions x212_card_edges_Tri.
Print Assumptions x212_simple_Tri.
Print Assumptions x212_small_cdc_hypotheses_Tri.
Print Assumptions x212_is_bridge_G1.
Print Assumptions x212_not_bridgeless_G1.
Print Assumptions x212_not_simple_Gd.
Print Assumptions x212_card_Lp.
Print Assumptions x212_card_edge_Lp.
Print Assumptions x212_mdeg_Lp.
Print Assumptions x212_subdeg_Lp.
Print Assumptions x212_even_subgraph_Lp.
Print Assumptions x212_subgraph_kregular_Lp.
Print Assumptions x212_subgraph_connected_Lp.
Print Assumptions x212_is_circuit_Lp.
Print Assumptions x212_two_edge_connected_Lp.
Print Assumptions x212_orientable_5_hypotheses_Lp.
Print Assumptions x212_cdc_Lp.
Print Assumptions x212_Lp_coverE.
Print Assumptions x212_Lp_even.
Print Assumptions x212_Lp_vertex.
Print Assumptions x212_Lp_balanced.
Print Assumptions x212_Lp_cover_card.
Print Assumptions x212_Lp_opposite.
Print Assumptions x212_orientable_5_Lp.
Print Assumptions x212_m_n_cover_Lp.
Print Assumptions x212_orientable_5_loop_instance.
Print Assumptions x212_path_len1.
Print Assumptions x212_path_len_card.
Print Assumptions kotzig_unique_k_path_small.
Print Assumptions x212_cycle_c3.
Print Assumptions x212_longest_cycle_c3.
Print Assumptions x212_cycle_not2.
Print Assumptions x212_cyclically_edge_connected_K1.
Print Assumptions x212_linear_length_teeth.
Print Assumptions x212_edge_cut0.
Print Assumptions x212_birmele_K1.
Print Assumptions x212_transversal0_teeth.

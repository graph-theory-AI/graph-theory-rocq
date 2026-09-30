(** * Chromatic.conjectures.grounding_U5 — grounding lemmas for milestone U5.

    SIMPLE, Qed-closed sanity results validating the NEW primitives introduced
    in [U5.v] (edge/total-colouring vocabulary).  For each new definition we
    record a SATISFIABLE witness and at least one textbook identity.  These are
    statement-validation lemmas, NOT the (open/partial) conjectures themselves.

    Witness objects:
      - [dipole3]: the 3-dipole D_3 (two vertices joined by three parallel
        edges).  It is the minimal CUBIC multigraph and the minimal Seymour
        3-graph; vertices are [bool] (so "every vertex is an endpoint of every
        edge" needs no ordinal case-split), edges are ['I_3].
      - [unit_graph tt]: the one-vertex edgeless multigraph (edge type [void]).
      - ['K_1]: the one-vertex simple graph (no edges) for the EDGE-colouring
        rows, where every adjacency hypothesis is vacuous.
      - [sts3]: the Steiner triple system on 3 points with the single block
        {0,1,2}; [hg_one d]: the one-edge d-uniform hypergraph. *)

From GTBase Require Import base.
From GraphTheory Require Import mgraph.
From Chromatic.foundations Require Import chi_bounding.
From Chromatic.conjectures Require Import U5.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ============================================================================
    Witness multigraph: the 3-dipole D_3 (two vertices, three parallel edges).
    ========================================================================== *)

Definition dipole3 : mgraph :=
  @Graph unit unit bool 'I_3 (fun b _ => b) (fun _ => tt) (fun _ => tt).

(** Every vertex is incident to every edge: [edges_at v] is the whole edge set.
    (For each [b]-endpoint, [endpoint b e = b], so taking [b := v] witnesses the
    incidence.) *)
Lemma edges_at_dipole3 (v : dipole3) : edges_at v = [set: edge dipole3].
Proof.
apply/setP => e; rewrite !inE.
by apply/existsP; exists v; rewrite eqxx.
Qed.

(** ** [regular_m] / [cubic] — witness: D_3 is 3-regular, hence cubic. *)
Lemma cubic_dipole3 : cubic dipole3.
Proof. by move=> v; rewrite edges_at_dipole3 cardsT card_ord. Qed.

Lemma regular_m_dipole3 : regular_m dipole3 3.
Proof. exact: cubic_dipole3. Qed.

(** ** [regular_m] — degenerate identity: the edgeless graph is 0-regular. *)
Lemma regular_m_unit : regular_m (unit_graph tt) 0.
Proof. by move=> v; apply: eq_card0; case. Qed.

(** ** [loopless] — witness: D_3 is loopless (source [false] ≠ target [true]). *)
Lemma loopless_dipole3 : loopless dipole3.
Proof. by move=> e. Qed.

(** ** [mDelta] — identity: the edgeless multigraph has maximum degree 0. *)
Lemma mDelta_unit : mDelta (unit_graph tt) = 0.
Proof. by rewrite /mDelta; apply: big1 => v _; apply: eq_card0; case. Qed.

(** ** [mDelta] — witness: D_3 has maximum degree 3. *)
Lemma mDelta_dipole3 : mDelta dipole3 = 3.
Proof.
rewrite /mDelta; apply/eqP; rewrite eqn_leq; apply/andP; split.
- by apply/bigmax_leqP => v _; rewrite edges_at_dipole3 cardsT card_ord.
- apply: leq_trans (leq_bigmax (true : dipole3)).
  by rewrite edges_at_dipole3 cardsT card_ord.
Qed.

(** ============================================================================
    [usimple] / [mconnected] / [remove_edge] / [edge_ends] / [msimple].
    ========================================================================== *)

(** ** [usimple] — textbook identity: adjacency in the underlying simple graph
    is exactly multigraph adjacency [madj]. *)
Lemma usimple_adj (G : mgraph) (x y : usimple G) : (x -- y) = madj x y.
Proof. by []. Qed.

(** ** [usimple] — witness: the underlying simple graph of the edgeless
    one-vertex multigraph has no edges. *)
Lemma usimple_unit_no_edge (x y : usimple (unit_graph tt)) : ~~ (x -- y).
Proof. by rewrite usimple_adj /madj; case: x; case: y; rewrite eqxx. Qed.

(** ** [mconnected] — witness: the one-vertex multigraph is connected. *)
Lemma mconnected_unit : mconnected (unit_graph tt).
Proof.
move=> x y _ _; suff -> : x = y by exact: connect0.
by case: x; case: y.
Qed.

(** ** [remove_edge] — identity: deleting an edge keeps the vertex set. *)
Lemma card_remove_edge (G : mgraph) (e : edge G) : #|remove_edge e| = #|G|.
Proof. by []. Qed.

(** ** [remove_edge] — textbook identity: edge deletion preserves looplessness. *)
Lemma remove_edge_loopless (G : mgraph) (e : edge G) :
  loopless G -> loopless (remove_edge e).
Proof. by move=> H [f Hf]; exact: H. Qed.

(** ** [msimple] — witness: the one-vertex edgeless multigraph is simple. *)
Lemma msimple_unit : msimple (unit_graph tt).
Proof. split; first by case. by move=> x1 x2 _; case: x1. Qed.

(** ** [msimple] — textbook identity: D_3 is NOT simple (it has parallel
    edges: every edge has the same endpoint pair {false,true}). *)
Lemma not_msimple_dipole3 : ~ msimple dipole3.
Proof.
case=> _ inj; move: (inj ord0 ord_max).
rewrite /edge_ends /= => /(_ erefl) /(congr1 (@nat_of_ord 3)).
by [].
Qed.

(** ============================================================================
    Row 1 — [diff_edge] / [near_edge] / [strong_edge_colourable].
    ========================================================================== *)

(** ** [diff_edge] — identity: an edge is never "different" from itself. *)
Lemma diff_edge_refl (G : sgraph) (x y : G) : diff_edge x y x y = false.
Proof. by rewrite /diff_edge !eqxx. Qed.

(** ** [near_edge] — identity: an edge is "near" itself (shared endpoints). *)
Lemma near_edge_refl (G : sgraph) (x y : G) : near_edge x y x y.
Proof. by rewrite /near_edge eqxx. Qed.

(** ** [strong_edge_colourable] — witness: ['K_1] (edgeless) is strongly
    1-colourable; the induced-matching constraint is vacuous. *)
Lemma strong_edge_colourable_K1 : strong_edge_colourable 'K_1 1.
Proof.
exists (fun _ _ => ord0); split; first by [].
by move=> x y u v xy; exfalso; move: xy;
  rewrite /edge_rel /= (ord1 x) (ord1 y) eqxx.
Qed.

(** ============================================================================
    Row 2 — [edge_boundary] / [is_r_graph].
    ========================================================================== *)

(** ** [edge_boundary] — identity: the boundary of the empty vertex set is
    empty (no edge has exactly one endpoint in ∅). *)
Lemma edge_boundary_set0 (G : mgraph) : @edge_boundary G set0 = set0.
Proof. by apply/setP => e; rewrite !inE addbb. Qed.

(** ** [edge_boundary] — for D_3 the boundary of either singleton is all three
    edges (each edge crosses from [false] to [true]). *)
Lemma edge_boundary_dipole3 (v : dipole3) :
  @edge_boundary dipole3 [set v] = [set: edge dipole3].
Proof.
apply/setP => e; rewrite !inE /=.
by case: v.
Qed.

(** ** [is_r_graph] — witness: D_3 is a Seymour 3-graph (3-regular, and every
    odd vertex set — necessarily a singleton — has |δ(X)| = 3 ≥ 3). *)
Lemma is_r_graph_dipole3 : is_r_graph dipole3 3.
Proof.
split; first exact: cubic_dipole3.
move=> X oddX.
have hX1 : #|X| == 1.
  move: oddX; have := max_card (mem X); rewrite card_bool => hle.
  by move: hle; case: #|X| => [|[|[|n]]].
case/cards1P: hX1 => v ->.
by rewrite edge_boundary_dipole3 cardsT card_ord.
Qed.

(** ============================================================================
    Row 3 — [subdivide_edge_s] / [subdivR_s] / [homeomorphic_s].
    ========================================================================== *)

(** ** [subdivide_edge_s] — identity: a single-edge subdivision adds one vertex. *)
Lemma card_subdivide_edge_s (G : sgraph) (x y : G) :
  #|subdivide_edge_s x y| = #|G| + 1.
Proof. by rewrite /subdivide_edge_s card_sum card_unit. Qed.

(** ** [subdivide_edge_s] — identity: the new vertex is adjacent to [x]. *)
Lemma subdivide_edge_s_adj (G : sgraph) (x y : G) :
  (inl x : subdivide_edge_s x y) -- (inr tt).
Proof. by rewrite /edge_rel /= eqxx. Qed.

(** ** [subdivR_s] — witness: a graph reaches its single-edge subdivision. *)
Lemma subdivR_s_one (G : sgraph) (x y : G) :
  subdivR_s G (subdivide_edge_s x y).
Proof.
apply: (@subdivR_s_step G G (subdivide_edge_s x y) x y).
- exact: subdivR_s_refl.
- exact: diso_id.
Qed.

(** ** [homeomorphic_s] — identity: homeomorphism is reflexive (common
    subdivision = the graph itself). *)
Lemma homeomorphic_s_refl (G : sgraph) : homeomorphic_s G G.
Proof. by exists G; split; exact: subdivR_s_refl. Qed.

(** ============================================================================
    Row 4 — [overfull_parameter].
    ========================================================================== *)

(** Ceiling division of 0 is 0 (the |S| ≤ 1 terms of w(G) vanish). *)
Lemma ceil_div0 k : ceil_div 0 k = 0.
Proof.
rewrite /ceil_div add0n; case: k => [|k].
- by rewrite sub0n div0n.
- by rewrite subSS subn0 (divn_small (ltnSn k)).
Qed.

(** ** [overfull_parameter] — identity: an edgeless multigraph has w(G) = 0. *)
Lemma overfull_parameter_unit : overfull_parameter (unit_graph tt) = 0.
Proof.
rewrite /overfull_parameter; apply: big1 => S _.
have -> : #|edge_set S| = 0 by apply: eq_card0; case.
exact: ceil_div0.
Qed.

(** ============================================================================
    Row 5 — [hypergraph] / [uniform_hg] / [simple_hg] / [hg_codegree_le].
    ========================================================================== *)

(** Witness hypergraph: a single d-element edge. *)
Definition hg_one (d : nat) : hypergraph :=
  @Hypergraph 'I_d unit (fun _ => setT).

(** ** [uniform_hg] — witness: [hg_one d] is d-uniform. *)
Lemma uniform_hg_one d : uniform_hg (hg_one d) d.
Proof. by move=> e; rewrite /hg_one /= cardsT card_ord. Qed.

(** ** [simple_hg] — witness: [hg_one d] is simple (one edge, trivially
    injective incidence). *)
Lemma simple_hg_one d : simple_hg (hg_one d).
Proof. by move=> [] [] _. Qed.

(** ** [hg_codegree_le] — identity: with a single edge, every (d−1)-set lies in
    at most one edge. *)
Lemma hg_codegree_le_one d : hg_codegree_le (hg_one d) d 1.
Proof. by move=> T _; apply: leq_trans (max_card _) _; rewrite card_unit. Qed.

(** ============================================================================
    Row 6 — [sts] / [sts_valid] / [sts_edge_colourable] / [is_universal_sts].
    ========================================================================== *)

(** Witness STS: the 3-point system with the single block {0,1,2}. *)
Definition sts3 : sts := @STS 'I_3 [set [set: 'I_3]].

(** ** [sts_valid] — witness: [sts3] is a valid Steiner triple system. *)
Lemma sts_valid_sts3 : sts_valid sts3.
Proof.
split.
- by move=> B; rewrite inE => /eqP ->; rewrite cardsT card_ord.
- move=> p q _; exists [set: 'I_3]; split.
  + by rewrite inE eqxx.
  + exact: in_setT.
  + exact: in_setT.
  + by move=> B'; rewrite inE => /eqP -> _ _.
Qed.

(** ** [sts_edge_colourable] — witness: D_3 is [sts3]-edge-colourable
    (colour each edge by its own name; the three edges at a vertex are all of
    ['I_3], which is the single block). *)
Lemma sts_edge_colourable_dipole3 : sts_edge_colourable dipole3 sts3.
Proof.
exists id => v.
have -> : [set id e | e in edges_at v] = [set: 'I_3].
  apply/eqP; rewrite eqEsubset; apply/andP; split; apply/subsetP => j _.
  + by rewrite inE.
  + apply/imsetP; exists j; first by rewrite edges_at_dipole3 in_setT.
    by [].
by rewrite inE eqxx.
Qed.

(** ** [is_universal_sts] — textbook identity: the empty-block STS is NOT
    universal (D_3 is loopless cubic but admits no colouring into ∅). *)
Lemma not_universal_empty : ~ is_universal_sts (@STS 'I_3 set0).
Proof.
move=> H; have [c Hc] := H dipole3 loopless_dipole3 cubic_dipole3.
by move: (Hc (true : dipole3)); rewrite in_set0.
Qed.

(** ============================================================================
    Row 7 — [edge_colour_seq] / [acyclic_edge_colouring].
    ========================================================================== *)

(** ** [edge_colour_seq] — identity: the colour sequence has the cycle's length. *)
Lemma size_edge_colour_seq (G : sgraph) k (col : G -> G -> 'I_k) (s : seq G) :
  size (edge_colour_seq col s) = size s.
Proof. by rewrite /edge_colour_seq size_map size_zip size_rot minnn. Qed.

(** ** [edge_colour_seq] — identity: empty cycle, empty colour sequence. *)
Lemma edge_colour_seq_nil (G : sgraph) k (col : G -> G -> 'I_k) :
  edge_colour_seq col [::] = [::].
Proof. by []. Qed.

(** ** [acyclic_edge_colouring] — witness: ['K_1] has an acyclic edge colouring
    (no edges, no cycles, so every clause is vacuous). *)
Lemma acyclic_edge_colouring_K1 :
  acyclic_edge_colouring (G := 'K_1) (fun _ _ => ord0 : 'I_1).
Proof.
split.
- by [].
- by move=> x y z _ xy; exfalso; move: xy; rewrite /edge_rel /= (ord1 x) (ord1 y) eqxx.
- move=> s /andP[_ /card_uniqP eqsz] hs.
  move: (max_card (mem s)); rewrite eqsz card_ord => h1.
  by move: hs; rewrite ltnNge (leqW h1).
Qed.

(** ============================================================================
    Row 8 — [star_edge_colouring].
    ========================================================================== *)

(** ** [star_edge_colouring] — witness: ['K_1] has a star edge colouring into
    ['I_6] (all path/cycle clauses are vacuous). *)
Lemma star_edge_colouring_K1 :
  star_edge_colouring (G := 'K_1) (fun _ _ => ord0 : 'I_6).
Proof.
split.
- by [].
- by move=> x y z _ xy; exfalso; move: xy; rewrite /edge_rel /= (ord1 x) (ord1 y) eqxx.
- by move=> x0 x1 x2 x3 x4 e01; exfalso; move: e01;
    rewrite /edge_rel /= (ord1 x0) (ord1 x1) eqxx.
- by move=> x0 x1 x2 x3 e01; exfalso; move: e01;
    rewrite /edge_rel /= (ord1 x0) (ord1 x1) eqxx.
Qed.

(** ============================================================================
    Row 9 — [behzads_statement]: guard repair (wave E2b, 2026-09-24).
    ========================================================================== *)

(** ** Guard has teeth: the OLD (unguarded) body, spelled out inline, is
    refutable -- the empty multigraph is simple, has [mDelta = 0] and total
    chromatic number [0], so the lower bound [1 <= 0] fails.  The guard
    [0 < #|G|] of the repaired row excludes exactly this counterexample. *)
Lemma behzads_unguarded_body_refutable :
  ~ (forall G : mgraph, msimple G ->
       (mDelta G).+1 <= total_chromatic_number G <= (mDelta G).+2).
Proof.
move=> H.
pose G : mgraph := @void_graph unit unit.
have sG : msimple G by split; [case | case].
have /andP[lo _] := H G sG.
have f : total_graph G -> 'I_0 by case=> -[].
have hf : forall x y : total_graph G, x -- y -> f x != f y by case=> -[].
by move: (leq_trans lo (chi_le_palette hf)); rewrite card_ord.
Qed.

(** ** Non-vacuity: a concrete NON-EMPTY simple multigraph (one vertex, no
    edges) meets both hypotheses of the repaired row. *)
Lemma behzads_hypotheses_satisfiable :
  exists G : mgraph, msimple G /\ (0 < #|G|)%N.
Proof.
exists (unit_graph tt); split; first exact: msimple_unit.
by apply/card_gt0P; exists tt.
Qed.

(** ============================================================================
    Axiom-freeness audit for the (tooling-awkward) trailing statements.
    ========================================================================== *)

Print Assumptions strong_edge_colouring_statement.
Print Assumptions seymours_r_graph_statement.
Print Assumptions three_edge_coloring_statement.
Print Assumptions goldbergs_statement.
Print Assumptions a_generalization_of_vizings_theorem_statement.
Print Assumptions universal_steiner_triple_systems_statement.
Print Assumptions acyclic_edge_coloring_statement.
Print Assumptions star_chromatic_index_of_cubic_graphs_statement.
Print Assumptions behzads_statement.
Print Assumptions behzads_unguarded_body_refutable.
Print Assumptions behzads_hypotheses_satisfiable.

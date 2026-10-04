(** * Chromatic.conjectures.grounding_U4 — grounding lemmas for milestone U4.

    SIMPLE, Qed-closed sanity results validating the new primitives introduced
    in [U4.v]: for each new definition we record a SATISFIABLE witness and at
    least one textbook identity.  These are statement-validation lemmas, not the
    (open/partial) conjectures themselves.

    Witness graphs are the small complete graphs ['K_0], ['K_1], ['K_n] and the
    one-vertex edgeless multigraph [unit_graph tt] (whose edge type is [void]),
    which make the degenerate/boundary cases of each primitive computable while
    still exercising the definitional content (proper colourings, choosability
    minimality, the paintability recursion, multigraph incidence/line/total
    constructions, complete-multipartite cardinality, acyclic colourings, and
    strong colourability).

    Planarity note: Row 10's statement primitive [acyclically_choosable] is
    validated here ([acyclic_colouring_complete], [acyclically_choosable_K1]);
    the planarity-gated STATEMENT itself ([acyclic_list_colouring_of_planar_
    graphs_statement]) is now genuinely faithful — its planarity hypothesis is
    base's combinatorial [wagner_planar] (no K5 / K3,3 minor, used opaquely), so
    no abstract placeholder remains.  Its colouring core is grounded via the
    [acyclically_choosable] witnesses above. *)

From GTBase Require Import base.
From GraphTheory Require Import minor mgraph.
From Chromatic.conjectures Require Import U4.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** [list_colourable] — witness: the identity colouring of ['K_n] from the
    full palette is a proper list-colouring (distinct vertices get distinct
    colours, which is exactly adjacency in a complete graph). *)
Lemma list_colourable_complete n :
  list_colourable (G := 'K_n) (fun _ : 'K_n => [set: 'K_n]).
Proof.
exists id; split.
- by move=> v; rewrite inE.
- by move=> x y; rewrite /edge_rel /=.
Qed.

(** ** [list_colourable_on] — degenerate identity: the empty induced subgraph
    is always (vacuously) L-colourable. *)
Lemma list_colourable_on_set0 n :
  list_colourable_on (G := 'K_n) (fun _ : 'K_n => [set: 'K_n]) set0.
Proof.
exists (fun=> None); split.
- by move=> v; rewrite in_set0.
- by move=> x y Hx _ _; rewrite in_set0 in Hx.
Qed.

(** ** [list_colourable_on] — witness on the full vertex set [setT]. *)
Lemma list_colourable_on_complete n :
  list_colourable_on (G := 'K_n) (fun _ : 'K_n => [set: 'K_n]) [set: 'K_n].
Proof.
exists (fun v => Some v); split.
- by move=> v _; exists v; rewrite inE.
- move=> x y _ _; rewrite /edge_rel /= => xy.
  by apply/eqP => -[] exy; rewrite exy eqxx in xy.
Qed.

(** ** [choosable] — witness: the one-vertex graph is 1-choosable. *)
Lemma choosable_K1 : choosable 'K_1 1.
Proof.
move=> C L HL.
have /card_gt0P[c Hc] : 0 < #|L ord0| by apply: leq_trans (HL ord0).
exists (fun _ => c); split.
- by move=> v; rewrite (ord1 v).
- by move=> x y xy; exfalso; move: xy;
     rewrite /edge_rel /= (ord1 x) (ord1 y) eqxx.
Qed.

(** ** [choosable] — boundary identity: no graph with a vertex is 0-choosable
    (empty lists cannot be respected); used for the minimality of [ch]. *)
Lemma not_choosable_K1_0 : ~ choosable 'K_1 0.
Proof.
move=> H.
have [f [Hf _]] := H bool (fun _ => set0) (fun _ => leq0n _).
by move: (Hf ord0); rewrite in_set0.
Qed.

(** ** [is_choice_number] — textbook identity: ch('K_1) = 1. *)
Lemma is_choice_number_K1 : is_choice_number 'K_1 1.
Proof.
split; first exact: choosable_K1.
move=> k Hk; case: k Hk => [|k] Hk //.
by case: (not_choosable_K1_0 Hk).
Qed.

(** ** [colourable_count] — identity: with full lists every vertex of ['K_n] is
    colourable, so λ_L = n = #|G|. *)
Lemma colourable_count_complete n :
  colourable_count (G := 'K_n) (fun _ : 'K_n => [set: 'K_n]) n.
Proof.
split.
- exists [set: 'K_n]; split; first exact: list_colourable_on_complete.
  by rewrite cardsT card_ord.
- move=> W _.
  by apply: leq_trans (max_card (mem W)) _; rewrite card_ord.
Qed.

(** ** [is_lambda] — witness/identity: λ_0('K_0) = 0 (no vertices, empty
    size-0 list assignment). *)
Lemma is_lambda_K0 : is_lambda 'K_0 0 0.
Proof.
split.
- exists bool, (fun _ : 'K_0 => set0); split; first by case.
  split.
  + exists set0; split; last by rewrite cards0.
    exists (fun=> None); split.
    * by move=> v Hv; rewrite in_set0 in Hv.
    * by move=> x y Hx _ _; rewrite in_set0 in Hx.
  + move=> W _.
    by apply: leq_trans (max_card (mem W)) _; rewrite card_ord.
- by move=> C L mu _ _.
Qed.

(** ** Paintability helpers. *)
Lemma setT_K0 : [set: 'K_0] = set0.
Proof. by apply/eqP; rewrite -cards_eq0 cardsT card_ord. Qed.

(** Once the alive set is empty, Painter has already won (any fuel). *)
Lemma paintableb_setT_empty (G : sgraph) n (f : G -> nat) :
  [set: G] = set0 -> paintableb n [set: G] f.
Proof. by move=> e; case: n => [|n] /=; rewrite e eqxx. Qed.

(** ** [paintable] — witness: the empty graph is paintable for any budget. *)
Lemma paintable_K0 (f : 'K_0 -> nat) : paintable f.
Proof. by apply: paintableb_setT_empty; exact: setT_K0. Qed.

(** ** [k_paintable] — witness: ['K_0] is k-paintable for every k. *)
Lemma k_paintable_K0 k : k_paintable 'K_0 k.
Proof. exact: paintable_K0. Qed.

(** ** [is_online_choice_number] — textbook identity: ch^OL('K_0) = 0. *)
Lemma is_online_choice_number_K0 : is_online_choice_number 'K_0 0.
Proof. by split; [exact: k_paintable_K0 | move=> k _]. Qed.

(** ** [loopless] — witness: the one-vertex edgeless multigraph is loopless
    (its edge type is empty). *)
Lemma loopless_unit : loopless (unit_graph tt).
Proof. by case. Qed.

(** ** [mDelta] — identity: the edgeless multigraph has maximum degree 0. *)
Lemma mDelta_unit : mDelta (unit_graph tt) = 0.
Proof. by rewrite /mDelta; apply: big1 => v _; apply: eq_card0; case. Qed.

(** ** [Delta_edge_critical] — witness: vacuously Δ-edge-critical (its line
    graph has no vertices). *)
Lemma Delta_edge_critical_unit : Delta_edge_critical (unit_graph tt).
Proof. by case. Qed.

(** ** [line_graph] — identity: the line graph of an edgeless multigraph is
    empty. *)
Lemma line_graph_unit_empty : #|line_graph (unit_graph tt)| = 0.
Proof. exact: card_void. Qed.

(** ** [total_graph] — identity: the total graph of the edgeless one-vertex
    multigraph has no edges. *)
Lemma total_graph_unit_edgeless (a b : total_graph (unit_graph tt)) :
  ~~ (a -- b).
Proof. by case: a => [[]|[]]; case: b => [[]|[]]; rewrite /edge_rel /=. Qed.

(** ** [madj] — textbook identity: no vertex is multi-adjacent to itself. *)
Lemma madj_irrefl (G : mgraph) (x : G) : ~~ madj x x.
Proof. by rewrite /madj eqxx. Qed.

(** ** [share_endpoint] / [incident] — identity: every edge shares an endpoint
    with itself (it is incident to its own source). *)
Lemma share_endpoint_refl (G : mgraph) (e : edge G) : share_endpoint e e.
Proof.
apply/existsP; exists (endpoint false e); apply/andP; split;
  by apply/existsP; exists false; rewrite eqxx.
Qed.

(** ** [line_rel] — identity: adjacency in the line graph entails sharing an
    endpoint. *)
Lemma line_rel_share (G : mgraph) (e1 e2 : edge G) :
  line_rel e1 e2 -> share_endpoint e1 e2.
Proof. by move=> /andP[_]. Qed.

(** ** [total_rel] — identity: in the total graph a vertex is adjacent to every
    edge it is the source of. *)
Lemma total_vertex_edge (G : mgraph) (e : edge G) :
  (inl (source e) : total_graph G) -- (inr e).
Proof. by rewrite /edge_rel /=; apply/existsP; exists false; rewrite eqxx. Qed.

(** ** [complete_multipartite] — textbook identity: K_{m*k} has exactly m·k
    vertices. *)
Lemma card_complete_multipartite k m :
  #|complete_multipartite k m| = k * m.
Proof. by rewrite card_prod !card_ord. Qed.

(** ** [cmp_rel] — identity: vertices in the same part are non-adjacent. *)
Lemma cmp_same_part k m (i : 'I_k) (a b : 'I_m) :
  ~~ @edge_rel (complete_multipartite k m) (i, a) (i, b).
Proof. by rewrite /edge_rel /= /cmp_rel /GTBase.complete_multipartite_graphs.complete_multipartite_rel /= eqxx. Qed.

(** ** [cmp_rel] — identity: vertices in different parts are adjacent. *)
Lemma cmp_diff_part k m (i j : 'I_k) (a b : 'I_m) :
  i != j -> @edge_rel (complete_multipartite k m) (i, a) (j, b).
Proof. by move=> hij; rewrite /edge_rel /=. Qed.

(** ** [acyclic_colouring] — witness: the identity colouring of ['K_n] is
    acyclic (all colours distinct, so every cycle is rainbow). *)
Lemma acyclic_colouring_complete n :
  acyclic_colouring (G := 'K_n) (fun _ : 'K_n => [set: 'K_n]) id.
Proof.
split.
- by move=> v; rewrite inE.
- by move=> x y; rewrite /edge_rel /=.
- move=> c /andP[_ uc] hsz.
  by rewrite map_id (undup_id uc).
Qed.

(** ** [acyclically_choosable] — witness: ['K_1] is acyclically 1-choosable
    (no edges, no genuine cycles). *)
Lemma acyclically_choosable_K1 : acyclically_choosable 'K_1 1.
Proof.
move=> C L HL.
have /card_gt0P[c Hc] : 0 < #|L ord0| by apply: leq_trans (HL ord0).
exists (fun _ => c); split.
- by move=> v; rewrite (ord1 v).
- by move=> x y xy; exfalso; move: xy;
     rewrite /edge_rel /= (ord1 x) (ord1 y) eqxx.
- move=> co /andP[_ /card_uniqP eqsz] hsz.
  move: (max_card (mem co)); rewrite eqsz card_ord => h1.
  move: (leqW h1) => h2.
  by move: hsz; rewrite ltnNge h2.
Qed.

(** ** [strongly_colorable] — witness: the one-vertex graph is strongly
    1-colourable. *)
Lemma strongly_colorable_K1 : strongly_colorable 'K_1 1.
Proof.
move=> P _ _.
exists (fun _ => ord0); split.
- by move=> x y xy; exfalso; move: xy;
     rewrite /edge_rel /= (ord1 x) (ord1 y) eqxx.
- by move=> B _ x y _ _ _; rewrite (ord1 x) (ord1 y).
Qed.

(** ============================================================================
    Minor guards used by Rows 8 and 10.
    ========================================================================== *)

(** ** [minor] guard-has-teeth (Row 8, [list_hadwiger_statement]): the
    K_t-minor-free hypothesis [~ minor G ('K_t)] is genuinely exercised — the
    single-vertex graph ['K_1] has NO ['K_2] minor (a minor never has more
    vertices than its host). *)
Lemma K2_not_minor_K1 : ~ minor 'K_1 'K_2.
Proof. by move=> /minor_card; rewrite !card_ord. Qed.

(** ** [wagner_planar] inhabitation (Row 10 planarity guard): ['K_1] is
    Wagner-planar — it has neither a K5 nor a K3,3 minor, both ruled out by
    cardinality (#|'K_5| = 5 and #|K_{3,3}| = 6 both exceed #|'K_1| = 1). *)
Lemma wagner_planar_K1 : wagner_planar 'K_1.
Proof.
split.
- by move=> /minor_card; rewrite !card_ord.
- by move=> /minor_card; rewrite card_sum !card_ord.
Qed.

(** ============================================================================
    Right-polarity fragments of the PARTIAL statements (TECHNIQUE #2).

    These are genuine half-directions / decided sub-cases of the actual
    STATEMENTS [partial_list_coloring_statement] (Row 1) and
    [strong_colorability_statement] (Row 11) — not merely primitive-validation
    lemmas like the ones above.  Each pins the correct TRUE value on a real
    slice of its conjecture without touching the OPEN interior (AGH's
    Hall/SDR transfer, resp. the Strong-Colouring / Haxell independent-
    transversal machinery), which remain out of scope.
    ========================================================================== *)

(** ** Row 1, [partial_list_coloring_statement] — ALWAYS-TRUE direction
    (choosable regime).  If [L] is fully list-colourable (a proper TOTAL choice
    exists) then the AGH bound holds by taking [W = setT]: the required
    inequality [t·#|G| ≤ cl·#|setT|] collapses to the hypothesis [t ≤ cl].  This
    is the mechanism lemma pinning the ENTIRE "L is genuinely choosable" slice of
    the conjecture to TRUE. *)
Lemma partial_list_coloring_full (G : sgraph) (t cl : nat)
  (C : finType) (L : G -> {set C}) :
  t <= cl -> list_colourable L ->
  exists W : {set G}, list_colourable_on L W /\ t * #|G| <= cl * #|W|.
Proof.
move=> Ht [f [Hf Hp]]; exists [set: G]; split.
- exists (fun v => Some (f v)); split.
  + by move=> v _; exists (f v); rewrite Hf.
  + by move=> x y _ _ xy; apply/eqP => -[] e; move: (Hp x y xy); rewrite e eqxx.
- rewrite cardsT; exact: leq_mul Ht (leqnn _).
Qed.

(** ** Row 1 — TOP endpoint [t = cl] (= χ_ℓ).  With every list of size exactly
    [cl], [choosable G cl] (extracted from [is_choice_number G cl]) yields full
    list-colourability, so [W = setT] gives the equality [cl·#|G| ≤ cl·#|G|].
    This is AGH's settled trivial remark λ_{χ_ℓ} = n, now a fragment of the
    actual statement shape. *)
Lemma partial_list_coloring_top (G : sgraph) (cl : nat)
  (C : finType) (L : G -> {set C}) :
  is_choice_number G cl -> (forall v : G, #|L v| = cl) ->
  exists W : {set G}, list_colourable_on L W /\ cl * #|G| <= cl * #|W|.
Proof.
move=> [Hch _] HL.
apply: (partial_list_coloring_full (t:=cl) (leqnn cl)).
by apply: Hch => v; rewrite HL.
Qed.

(** ** Row 1 — SMALL-INSTANCE: the FULL statement decided on the single-vertex
    graph ['K_1] for every admissible [t].  [is_choice_number 'K_1 cl] forces
    [cl = 1] (uniqueness against the grounded [is_choice_number_K1]), so
    [t ∈ {0,1}]: [t = 0] takes [W = set0] (vacuously colourable, bound
    [0 ≤ cl·0]); [t = 1 = cl] colours [ord0] from its nonempty size-1 list with
    [W = setT] (#|W| = 1, bound [1·1 ≤ 1·1]).  The comma after [('K_1)] in the
    hypothesis is parenthesised to avoid the complete-bipartite ['K_ n , m]
    notation swallowing it. *)
Lemma partial_list_coloring_K1 (t cl : nat) (C : finType) (L : 'K_1 -> {set C}) :
  is_choice_number 'K_1 cl -> t <= cl -> (forall v : ('K_1), #|L v| = t) ->
  exists W : {set 'K_1}, list_colourable_on L W /\ t * #|'K_1| <= cl * #|W|.
Proof.
move=> Hcl Ht HL.
have E1 : cl = 1.
  apply/eqP; rewrite eqn_leq; apply/andP; split.
  - exact: (proj2 Hcl _ (proj1 is_choice_number_K1)).
  - exact: (proj2 is_choice_number_K1 _ (proj1 Hcl)).
move: Ht HL; rewrite E1 => Ht HL.
case: t Ht HL => [|[|t]] // Ht HL.
- exists set0; split.
  + exists (fun=> None); split.
    * by move=> v; rewrite in_set0.
    * by move=> x y Hx _ _; rewrite in_set0 in Hx.
  + by rewrite mul0n.
- have /card_gt0P[c Hc] : 0 < #|L ord0| by rewrite HL.
  exists [set: 'K_1]; split.
  + exists (fun _ => Some c); split.
    * by move=> v _; exists c; rewrite (ord1 v).
    * by move=> x y _ _; rewrite /edge_rel /= (ord1 x) (ord1 y) eqxx.
  + by rewrite cardsT card_ord.
Qed.

(** ** Row 11, [strong_colorability_statement] — ALWAYS-TRUE direction
    (enough-colours engine).  If the palette is at least as large as V(G)
    ([#|G| ≤ r]) then G is strongly r-colourable via the injection
    [widen_ord ∘ enum_rank : G ↪ 'I_r]: an injective colouring is proper
    (adjacency is irreflexive, [sgP]) and rainbow on every block.  This is the
    unconditionally-true half of the statement, TRUE on the whole family
    [{G : #|G| ≤ 2·Δ G}] (all complete / sufficiently dense graphs). *)
Lemma strongly_colorable_card (G : sgraph) (r : nat) :
  #|G| <= r -> strongly_colorable G r.
Proof.
move=> Hle P _ _.
pose f (v : G) := widen_ord Hle (enum_rank v).
have finj : injective f.
  move=> x y; rewrite /f => /(congr1 val); rewrite /widen_ord /= => exy.
  by apply: enum_rank_inj; apply: val_inj.
exists f; split.
- by move=> x y xy; apply/eqP => exy; move: xy; rewrite (finj _ _ exy) sgP.
- by move=> B _ x y _ _; exact: finj.
Qed.

(** ** Row 11 helper — [#|N(x)| = n-1] in ['K_n]: the open neighbourhood of a
    complete-graph vertex is everything but itself. *)
Lemma card_N_complete n (x : 'K_n) : #|N(x)| = n.-1.
Proof.
rewrite /open_neigh.
have -> : [set y | x -- y] = [set: 'K_n] :\ x.
  by apply/setP=> y; rewrite !inE andbT eq_sym.
by rewrite cardsDS ?sub1set ?inE // cardsT card_ord cards1 subn1.
Qed.

(** ** Row 11 helper — [n-1 ≤ Δ('K_n)] for [0 < n]: the degree of any vertex is
    a lower bound for the max degree. *)
Lemma Delta_complete_ge n : 0 < n -> n.-1 <= Delta 'K_n.
Proof.
move=> n0; rewrite /Delta; pose x0 : 'K_n := Ordinal n0.
by rewrite -(card_N_complete x0) (leq_bigmax x0).
Qed.

(** ** Row 11 — SMALL-INSTANCE on the infinite family of complete graphs: for
    [n ≥ 2], ['K_n] is strongly (2·Δ)-colourable.  Here [2·Δ('K_n) = 2(n-1) ≥ n],
    so the enough-colours engine [strongly_colorable_card] applies — a genuine
    non-vacuous decidable slice of the conjecture (K_n really needs all n colours
    distinct). *)
Lemma strong_Kn n : 2 <= n -> strongly_colorable 'K_n (2 * Delta 'K_n).
Proof.
move=> n2; apply: strongly_colorable_card; rewrite card_ord.
apply: (@leq_trans (2 * n.-1)).
- by case: n n2 => [|[|k]] // _; rewrite mul2n -addnn addSn ltnS leq_addl.
- by rewrite leq_mul2l /=; apply: Delta_complete_ge; exact: leq_trans n2.
Qed.

(** ** Row 11 diagnostic — TEETH on the [(partition + block-size ≤ r)] guard at [r = 0]:
    a NONEMPTY graph has no partition all of whose blocks have size ≤ 0 (blocks
    are nonempty), so [strongly_colorable G 0] holds vacuously for [0 < #|G|].
    This is the audited corner that the statement now excludes with [0 < Delta G]. *)
Lemma strongly_colorable0 (G : sgraph) : 0 < #|G| -> strongly_colorable G 0.
Proof.
move=> /card_gt0P[v _] P Ppart Hsz; exfalso.
have vcov : v \in cover P by rewrite (cover_partition Ppart) inE.
have Bin : pblock P v \in P by rewrite pblock_mem.
have := Hsz _ Bin; rewrite leqn0 cards_eq0 => /eqP e0.
by move: (mem_pblock P v); rewrite vcov e0 in_set0.
Qed.

(** ** Row 11 helper — [Δ('K_1) = 0]: the single vertex has no neighbours. *)
Lemma Delta_K1 : Delta 'K_1 = 0.
Proof. by rewrite /Delta big_ord1 card_N_complete. Qed.

(** ** Row 11 diagnostic — the old unguarded statement was vacuous on a NONEMPTY
    edgeless graph ['K_1], where [2·Δ = 0].  Kept as a regression witness for why
    [strong_colorability_statement] carries the [0 < Delta G] guard. *)
Lemma strong_K1 : strongly_colorable 'K_1 (2 * Delta 'K_1).
Proof.
by rewrite Delta_K1 muln0; apply: strongly_colorable0; rewrite card_ord.
Qed.

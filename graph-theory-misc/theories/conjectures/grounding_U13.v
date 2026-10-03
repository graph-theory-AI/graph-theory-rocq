(** * GTMisc.conjectures.grounding_U13 — grounding lemmas for milestone U13.

    SIMPLE, Qed-closed sanity results validating the NEW area-specific primitives
    introduced in [U13.v].  For (essentially) each new definition we record a
    SATISFIABLE witness and at least one textbook identity.  These are
    statement-validation lemmas, NOT the (open) conjectures themselves.

    Two tiny reusable carriers are used throughout:
      - [E0] / [E1] : the edgeless graphs on 0 / 1 vertices (via [mk_sgraph] of
        the empty relation) — clean witnesses for the vacuous / singleton cases;
      - [K2]        : the complete graph on 2 vertices (via [mk_sgraph] of the
        full relation) — the minimal carrier with an edge and with ω = 2,
        needed for the [pebble_move] and [splits_max_cliques] witnesses.

    Reused base / coq-graph-theory primitives ([subdivision], [girth_geq], [ball],
    [regular], [is_hom], [cartesian_product], [clique]/[ω], [connected], [χ]) are
    NOT re-grounded here; they come verbatim from the imported libraries.

    Coverage notes (honest): every new primitive gets at least one Qed-closed
    identity; almost all also get a satisfiable witness.  The exact-diameter
    predicate has a concrete [K2] witness below.  Exact girth is grounded by its
    two structural projections; a positive prescribed-girth witness requires a
    genuine cycle computation, which is out of scope for these SIMPLE sanity
    checks. *)

From GTBase Require Import base.
From GraphTheory Require Import preliminaries.
From mathcomp Require Import fingroup perm.
From GTMisc.conjectures Require Import U13.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ============================================================================
    Reusable tiny carriers.
    ========================================================================== *)

Definition E0 : sgraph := @mk_sgraph 'I_0 (fun _ _ => false).
Definition E1 : sgraph := @mk_sgraph 'I_1 (fun _ _ => false).
Definition K2 : sgraph := @mk_sgraph 'I_2 (fun _ _ => true).

(** [mk_sgraph] of the empty relation has no edges. *)
Lemma mk_sgraph_edgeless (V : finType) (x y : @mk_sgraph V (fun _ _ => false)) :
  ~~ (x -- y).
Proof. by rewrite /edge_rel/= /relAdj/= andbF. Qed.

(** [K2] is genuinely [K2]: adjacency = distinctness. *)
Lemma K2_edge (x y : K2) : (x -- y) = (x != y).
Proof. by rewrite /edge_rel/= /relAdj/= andbT. Qed.

Lemma ord0_neq_max2 : (ord0 : 'I_2) != ord_max.
Proof. by []. Qed.

Lemma setT_E0 : [set: E0] = set0.
Proof. by apply/setP; case=> m mlt; exact: (False_rect _ (notF mlt)). Qed.

Lemma cardT_K2 : #|[set: K2]| = 2.
Proof. by rewrite cardsT card_ord. Qed.

(** ============================================================================
    Shared helpers: [oedges] / [n_edges].
    ========================================================================== *)

(** identity: an oriented edge is an edge. *)
Lemma oedges_edge (G : sgraph) (p : G * G) : p \in oedges G -> p.1 -- p.2.
Proof. by rewrite inE => /andP[]. Qed.

(** identity + witness: edgeless graphs have no oriented edges / 0 edges. *)
Lemma oedges_edgeless (V : finType) :
  oedges (@mk_sgraph V (fun _ _ => false)) = set0.
Proof.
by apply/setP=> p; rewrite !inE (negbTE (mk_sgraph_edgeless p.1 p.2)).
Qed.

Lemma n_edges_edgeless (V : finType) :
  n_edges (@mk_sgraph V (fun _ _ => false)) = 0.
Proof. by rewrite /n_edges oedges_edgeless cards0. Qed.

Lemma n_edges_E1 : n_edges E1 = 0.
Proof. exact: n_edges_edgeless. Qed.

(** ============================================================================
    Row 1 — induced cycles and monochromatic maximum cliques.
    ========================================================================== *)

(** [induced_cycle] — identity (the embedding is injective) + witness (the empty
    0-cycle is induced in any graph, so [has_induced_cycle G 0] is satisfiable). *)
Lemma induced_cycle_inj (G : sgraph) (k : nat) (f : 'I_k -> G) :
  induced_cycle f -> injective f.
Proof. by case. Qed.

Lemma has_induced_cycle_0 (G : sgraph) : has_induced_cycle G 0.
Proof.
exists (fun i : 'I_0 => match i with Ordinal m mlt => False_rect G (notF mlt) end).
by split=> -[m mlt]; exact: (False_rect _ (notF mlt)).
Qed.

(** [is_max_clique] — identity (a max clique is a clique) + witness (the empty
    set is the unique maximum clique of the empty graph, since ω = 0). *)
Lemma is_max_clique_clique (G : sgraph) (Q : {set G}) :
  is_max_clique Q -> clique Q.
Proof. by case. Qed.

Lemma is_max_clique_E0 : is_max_clique (set0 : {set E0}).
Proof.
split; first by move=> x y; rewrite in_set0.
by rewrite cards0 setT_E0 omega0.
Qed.

(** [monochromatic] — witness (any constant colouring is monochromatic) and the
    vacuous-on-[set0] identity. *)
Lemma monochromatic_const (G : sgraph) (b : bool) (Q : {set G}) :
  monochromatic (fun _ => b) Q.
Proof. by move=> x y. Qed.

Lemma monochromatic_set0 (G : sgraph) (c : G -> bool) : monochromatic c set0.
Proof. by move=> x y; rewrite in_set0. Qed.

(** [splits_max_cliques] — a genuine SATISFIABLE witness: on [K2] (ω = 2, the
    unique maximum clique is the whole vertex set {0,1}), the colouring that
    separates the two vertices makes no maximum clique monochromatic. *)
Lemma cliqueb_K2T : [set: K2] \in cliques [set: K2].
Proof.
by rewrite inE subxx /=; apply/cliqueP => x y _ _ xy; rewrite K2_edge xy.
Qed.

Lemma omega_K2 : ω([set: K2]) = 2.
Proof.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- case: (omegaP [set: K2]) => K /maxcliquesW/cliques_subset Ksub.
  by rewrite -cardT_K2; exact: subset_leq_card Ksub.
- by rewrite -cardT_K2; exact: clique_bound cliqueb_K2T.
Qed.

Lemma splits_max_cliques_K2 :
  splits_max_cliques (fun v : K2 => v == ord_max).
Proof.
move=> Q [clq cardQ] mono.
have QT : Q = [set: K2].
  by apply/eqP; rewrite eqEcard subsetT /= cardT_K2 cardQ omega_K2.
have m0 : (ord0 : K2) \in [set: K2] by rewrite inE.
have mM : (ord_max : K2) \in [set: K2] by rewrite inE.
have he := mono ord0 ord_max; rewrite QT in he.
move: (he m0 mM); rewrite eqxx => /eqP/eqP.
by rewrite (negbTE ord0_neq_max2).
Qed.

Lemma splits_max_cliques_sat :
  exists (G : sgraph) (c : G -> bool), splits_max_cliques c.
Proof. by exists K2, (fun v => v == ord_max); exact: splits_max_cliques_K2. Qed.

(** ============================================================================
    Row 2 — book embeddings / book thickness / one-subdivision.
    ========================================================================== *)

(** [book_embedding] — witness (the empty graph admits a 0-page embedding) and a
    textbook monotonicity identity (more pages still embed). *)
Lemma book_embedding_E0_0 : book_embedding E0 0.
Proof.
exists (fun _ : E0 => 0), (fun _ _ : E0 => 0); split;
  by case=> m mlt; exact: (False_rect _ (notF mlt)).
Qed.

Lemma book_embedding_mono (G : sgraph) (k k' : nat) :
  book_embedding G k -> k <= k' -> book_embedding G k'.
Proof.
move=> [pos [col [ip sc bk nc]]] le; exists pos, col; split=> //.
by move=> x y; apply: leq_trans (bk x y) le.
Qed.

(** [is_book_thickness] — witness: the empty graph has book thickness 0. *)
Lemma is_book_thickness_E0_0 : is_book_thickness E0 0.
Proof. split; [exact: book_embedding_E0_0 | by move=> m _]. Qed.

(** [subdivide1] — definitional identity with base's [subdivision _ 2]. *)
Lemma subdivide1E (G : sgraph) : subdivide1 G = subdivision G 2.
Proof. by []. Qed.

(** ============================================================================
    Row 3 — average degree / subgraph.
    ========================================================================== *)

(** [avgdeg_geq] — witness (average degree ≥ 0 always) + monotonicity identity. *)
Lemma avgdeg_geq_0 (G : sgraph) : avgdeg_geq G 0.
Proof. by rewrite /avgdeg_geq /average_degree_geq mul0n. Qed.

Lemma avgdeg_geq_mono (G : sgraph) (d d' : nat) :
  avgdeg_geq G d -> d' <= d -> avgdeg_geq G d'.
Proof. rewrite /avgdeg_geq /average_degree_geq => H le. apply: leq_trans H. by rewrite leq_mul2r le orbT. Qed.

(** [subgraph_of] — reflexivity (every graph is a subgraph of itself). *)
Lemma subgraph_of_refl (G : sgraph) : subgraph_of G G.
Proof. by apply/has_subgraphP; exists id; split=> // x y. Qed.

(** ============================================================================
    Row 4 — graph-from-relation, edge-union, degeneracy.
    ========================================================================== *)

(** [mk_sgraph] / [edge_union] — definitional edge identities. *)
Lemma mk_sgraph_edge (V : finType) (r : rel V) (x y : @mk_sgraph V r) :
  (x -- y) = relAdj r x y.
Proof. by []. Qed.

Lemma edge_union_edge (V : finType) (r1 r2 : rel V) (x y : edge_union r1 r2) :
  (x -- y) = relAdj (fun a b => r1 a b || r2 a b) x y.
Proof. by []. Qed.

(** [degenerate] — witness (every graph is [#|G|]-degenerate) + monotonicity. *)
Lemma degenerate_max (G : sgraph) : k_degenerate G #|G|.
Proof. by move=> S _ /set0Pn[x xS]; exists x; split=> //; exact: max_card. Qed.

Lemma degenerate_mono (G : sgraph) (k k' : nat) :
  k_degenerate G k -> k <= k' -> k_degenerate G k'.
Proof.
move=> H le S Hsub Hs; have [v [vS dv]] := H S Hsub Hs.
by exists v; split=> //; apply: leq_trans dv le.
Qed.

(** ============================================================================
    Multistage networks (Rows 5 and 11).
    ========================================================================== *)

(** [stage_regular] — witness: the full bipartite stage on ['I_t] is t-regular. *)
Lemma stage_regular_full (t : nat) : @stage_regular t (fun _ _ => true) t.
Proof.
split=> x;
  by rewrite (_ : [set _ | true] = setT) ?cardsT ?card_ord //;
     apply/setP=> z; rewrite !inE.
Qed.

(** [stage_reachable] — witness (0-stage reaches itself) + identity (0-stage
    reachability is equality). *)
Lemma stage_reachable_0 (t : nat) (S : rel 'I_t) (a : 'I_t) :
  stage_reachable S 0 a a.
Proof. by exists [::]. Qed.

Lemma stage_reachable_0_eq (t : nat) (S : rel 'I_t) (a b : 'I_t) :
  stage_reachable S 0 a b -> a = b.
Proof. by move=> [w [/size0nil -> _ <-]]. Qed.

(** [externally_connected] — witness: the full stage is externally connected in
    one stage. *)
Lemma externally_connected_full (t : nat) :
  @externally_connected t (fun _ _ => true) 1.
Proof. by move=> a b; exists [:: b]. Qed.

(** [multistage_route] — witness: the constant route realises the identity
    permutation through 0 stages. *)
Lemma multistage_route_id (t : nat) (S : rel 'I_t) :
  multistage_route S 0 (fun i _ => i) 1%g.
Proof.
split.
- by [].
- by move=> i; rewrite perm1.
- by move=> i s; rewrite ltn0.
- by move=> s _ x y ->.
Qed.

(** [rearrangeable] — witness: any single-node stage is rearrangeable in 0
    stages (the only permutation of ['I_1] is the identity). *)
Lemma rearrangeable_I1_0 (S : rel 'I_1) : rearrangeable S 0.
Proof.
move=> pi; exists (fun i _ => i); split.
- by [].
- by move=> i; rewrite (ord1 i) (ord1 (pi ord0)).
- by move=> i s; rewrite ltn0.
- by move=> s _ x y ->.
Qed.

(** [se_adj] — identity: the n=1 shuffle-exchange stage (on ['I_1]) is total when
    the radix is positive. *)
Lemma se_adj_n1 (k : nat) (i j : 'I_(k ^ (1 - 1))) : 0 < k -> @se_adj k 1 i j.
Proof.
move=> kpos; rewrite /se_adj; change (k ^ (1 - 1)) with 1.
by rewrite modn1.
Qed.

(** ============================================================================
    Row 6 — pebbling.
    ========================================================================== *)

(** [pebble_move] — identity (a move needs an edge) + a concrete satisfiable
    move on [K2]. *)
Lemma pebble_move_edge (G : sgraph) (D D' : G -> nat) :
  pebble_move D D' -> exists u v : G, u -- v.
Proof. by move=> [u [v [uv _ _]]]; exists u, v. Qed.

Lemma pebble_move_sat : exists (D D' : K2 -> nat), pebble_move D D'.
Proof.
exists (fun _ => 2).
exists (fun w => if w == ord0 then 2 - 2 else if w == ord_max then 2 + 1 else 2).
by exists ord0, ord_max; split.
Qed.

(** [reaches] — reflexive (witness [reaches_refl]) and transitive (identity). *)
Lemma reaches_trans (G : sgraph) (D1 D2 D3 : G -> nat) :
  reaches D1 D2 -> reaches D2 D3 -> reaches D1 D3.
Proof.
move=> H; move: D3; elim: H => [E|A B C ab r IH] D3 H2; first exact: H2.
exact: reaches_step ab (IH _ H2).
Qed.

(** [solvable] — witness: a target already holding a pebble is solvable. *)
Lemma solvable_refl (G : sgraph) (D : G -> nat) (r : G) :
  1 <= D r -> solvable D r.
Proof. by move=> H; exists D; split; [exact: reaches_refl | exact: H]. Qed.

(** [is_pebbling_number] — identity: the pebbling number, when it exists, is
    unique (least-N is characterised up to equality). *)
Lemma is_pebbling_number_uniq (G : sgraph) (N M : nat) :
  is_pebbling_number G N -> is_pebbling_number G M -> N = M.
Proof.
move=> [solN minN] [solM minM].
by apply/eqP; rewrite eqn_leq (minN _ solM) (minM _ solN).
Qed.

(** ============================================================================
    Row 7 — diameter / girth (structural projection identities).
    ========================================================================== *)

Lemma has_diameter_ball (G : sgraph) (d : nat) :
  has_diameter G d -> forall u v : G, v \in ball d u.
Proof. by case. Qed.

(** Witness: [K2] has exact diameter 1. *)
Lemma has_diameter_K2_1 : has_diameter K2 1.
Proof.
split.
- move=> u v; rewrite /= !inE.
  case uv: (v == u); first by [].
  rewrite /=.
  apply/bigcupP; exists u; first by rewrite inE eqxx.
  by rewrite inE K2_edge eq_sym uv.
- exists (ord0 : K2); exists (ord_max : K2).
  by rewrite /= !inE.
Qed.

Lemma has_girth_geq (G : sgraph) (g : nat) : has_girth G g -> girth_geq G g.
Proof. by case. Qed.

Lemma has_girth_cycle (G : sgraph) (g : nat) :
  has_girth G g -> exists c : seq G, ucycle (--) c /\ 2 < size c /\ size c = g.
Proof. by case. Qed.

(** ============================================================================
    Row 8 — trees / graceful labellings.
    ========================================================================== *)

(** [is_tree_card] — witness: the single-vertex graph is a tree. *)
Lemma is_tree_card_E1 : is_tree_card E1.
Proof.
split; last by rewrite n_edges_E1 card_ord.
by apply: connectedTI => x y; rewrite (ord1 x) (ord1 y); exact: connect0.
Qed.

(** [edge_label] — identities: symmetric, and zero on a loop. *)
Lemma edge_label_sym (G : sgraph) (l : G -> nat) (u v : G) :
  edge_label l (u, v) = edge_label l (v, u).
Proof. by rewrite /edge_label /= addnC. Qed.

Lemma edge_label_self (G : sgraph) (l : G -> nat) (v : G) :
  edge_label l (v, v) = 0.
Proof. by rewrite /edge_label /= subnn. Qed.

(** [graceful_labeling] — witness: the single-vertex tree is gracefully
    labelled by the constant-0 labelling (no edges to constrain). *)
Lemma graceful_labeling_E1 : graceful_labeling (fun _ : E1 => 0).
Proof.
split.
- by move=> x y _; rewrite (ord1 x) (ord1 y).
- by move=> v; rewrite n_edges_E1.
- by move=> p; rewrite oedges_edgeless in_set0.
- by move=> p q; rewrite oedges_edgeless in_set0.
Qed.

(** ============================================================================
    Row 9 — imbalance / graphic sequences.
    ========================================================================== *)

(** [vdeg] — definitional identity. *)
Lemma vdegE (G : sgraph) (v : G) : vdeg v = #|N(v)|.
Proof. by []. Qed.

(** [imb] — identities: symmetric, and zero on a loop. *)
Lemma imb_sym (G : sgraph) (u v : G) : imb (u, v) = imb (v, u).
Proof. by rewrite /imb /= addnC. Qed.

Lemma imb_self (G : sgraph) (v : G) : imb (v, v) = 0.
Proof. by rewrite /imb /= subnn. Qed.

(** [seq_M_G] — witness/identity: the imbalance multiset of an edgeless graph is
    empty. *)
Lemma seq_M_G_edgeless (V : finType) :
  seq_M_G (@mk_sgraph V (fun _ _ => false)) = [::].
Proof. by rewrite /seq_M_G oedges_edgeless enum_set0. Qed.

(** [graphic] — witness: the empty sequence is graphic (realised by the empty
    graph). *)
Lemma graphic_nil : graphic [::].
Proof. by exists E0; rewrite setT_E0 enum_set0. Qed.

(** ============================================================================
    Row 10 — the gold-grabbing game.
    ========================================================================== *)

(** [is_leaf] — identity (a leaf is in the set) + witness (the lone vertex of
    [E1] is takeable). *)
Lemma is_leaf_mem (G : sgraph) (S : {set G}) (v : G) : is_leaf S v -> v \in S.
Proof. by move=> /andP[]. Qed.

Lemma is_leaf_E1 : is_leaf [set: E1] ord0.
Proof.
apply/andP; split; first by rewrite inE.
by apply: leq_trans (max_card _) _; rewrite card_ord.
Qed.

(** [gold_total] — identity: empty state holds no gold. *)
Lemma gold_total_set0 (G : sgraph) (g : G -> nat) : gold_total g set0 = 0.
Proof. by rewrite /gold_total big_set0. Qed.

(** [leaf_game_solution] — witness: on the single-vertex tree, the game value is
    the total gold and the (only) optimal move is the lone vertex; this satisfies
    the Bellman optimality recursion. *)
Lemma leaf_game_E1 (g : E1 -> nat) :
  leaf_game_solution g (gold_total g) (fun _ => ord0).
Proof.
move=> S; split.
- move=> Hno; case: (set_0Vmem S) => [->|[v vS]].
  + by rewrite gold_total_set0.
  + exfalso; apply: Hno; exists v; apply/andP; split=> //.
    by apply: leq_trans (max_card _) _; rewrite card_ord.
- move=> [w /andP[wS _]].
  have o0S : ord0 \in S by rewrite -(ord1 w).
  have SE : S = [set ord0] by apply/setP=> x; rewrite (ord1 x) inE eqxx o0S.
  have Sd : S :\ ord0 = set0
    by rewrite SE; apply/setP=> x; rewrite in_setD1 inE andNb in_set0.
  split.
  + by rewrite SE; apply/andP; split;
       [exact: set11 | apply: leq_trans (max_card _) _; rewrite card_ord].
  + by rewrite Sd gold_total_set0 addn0 subn0 /gold_total SE big_set1.
  + by move=> u _;
       rewrite (ord1 u) Sd gold_total_set0 addn0 subn0 /gold_total SE big_set1.
Qed.

(** ============================================================================
    Row 12 — hexagonal weighted colouring.
    ========================================================================== *)

(** [tri_adj] — identity (irreflexive) + a concrete satisfiable adjacency. *)
Lemma tri_adj_irrefl (a : nat * nat) : tri_adj a a = false.
Proof.
case: a => x y; rewrite /tri_adj (ltn_eqF (ltnSn x)) (ltn_eqF (ltnSn y)).
by rewrite !andFb !andbF.
Qed.

Lemma tri_adj_sat : tri_adj (0, 0) (1, 0).
Proof. by []. Qed.

(** [hexagonal] — witness: the single-vertex graph embeds in the triangular
    lattice. *)
Lemma hexagonal_E1 : hexagonal E1.
Proof.
exists (fun _ : E1 => (0, 0)); split.
- by move=> x y _; rewrite (ord1 x) (ord1 y).
- by move=> u v; rewrite (ord1 u) (ord1 v) eqxx.
Qed.

(** [weighted_clique_number] — witness: under the zero weighting every weighted
    clique number is 0. *)
Lemma weighted_clique_number_zero (G : sgraph) :
  weighted_clique_number (fun _ : G => 0) 0.
Proof.
split.
- by exists set0; split; [move=> x y; rewrite in_set0 | rewrite big_set0].
- by move=> Q _; rewrite big1_eq.
Qed.

(** [weighted_colourable] — witness: the zero weighting is 0-colourable. *)
Lemma weighted_colourable_zero (G : sgraph) :
  weighted_colourable (fun _ : G => 0) 0.
Proof.
exists (fun _ : G => set0); split.
- by move=> v; rewrite cards0.
- by move=> x y _; rewrite -setI_eq0 set0I eqxx.
Qed.

(** [weighted_chromatic_number] — witness: the zero weighting has weighted
    chromatic number 0. *)
Lemma weighted_chromatic_number_zero (G : sgraph) :
  weighted_chromatic_number (fun _ : G => 0) 0.
Proof. by split; [exact: weighted_colourable_zero | move=> m _]. Qed.

(** ============================================================================
    TECHNIQUE #3 — independent second encodings + proved equivalences.

    For two load-bearing primitives of [U13.v] we give a SECOND, structurally
    unrelated formalization and prove it equivalent to the original (Qed,
    axiom-free).  Agreement between the two independent encodings is the
    faithfulness evidence for the chosen definition.
    ========================================================================== *)

(** ---------------------------------------------------------------------------
    [stage_reachable] — combinatorial walk  vs  iterated relational power.

    [stage_reachable S m a b] is an EXISTENTIAL over an explicit witness sequence
    [w] (a length-[m] walk along [S] from [a] to [b]).  The independent encoding
    [relpow] is the [m]-fold relational composition of [S] — a fuel-recursive
    boolean fixpoint (the "matrix power" characterization), with no witness list.
    The equivalence is the classic "walk exists  iff  reachable in a bounded
    number of relational-composition steps"; the proof is a genuine induction on
    [m] with a [c :: w'] / [exists c] case analysis, not a definitional unfold. *)

Fixpoint relpow {t : nat} (S : rel 'I_t) (m : nat) (a b : 'I_t) : bool :=
  match m with
  | 0 => a == b
  | m'.+1 => [exists c : 'I_t, S a c && relpow S m' c b]
  end.

Definition stage_reachable_alt {t} (S : rel 'I_t) (m : nat) (a b : 'I_t) : Prop :=
  relpow S m a b.

Lemma stage_reachableP (t : nat) (S : rel 'I_t) (m : nat) (a b : 'I_t) :
  stage_reachable S m a b <-> stage_reachable_alt S m a b.
Proof.
rewrite /stage_reachable /stage_reachable_alt.
elim: m a => [|m IH] a /=.
- split.
  + by move=> [w [/size0nil -> _ <-]]; rewrite eqxx.
  + by move=> /eqP <-; exists [::].
- split.
  + move=> [w [sz]]; case: w sz => [|c w'] // [sz] /=.
    move=> /andP[Sac pcw] lcw.
    apply/existsP; exists c; rewrite Sac /=.
    by apply/IH; exists w'.
  + move=> /existsP[c] /andP[Sac /IH [w' [sz pcw lcw]]].
    by exists (c :: w'); split=> //=; [rewrite sz | rewrite Sac].
Qed.

(** ---------------------------------------------------------------------------
    [n_edges] — oriented-pair edge count  vs  local degree-sum (handshake).

    [n_edges G = #|oedges G|] counts undirected edges via a GLOBAL set of
    [enum_rank]-ORDERED pairs [(lo, hi)] (one canonical representative per edge).
    The independent encoding [n_edges_alt G = (\sum_v #|N(v)|)./2] is the LOCAL
    per-vertex degree sum, halved — the handshaking-lemma characterization, which
    never mentions an ordering or a representative choice.

    Bridge: [#|oedges G| = #|E(G)|] via the bijection [p |-> [set p.1; p.2]] onto
    coq-graph-theory's UNORDERED 2-set edge set [E(G)] (injective because the
    [enum_rank] order pins which endpoint is which; surjective by ordering the
    two endpoints of any [set x;y]); then reuse the library handshake theorem
    [edges_sum_degrees : 2 * #|E(G)| = \sum_(x in G) #|N(x)|] and halve. *)

Definition n_edges_alt (G : sgraph) : nat := (\sum_(v : G) #|N(v)|)./2.

Lemma oedges_card_edges (G : sgraph) : #|oedges G| = #|E(G)|.
Proof.
pose f (p : G * G) := [set p.1; p.2].
have finj : {in oedges G &, injective f}.
  move=> [a b] [c d]; rewrite !inE /= => /andP[_ rab] /andP[_ rcd].
  rewrite /f /= => /doubleton_eq_iff[[-> ->]//|[ea bd]].
  move: rab rcd; rewrite ea bd => rab' rcd'.
  by move: (ltn_trans rab' rcd'); rewrite ltnn.
have imf : [set f p | p in oedges G] = E(G).
  apply/setP => e; apply/idP/idP.
  - move=> /imsetP[[a b] Hab He]; move: Hab; rewrite inE /= => /andP[ab _].
    by apply/edgesP; exists a, b; split; [rewrite He /f /= | exact: ab].
  - move=> /edgesP[x [y [He xy]]].
    have rxy : enum_rank x != enum_rank y.
      by rewrite (inj_eq enum_rank_inj) (sg_edgeNeq xy).
    apply/imsetP; rewrite He.
    case: (ltngtP (enum_rank x) (enum_rank y)) => [lt|gt|eqn].
    + by exists (x, y); [rewrite inE /= xy lt | rewrite /f /=].
    + by exists (y, x); [rewrite inE /= sgP xy gt | rewrite /f /= setUC].
    + by move: rxy; rewrite (val_inj eqn) eqxx.
by rewrite -imf (card_in_imset finj).
Qed.

Lemma n_edges_double (G : sgraph) : 2 * n_edges G = \sum_(v : G) #|N(v)|.
Proof. by rewrite /n_edges oedges_card_edges edges_sum_degrees. Qed.

Theorem n_edges_handshake (G : sgraph) : n_edges G = n_edges_alt G.
Proof. by rewrite /n_edges_alt -n_edges_double mul2n doubleK. Qed.

(** * Hom.conjectures.grounding_U3 — grounding lemmas for milestone U3.

    SIMPLE, Qed-closed sanity results validating the new primitives introduced
    in [U3.v].  For each new definition we record a SATISFIABLE WITNESS and at
    least one TEXTBOOK IDENTITY the definition must satisfy.  These are
    statement-validation lemmas, NOT the (open/solved/disproved) conjectures
    themselves.

    They double as the bridges promised in U3.v's comments — in particular
    [hom_ffunP : reflect (is_hom f) (hom_ffun f)] proves that the boolean
    endomorphism predicate [hom_ffun] coincides with base's Prop-valued [is_hom]
    (so Row 9 reuses base's homomorphism vocabulary, it does not redefine it),
    and [mapping_planar_antimono] shows the Row-7 planarity gate is a genuine
    discharged Section parameter (contravariant in [is_planar]), confirming the
    faithfulness fix away from the inert inner [forall is_planar]. *)

From GTBase Require Import base.
From GraphTheory Require Import dom.
From mathcomp Require Import fingroup.
From Hom.conjectures Require Import U3.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** [cycle_graph] / [C5] — witness + identity. *)

(** Satisfiable witness: [C5] has an edge (vertices 0 and 1 are adjacent). *)
Lemma C5_has_edge : exists x y : C5, x -- y.
Proof.
exists (@Ordinal 5 0 isT), (@Ordinal 5 1 isT).
by rewrite /edge_rel /= /cyc_rel /=.
Qed.

(** Textbook identity: in a cycle, adjacency forces the cyclic-successor
    relation on the indices (one of the two consecutive cases holds). *)
Lemma cycle_adj_succ n (i j : cycle_graph n) :
  i -- j -> ((val i).+1 %% n == val j) || ((val j).+1 %% n == val i).
Proof. by rewrite /edge_rel /= /cyc_rel => /andP[_]. Qed.

(** ** [path_graph] — witness + identity. *)

(** Satisfiable witness: [path_graph 2] has an edge (0 and 1 are adjacent). *)
Lemma path_graph_has_edge : exists x y : path_graph 2, x -- y.
Proof.
exists (@Ordinal 2 0 isT), (@Ordinal 2 1 isT).
by rewrite /edge_rel /= /path_graphs.ordinal_path_rel /=.
Qed.

(** Textbook identity: in a path, adjacency forces consecutive indices
    (no modular wrap). *)
Lemma path_adj_succ n (i j : path_graph n) :
  i -- j -> ((val i).+1 == val j) || ((val j).+1 == val i).
Proof. by rewrite /edge_rel /= /path_graphs.ordinal_path_rel. Qed.

(** ** [star_graph] — witness + identity. *)

(** Definitional identity: the 2-vertex star is the single edge ['K_1,1]. *)
Lemma star_graph2 : star_graph 2 = 'K_1, 1.
Proof. by []. Qed.

(** Textbook identity: the [n]-vertex star really has [n] vertices. *)
Lemma card_star_graph n : 0 < n -> #|star_graph n| = n.
Proof. by move=> n0; rewrite /star_graph card_sum !card_ord add1n prednK. Qed.

(** ** [bipartite_rel] — witness + closure identity. *)

(** Satisfiable witness: the empty relation is bipartite. *)
Lemma bipartite_rel0 (G : sgraph) : bipartite_rel (fun _ _ : G => false).
Proof. by exists (fun=> true). Qed.

(** Textbook identity: bipartiteness is downward closed (a sub-relation of a
    bipartite relation is bipartite). *)
Lemma bipartite_rel_sub (G : sgraph) (r s : rel G) :
  (forall x y, r x y -> s x y) -> bipartite_rel s -> bipartite_rel r.
Proof. by move=> rs [f Hf]; exists f => x y /rs/Hf. Qed.

(** ** [triangle_free] — witness via a graph carrying an edge. *)

(** Helper: a 2-vertex graph has no triangle (three pairwise-adjacent, hence
    pairwise-distinct, vertices would need 3 vertices). *)
Lemma no_tri_card2 (G : sgraph) (x y z : G) :
  #|G| = 2 -> x -- y -> y -- z -> z -- x -> False.
Proof.
move=> cardG xy yz zx.
have Exy : (x == y) = false := sg_edgeNeq xy.
have Eyz : (y == z) = false := sg_edgeNeq yz.
have Ezx : (z == x) = false := sg_edgeNeq zx.
have card3 : #|[set x; y; z]| = 3.
  rewrite -setUA cardsU1 cards2 !inE negb_or Exy Eyz [x == z]eq_sym Ezx.
  by [].
have h := subset_leq_card (subsetT [set x; y; z]).
by move: h; rewrite card3 cardsT cardG.
Qed.

(** Witness: ['K_2] (an edge) is triangle-free. *)
Lemma triangle_free_K2 : triangle_free 'K_2.
Proof. by move=> x y z; apply: no_tri_card2; rewrite card_ord. Qed.

(** ** [k_connected] — witness + projection identity. *)

(** Satisfiable witness: every nonempty graph is 0-connected (the connectivity
    clause is vacuous for [k = 0]). *)
Lemma k_connected0 : k_connected 'K_1 0.
Proof. by split=> [|S]; rewrite ?card_ord ?ltn0. Qed.

(** Textbook identity: [k]-connectivity requires more than [k] vertices. *)
Lemma k_connected_card (G : sgraph) k : k_connected G k -> k < #|G|.
Proof. by case. Qed.

(** ** [longest_cycle] — defining-property projections. *)

Lemma longest_cycle_ucycle (G : sgraph) (c : seq G) :
  longest_cycle c -> ucycle (--) c.
Proof. by case/seq_longest_cycle_ucycleE. Qed.

Lemma longest_cycle_size (G : sgraph) (c : seq G) :
  longest_cycle c -> 2 < size c.
Proof. by case/seq_longest_cycle_ucycleE. Qed.

(** Maximality: no cycle is longer than a longest cycle. *)
Lemma longest_cycle_max (G : sgraph) (c c' : seq G) :
  longest_cycle c -> ucycle (--) c' -> size c' <= size c.
Proof. by case/seq_longest_cycle_ucycleE=> _ _ H; apply: H. Qed.

(** ** [chord] — projection identity. *)

(** Textbook identity: a chord is in particular an edge of the graph. *)
Lemma chord_edge (G : sgraph) (c : seq G) :
  chord c -> exists x y : G, x -- y.
Proof. by case=> x [y] [_ _ xy _ _]; exists x, y. Qed.

(** ** [is_path] — witnesses + identity. *)

(** Witness: the empty walk and any single vertex are paths. *)
Lemma is_path_nil (G : sgraph) : is_path (G := G) [::].
Proof. by []. Qed.

Lemma is_path1 (G : sgraph) (x : G) : is_path [:: x].
Proof. by []. Qed.

(** Textbook identity: the vertices of a path are pairwise distinct. *)
Lemma is_path_uniq (G : sgraph) (s : seq G) : is_path s -> uniq s.
Proof. by case/andP. Qed.

(** ** [longest_path] — witness + projection identities. *)

Lemma longest_path_is_path (G : sgraph) (s : seq G) :
  longest_path s -> is_path s.
Proof. by case. Qed.

Lemma longest_path_max (G : sgraph) (s t : seq G) :
  longest_path s -> is_path t -> size t <= size s.
Proof. by case=> _ H; apply: H. Qed.

(** Satisfiable witness: in the 1-vertex graph ['K_1] the single-vertex walk is
    a longest path (no path can be longer than the number of vertices). *)
Lemma longest_path_K1 : longest_path (G := 'K_1) [:: ord0].
Proof.
split; first exact: is_path1.
move=> t /andP[ut _].
have E : #|mem t| = size t by apply/card_uniqP.
rewrite /= -E.
by apply: leq_trans (max_card (mem t)) _; rewrite card_ord.
Qed.

(** ** [hom_ffun] / [endo_count] — reflection bridge + witness. *)

(** Bridge: [hom_ffun] is exactly the boolean reflection of base's [is_hom]
    (this is the lemma promised in U3.v's Row-9 comment, documenting that the
    endomorphism predicate reuses — does not redefine — base's homomorphism). *)
Lemma hom_ffunP (G : sgraph) (f : {ffun G -> G}) :
  reflect (is_hom f) (hom_ffun f).
Proof.
apply: (iffP idP).
- move/forallP => H x y xy.
  move/forallP: (H x) => H'.
  by move/implyP: (H' y); apply.
- move=> H; apply/forallP => x; apply/forallP => y.
  by apply/implyP => xy; exact: (H x y xy).
Qed.

(** Witness/identity: every graph has at least one endomorphism (the identity),
    so the endomorphism count is positive. *)
Lemma endo_count_gt0 (G : sgraph) : 0 < endo_count G.
Proof.
apply/card_gt0P; exists [ffun x => x]; rewrite inE.
apply/forallP => x; apply/forallP => y; apply/implyP => xy.
by rewrite !ffunE.
Qed.

(** ** [hom_equiv] — reflexivity (witness) + symmetry (identity). *)

Lemma hom_equiv_refl (G : sgraph) : hom_equiv G G.
Proof. by split; exists id => x y. Qed.

Lemma hom_equiv_sym (G H : sgraph) : hom_equiv G H -> hom_equiv H G.
Proof. by case=> a b; split. Qed.

(** ** [srg] / [strongly_regular] — witness via ['K_2]. *)

Lemma neighK2 (x : 'K_2) : N(x) = ~: [set x].
Proof. by apply/setP => y; rewrite !inE eq_sym. Qed.

Lemma regular_K2 : regular 'K_2 1.
Proof.
by move=> x; rewrite neighK2 (cardsCs (~: [set x])) setCK cards1 card_ord subn1.
Qed.

(** ['K_2] is strongly regular with parameters (k,l,m) = (1,0,0). *)
Lemma srg_K2 : srg 'K_2 1 0 0.
Proof.
split.
- exact: regular_K2.
- move=> x y xy.
  have e2 : [set x] :|: [set y] = [set: 'K_2].
    apply/eqP; rewrite eqEcard subsetT cardsU1 inE cards1 cardsT card_ord.
    by rewrite (sg_edgeNeq xy).
  by rewrite /common_nbr !neighK2 -setCU e2 setCT cards0.
- move=> x y xney nadj; exfalso; move: nadj.
  by rewrite (_ : (x -- y) = (x != y)) ?xney.
Qed.

Lemma strongly_regular_K2 : strongly_regular 'K_2.
Proof. by exists 1, 0, 0; exact: srg_K2. Qed.

(** ** [pcayley] / [pconn_set] — witness + edgeless identity. *)

(** Satisfiable witness: the empty connection set is a valid Cayley set. *)
Lemma pconn_set0 (M : finGroupType) (k : nat) :
  pconn_set (@set0 {ffun 'I_k -> M}).
Proof. by split=> [|f]; rewrite inE. Qed.

(** Textbook identity: the Cayley graph of the empty connection set is edgeless. *)
Lemma pcayley_set0_edgeless (M : finGroupType) (k : nat)
  (f g : pcayley (@set0 {ffun 'I_k -> M})) : ~~ (f -- g).
Proof. by rewrite /edge_rel /= /pcayley_rel !inE andbF. Qed.

(** ** [graph_power] / [subdivision] / [frac_power] — promoted constructions,
    grounded again in this (2nd) area ([@MOVE-to-base] candidates). *)

(** Identity: the 0-th power is edgeless. *)
Lemma graph_power0_edgeless (G : sgraph) (x y : graph_power G 0) : ~~ (x -- y).
Proof.
by rewrite /edge_rel /= /pow_rel /reach_le /= !inE [y == x]eq_sym orbb andNb.
Qed.

(** Identity: in a subdivision, original vertices are never adjacent. *)
Lemma sub_inl_inl (G : sgraph) n (a b : G) :
  ~~ @edge_rel (subdivision G n) (inl a) (inl b).
Proof. by rewrite /edge_rel /= /sub_rel /=. Qed.

(** Identity: the 0-th fractional power is edgeless. *)
Lemma frac_power0_edgeless (G : sgraph) n (x y : frac_power G 0 n) : ~~ (x -- y).
Proof. exact: graph_power0_edgeless. Qed.

(** ** Row 7 planarity gate — now GENUINE via base's [wagner_planar].

    The Row-7 statement no longer takes a planarity predicate parameter: it
    instantiates planarity at base's combinatorial, axiom-free [wagner_planar]
    ([~ minor _ 'K_5 /\ ~ minor _ (KB 3 3)] — Wagner planarity), used opaquely.
    The former antitone-in-[is_planar] sanity lemma is therefore retired (the
    placeholder it validated is gone).  We instead record that the statement is
    non-vacuous as a hypothesis shape: it has the expected [forall G k]
    quantifier structure with a real planarity premise. *)
Lemma mapping_planar_statement_shape :
  mapping_planar_graphs_to_odd_cycles_statement =
  (forall (G : sgraph) (k : nat),
     0 < k -> wagner_planar G -> girth_geq G (4 * k) ->
     homs_to G (cycle_graph (2 * k + 1))).
Proof. by []. Qed.

(** ** [tensor_product] (×, Hedetniemi's product) — non-vacuity, teeth, law.

    The tensor / categorical product is the central construction of Row 1
    (Hedetniemi).  These three lemmas ground it: its carrier is not spuriously
    edgeless, tensoring genuinely depends on both factors (not an always-full
    relation), and adjacency obeys the defining product law. *)

(** Inhabitation: the tensor product of two edge-bearing graphs has an edge —
    [(0,0) -- (1,1)] in ['K_3 × 'K_3] (both coordinate pairs are distinct, hence
    adjacent in ['K_3]).  The Hedetniemi carrier is not spuriously edgeless. *)
Lemma tensor_product_has_edge : exists x y : (tensor_product 'K_3 'K_3), x -- y.
Proof.
exists (@Ordinal 3 0 isT, @Ordinal 3 0 isT).
exists (@Ordinal 3 1 isT, @Ordinal 3 1 isT).
by rewrite /edge_rel/= /tensor_rel/=.
Qed.

(** Guard has teeth: tensoring any graph [G] with ['K_1] kills every edge (the
    second coordinate is forced equal, and adjacency is irreflexive).  So the
    tensor relation genuinely depends on both factors — it is not always full. *)
Lemma tensor_product_K1_edgeless (G : sgraph) (x y : tensor_product G 'K_1) :
  ~~ (x -- y).
Proof.
have E2 : x.2 = y.2 by rewrite [x.2]ord1 [y.2]ord1.
by rewrite /edge_rel/= /tensor_rel/= E2 sg_irrefl andbF.
Qed.

(** Structural law: adjacency in [G × H] projects to adjacency in both
    coordinates — the defining property of the categorical product. *)
Lemma tensor_edge_proj (G H : sgraph) (x y : tensor_product G H) :
  x -- y -> (x.1 -- y.1) && (x.2 -- y.2).
Proof. by []. Qed.

(** ** [girth_geq] — satisfiability witness (Row 2 / Row 7 premise). *)

(** Inhabitation: [girth_geq 'K_1 g] holds for every [g] — ['K_1] is acyclic, so
    it has no genuine cycle (any [ucycle] is [uniq], hence of size [<= 1 < 3]) and
    vacuously satisfies the girth bound.  So [girth_geq] is not accidentally
    always-false (which would make the pentagon/planarity implications vacuous). *)
Lemma girth_geq_K1 g : girth_geq 'K_1 g.
Proof.
move=> c /andP[_ uc] sz.
have E : #|mem c| = size c by apply/card_uniqP.
have le1 : size c <= 1.
  rewrite -E; apply: leq_trans (max_card (mem c)) _; by rewrite card_ord.
by move: (leq_trans sz le1).
Qed.

(** ** [is_core] — satisfiability witness (Row 4 / Row 6 conclusion). *)

(** Inhabitation: ['K_1] is a core — every endomorphism of the one-vertex graph
    is (trivially) bijective.  So the [is_core] conclusion predicate is
    satisfiable, not accidentally always-false. *)
Lemma is_core_K1 : is_core 'K_1.
Proof. by move=> f _; exists f; move=> x; rewrite (ord1 (f (f x))) (ord1 x). Qed.

(** ** Row 1 — Hedetniemi's EASY direction (the always-true [<=] half).

    Hedetniemi's equality [χ(G × H) = min(χ G, χ H)] was DISPROVED by Shitov
    (2019): there are finite [G],[H] with [χ(G × H) < min(χ G, χ H)].  That
    refutation is the [>=] direction and is OUT OF SCOPE here — it requires
    Shitov's giant construction (χ ~ 3400+); no small counterexample exists
    (Hedetniemi holds whenever [min(χ G, χ H) <= 4], El-Zahar–Sauer), so the
    inequality cannot be violated by any graph a proof-assistant could enumerate.

    The [<=] direction, however, is TRUE FOR ALL graphs, and we prove it here.
    It rests on the categorical-product structure recorded by [tensor_edge_proj]:
    both coordinate projections [p ↦ p.1] and [p ↦ p.2] are graph homomorphisms
    [tensor_product G H → G] (resp. [→ H]).  The engine is [chi_hom_le]: a
    homomorphism [f : A → B] pulls any proper colouring of [B] back to a proper
    colouring of [A] (the fibres over the colour classes stay stable because
    [f] preserves edges), whence [χ A <= χ B]. *)

(** Colouring pulls back along a homomorphism, so χ is monotone under [homs_to]:
    if [f : A → B] is edge-preserving then [χ(A) <= χ(B)].  Proof: take an optimal
    colouring [P] of [B]; the map [g z := pblock P (f z)] (the [P]-block of [f z])
    induces the partition [P' := preim_partition g [set: A]] of [A].  Each block of
    [P'] is stable — two vertices [u],[v] in one block share a block [T := g u = g v]
    of [P], and if [u -- v] then [f u -- f v] with [f u, f v ∈ T], contradicting
    stability of [T].  And [#|P'| <= #|P|] because each block is [g]-constant and
    [g] lands in [P].  Then [color_bound] gives [χ(A) <= #|P'| <= #|P| = χ(B)]. *)
Lemma chi_hom_le (A B : sgraph) (f : A -> B) :
  is_hom f -> (χ([set: A]) <= χ([set: B]))%N.
Proof.
move=> homf.
case: (chiP [set: B]) => P colP _.
have [partP stabP] := andP colP.
have covP : cover P = [set: B] := cover_partition partP.
pose g (z : A) := pblock P (f z).
have gP z : g z \in P by apply: pblock_mem; rewrite covP inE.
pose P' := preim_partition g [set: A].
have colP' : coloring P' [set: A].
  apply/andP; split; first exact: preim_partitionP.
  apply/forall_inP => S SP'.
  move: SP'; rewrite /P' /preim_partition /equivalence_partition.
  move=> /imsetP[x _ ->].
  apply/stableP => u v uS vS.
  move: uS vS; rewrite !inE => /andP[_ /eqP gxu] /andP[_ /eqP gxv].
  apply/negP => uv.
  have fuv : f u -- f v := homf _ _ uv.
  have stT : stable (pblock P (f u)) by move/forall_inP: stabP; apply; exact: gP.
  have fuT : f u \in pblock P (f u) by rewrite mem_pblock covP inE.
  have Euv : pblock P (f u) = pblock P (f v) by rewrite -/(g u) -/(g v) -gxu gxv.
  have fvT : f v \in pblock P (f u) by rewrite Euv mem_pblock covP inE.
  by move/stableP: stT => /(_ _ _ fuT fvT); rewrite fuv.
apply: leq_trans (color_bound colP') _.
have HP' : P' = (fun T : {set B} => [set y in [set: A] | T == g y]) @: (g @: [set: A]).
  rewrite -imset_comp /P' /preim_partition /equivalence_partition.
  by apply: eq_imset => x /=.
rewrite HP'.
apply: leq_trans (leq_imset_card _ _) _.
apply: subset_leq_card; apply/subsetP => T /imsetP[z _ ->].
exact: gP.
Qed.

(** Hedetniemi's EASY direction: [χ(G × H) <= min(χ G, χ H)], for ALL [G],[H].
    Both projections of the tensor product are homomorphisms ([tensor_edge_proj]),
    so [chi_hom_le] bounds [χ(G × H)] by [χ G] and by [χ H] simultaneously. *)
Lemma hedetniemi_le G H :
  (χ([set: tensor_product G H]) <= minn (χ([set: G])) (χ([set: H])))%N.
Proof.
rewrite leq_min; apply/andP; split.
- apply: (chi_hom_le (f := fun p : tensor_product G H => p.1)) => x y xy.
  by have /andP[h _] := tensor_edge_proj xy.
- apply: (chi_hom_le (f := fun p : tensor_product G H => p.2)) => x y xy.
  by have /andP[_ h] := tensor_edge_proj xy.
Qed.

(** ** [chord] — independent re-encoding via cyclic successor/predecessor
    (TECHNIQUE #3: a second, structurally unrelated encoding + a proved [<->]).

    [chord] (U3.v) identifies "cyclically consecutive in [c]" with membership
    in the positional edge-list [zip c (rot 1 c)].  We give here a second,
    structurally unrelated characterization [chord_succ] built from MathComp's
    cyclic combinators [next] / [path.prev] (path.v) — index-lookup fixpoints
    ([next_nth] / [prev_nth]) with no [zip] and no [rot].  A chord is then an
    edge [x -- y] between two cycle vertices such that [y] is NEITHER the
    cyclic successor [next c x] NOR the cyclic predecessor [path.prev c x] of
    [x].  (We qualify [path.prev] because [GraphTheory] shadows the bare name
    [prev].)

    For [uniq c] — the regime of every [longest_cycle], since
    [ucycle = cycle && uniq] — the two encodings coincide ([chordE], Qed).
    The bridge is the crux [zip_rot1_next]: for [uniq c], the pair [(x,y)] is
    a cycle-edge exactly when [x \in c] and [y = next c x].  That is a genuine
    [nth] / [index] / [rot] identity (NOT reflexivity): it reconciles the
    positional zip-with-rotation encoding of adjacency-in-the-cycle with the
    functional [next] encoding, and its proof needs [nthP], [nth_zip],
    [index_uniq], and the pointwise bridge [next_nth_rot]. *)

(** Pointwise bridge: the cyclic successor is the rotated-list lookup at the
    vertex's own index (this is where [next] and [rot 1] are reconciled). *)
Lemma next_nth_rot (T : eqType) (c : seq T) (x : T) :
  x \in c -> next c x = nth x (rot 1 c) (index x c).
Proof.
move=> xc.
rewrite next_nth xc.
case: c xc => [//|y0 c'] xc.
rewrite rot1_cons nth_rcons.
have hi : index x (y0 :: c') < size (y0 :: c') by rewrite index_mem.
case: ltnP => [hlt|hge].
- by apply: set_nth_default.
- suff -> : index x (y0 :: c') = size c' by rewrite eqxx nth_default.
  by apply/eqP; rewrite eqn_leq hge andbT -ltnS.
Qed.

(** Crux: for [uniq c], [(x,y)] lies in the cycle-edge list [zip c (rot 1 c)]
    exactly when [x] is a vertex and [y] is its cyclic successor. *)
Lemma zip_rot1_next (T : eqType) (c : seq T) (x y : T) :
  uniq c -> ((x, y) \in zip c (rot 1 c)) = (x \in c) && (next c x == y).
Proof.
move=> uc.
apply/idP/idP.
- move=> /(nthP (x, y)) [i]; rewrite size_zip size_rot minnn => hi hxy.
  move: hxy; rewrite nth_zip; last by rewrite size_rot.
  case=> hx hy.
  have xc : x \in c by rewrite -hx; apply: mem_nth.
  have idx : index x c = i by rewrite -hx index_uniq.
  rewrite xc /=; apply/eqP.
  rewrite (next_nth_rot xc) idx -hy.
  by apply: set_nth_default; rewrite size_rot.
- case/andP => xc /eqP hn.
  apply/(nthP (x, y)); exists (index x c).
    by rewrite size_zip size_rot minnn index_mem.
  rewrite nth_zip; last by rewrite size_rot.
  rewrite nth_index //.
  congr (_, _).
  rewrite -hn (next_nth_rot xc).
  by apply: set_nth_default; rewrite size_rot index_mem.
Qed.

(** For [uniq c]: "[x] is the successor of [y]" and "[y] is the predecessor of
    [x]" are the same boolean (the [next]/[path.prev] cancellation). *)
Lemma succ_pred_eq (T : eqType) (c : seq T) (x y : T) :
  uniq c -> (next c y == x) = (path.prev c x == y).
Proof.
move=> uc; apply/idP/idP => /eqP H; apply/eqP.
- by rewrite -H prev_next.
- by rewrite -H next_prev.
Qed.

(** Independent re-encoding of [chord]: an edge [x -- y] joining two cycle
    vertices that are neither cyclic successors nor cyclic predecessors. *)
Definition chord_succ (G : sgraph) (c : seq G) : Prop :=
  exists x y : G,
    [/\ x \in c, y \in c, x -- y, next c x != y & path.prev c x != y].

(** TECHNIQUE #3 target (Qed, axiom-free): on the [uniq] cycles to which
    [chord] is applied, the zip/rot encoding and the successor/predecessor
    encoding agree. *)
Lemma chordE (G : sgraph) (c : seq G) :
  uniq c -> (chord c <-> chord_succ c).
Proof.
move=> uc; split.
- move=> [x [y] [xc yc xy nxy nyx]].
  exists x, y; split=> //.
  + by rewrite zip_rot1_next // xc andTb in nxy.
  + by rewrite zip_rot1_next // yc andTb succ_pred_eq // in nyx.
- move=> [x [y] [xc yc xy nxy nyx]].
  exists x, y; split=> //.
  + by rewrite zip_rot1_next // xc andTb.
  + by rewrite zip_rot1_next // yc andTb succ_pred_eq.
Qed.

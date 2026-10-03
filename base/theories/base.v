(** * GTBase.base — graph-theory-base: the single owner of cross-area primitives

    The shared foundation of the graph-theory-rocq federation (plan §A ownership
    table).  It (1) RE-EXPORTS the core undirected vocabulary of coq-graph-theory
    so every area package imports it from ONE place, and (2) owns the cross-area
    primitives that more than one area needs.

    Surface discovered + validated by the U1 (chromatic-theory) milestone:
      re-exported:  [sgraph], [x -- y], [N(x)] (open_neigh), [χ(A)]=[chi_mem],
                    [ω(A)]=[omega_mem], [α], [clique]/[cliques], [connected],
                    ['K_n]=[complete n], [F ≃ G]=[diso], [ucycle]/[ucycleb];
      owned here:   [Delta] (Δ), [common_nbr], [regular], [min_degree_at_least], [min_degree], [subcubic],
                    [girth_geq], [ceil_div].

    Planarity is NOT here yet: the [coq-graph-theory-planar] / [coq-fourcolor]
    layer (plan gate G2) is added only once that spike passes.

    ** Vocabulary statements MUST use (WP4b)

    Before introducing a [Local xNNN_...] definition in a conjecture file, look
    here and in [GRAPHTHEORY_API.md] / [MATHCOMP_EXTRAITS.md].  A notion needed by
    >= 2 packages belongs in [GTBase.common]; by >= 2 waves of one package, in that
    package's [foundations/]; only then local.

    From coq-graph-theory (all re-exported above):
    - [sgraph.v]: [sgraph], [x -- y], [N(x)] ([open_neigh]), [NS(S)],
      [E(G)] ([sg_edge_set]), [in_edges], [card_edge_Kn], [connected],
      [connectedb], [clique]/[cliqueb], [is_forest]/[is_tree]/[is_forestb],
      [Path]/[upath]/[irred]/[IPath], [subgraph]/[induced]/[induced_type],
      [add_node]/[del_edges], ['K_n] ([complete]), ['K_n,m] ([KB]),
      [diso] ([F ≃ G]), [num_edges], [components].
    - [digraph.v]: [diGraph] ([relType]), [DiGraph], [edge_rel], [connect],
      [Path]/[pathp]/[upath], [induced]/[del_edge] on digraphs.
    - [connectivity.v]: [separator]/[separatorb], [separates], [vseparator],
      [kconnected] ([k.-connected], Menger form), [matching], [dimatching].
    - [minor.v]: [minor], [strict_minor], [minor_map], [minor_rmap] (re-exported as
      abbreviations).  [K4_free] is NOT re-exported — see the import block below.
    - [treewidth.v]: [sdecomp] (tree decomposition; [width] itself is in [sgraph.v]).
    - [dom.v]: [stable], [dominating], [irredundant] (booleans), [max_st]/[min_dom]/
      [max_irr], the weighted [gamma_w]/[alpha_w]/[IR_w], [hereditary]/
      [superhereditary], [weight_set].  NB these live in
      [Section Domination_Theory (G : sgraph)], so after the section they read
      [stable S], [dominating S], ... with [G] implicit.
    - [coloring.v]: [coloring], [chi_mem] ([χ(A)]), [omega_mem] ([ω(A)]), [α].
    - MathComp [path.v]: [path]/[sorted], [cycle]/[ucycle]/[ucycleb], [upath],
      [arc], [rot], [next].
    - [partition.v] / [helly.v] are LEMMA modules: [Require Import] them on demand.

    From [GTBase.common] (see that file): [sg_edge_setE]/[in_sg_edge_set] (the
    bridge from the local [*_edge_set] comprehensions to [E(G)]; there is NO
    [edge_set] in base — that name belongs to [mgraph.edge_set]), [edge_disjoint],
    [perfect_matching], [hamiltonian_cycle]/[hamiltonian], [hamiltonian_path]/
    [traceable], [del_edge_set], [k_edge_connected], [has_subgraph],
    [induced_free], [complete_bipartite], [oriented], [tournament], [acyclic].

    Owned by this file: [Delta] (Δ), [ceil_div], [common_nbr], [regular], [min_degree_at_least], [min_degree], [subcubic],
    [girth_geq], [has_girth], [bipartite], [triangle_free], [cycle_graph],
    [k_connected] (Whitney form, with [k_connected1]; the library's Menger-form
    [kconnected] is also available), [k_degenerate]/[k_degenerate_on], [average_degree_geq],
    [is_hom]/[homs_to]/[is_core], [cartesian_product], [tensor_product],
    [graph_power], [subdivision], [frac_power], [wagner_planar], [minor_card],
    [mgraph] notation, [loopless], [mregular]/[mcubic]/[loopless_cubic], [line_graph], [total_graph],
    [chromatic_index] (χ'), [total_chromatic_number] (χ''), [edge_colourable],
    [total_colourable], [mDelta], [uwalk], [list_colourable]/[list_colourable_on],
    [choosable], [is_choice_number].
    Owned by the other [GTBase] modules re-exported below: [asymptotics],
    [complexity], [finite_graph], [graph_metric] (distances), [list_flexibility],
    [posets], [surface], [bipartitions] (supplied and existential finite
    bipartitions, relation colourings, and edge-deletion adapters), [walks_paths] (vertex sequences: [seq_vertices], the
    support of a raw sequence, with its correspondence to the library [Path]), [incidence]
    ([incidence_degree]: the number of members of a supplied finite family containing a vertex). *)

From mathcomp Require Export all_boot.
(* WP4b: the core undirected vocabulary of coq-graph-theory is exported from ONE place.
   [connectivity] (connected/connectedb, separator/separates/vseparator, kconnected,
   matching/dimatching), [treewidth] (sdecomp) and [dom]
   (stable/dominating/irredundant, gamma_w/alpha_w/IR_w) joined the original
   [digraph sgraph coloring] so that conjecture statements reuse the library instead of
   re-encoding these notions locally.  [partition]/[helly] stay out: they are lemma modules,
   imported on demand.  The package is compiled with [-w -notation-overridden]. *)
From GraphTheory Require Export digraph sgraph coloring connectivity treewidth dom.
(* mgraph is IMPORTED, not EXPORTED: base needs the multigraph type to define the line/total
   graph below, but mgraph's notations/coercions would shadow the sgraph vocabulary in pure-sgraph
   importers (U1/U3). Downstream gets base's [mgraph] notation + line_graph/total_graph/χ'/χ'';
   an mgraph-area milestone (U5) imports mgraph itself for the raw edge/source/incident API. *)
From GraphTheory Require Import mgraph.
(* minor is IMPORTED and then SELECTIVELY re-exported.  A full [Require Export minor] also
   exports [minor.K4_free] (on [sgraph]), which shadows the [K4_free] on [iGraph] owned by
   infinite-graph-theory/foundations/igraph.v and breaks
   infinite-graph-theory/theories/conjectures/grounding_D4inf1.v (a file base does not own).
   The abbreviations below give downstream the minor vocabulary without that one name;
   a package that wants [K4_free] on [sgraph] does [From GraphTheory Require Import minor]. *)
From GraphTheory Require Import minor.
Notation minor := GraphTheory.core.minor.minor.
Notation strict_minor := GraphTheory.core.minor.strict_minor.
Notation minor_map := GraphTheory.core.minor.minor_map.
Notation minor_rmap := GraphTheory.core.minor.minor_rmap.
From GTBase Require Export common.
From GTBase Require Export bipartitions.
From GTBase Require Export asymptotics.
From GTBase Require Export complexity.
From GTBase Require Export finite_graph.
From GTBase Require Export graph_metric.
From GTBase Require Export list_flexibility.
From GTBase Require Export posets.
From GTBase Require Export monochromatic.
From GTBase Require Export incidence.
From GTBase Require Export surface.
From GTBase Require Export walks_paths.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The loopless multigraph type: a [graph unit unit] (unlabelled vertices/edges). *)
Notation mgraph := (graph unit unit).

(** Maximum degree Δ(G).  Empty graph ↦ 0; users carry a non-triviality guard. *)
Definition Delta (G : sgraph) : nat := \max_(x : G) #|N(x)|.

(** ⌈a/b⌉, with the mathcomp convention ⌈a/0⌉ = 0.  Graph-free arithmetic helper. *)
Definition ceil_div (a b : nat) : nat := (a + b - 1) %/ b.

(** Common open neighbourhood of two vertices. *)
Definition common_nbr (G : sgraph) (u v : G) : {set G} := N(u) :&: N(v).

(** [d]-regularity: every vertex has degree exactly [d]. *)
Definition regular (G : sgraph) (d : nat) : Prop := forall v : G, #|N(v)| = d.

(** Minimum-degree LOWER BOUND: every vertex has at least [d] neighbours, the universal form
    [forall v, d <= #|N(v)|].  It is not an attained minimum: the empty graph ['K_0] satisfies
    every bound ([min_degree_at_least_K0]) and no nonemptiness is built in, so comparisons with
    [Delta] or [#|G|] take a vertex ([min_degree_at_least_Delta], [min_degree_at_least_lt_card]).
    On an induced subgraph the bound is [min_degree_at_least (induced S) d]; it is not inherited
    from [G].  "No isolated vertices" is the bound 1 ([min_degree_at_least1P]).  Upstream degree
    facts give the complete, complete bipartite and k-connected cases.
    Registry: meta/library_primitives/minimum-degree-at-least.json (A11). *)
Definition min_degree_at_least (G : sgraph) (d : nat) : Prop := forall v : G, d <= #|N(v)|.

Lemma min_degree_at_least0 (G : sgraph) : min_degree_at_least G 0.
Proof. by []. Qed.

(** Antitone in the bound. *)
Lemma min_degree_at_least_le (G : sgraph) (d d' : nat) :
  d' <= d -> min_degree_at_least G d -> min_degree_at_least G d'.
Proof. by move=> dd' h v; apply: leq_trans (h v). Qed.

Lemma regular_min_degree_at_least (G : sgraph) (d : nat) :
  regular G d -> min_degree_at_least G d.
Proof. by move=> h v; rewrite h. Qed.

(** The bound 1: no isolated vertex. *)
Lemma min_degree_at_least1P (G : sgraph) :
  min_degree_at_least G 1 <-> forall v : G, exists w : G, v -- w.
Proof.
split=> h v; last by have [w vw] := h v; apply/card_gt0P; exists w; rewrite in_opn.
by have /card_gt0P[w] := h v; rewrite in_opn => vw; exists w.
Qed.

(** The empty graph satisfies every bound. *)
Lemma min_degree_at_least_K0 (d : nat) : min_degree_at_least 'K_0 d.
Proof. by case. Qed.

Lemma min_degree_at_least_Kn (n : nat) : min_degree_at_least 'K_n.+1 n.
Proof. by move=> v; exact: deg_Kn. Qed.

Lemma min_degree_at_least_Knm (n m : nat) : min_degree_at_least 'K_n,m (minn n m).
Proof. by move=> v; exact: deg_Knm. Qed.

Lemma min_degree_at_least_kconnected (G : sgraph) (k : nat) :
  k.-connected G -> min_degree_at_least G k.
Proof. by move=> h v; exact: kconnected_degree. Qed.

(** Isomorphisms preserve the bound: they map the neighbours of [x] onto those of its image.
    ([bij] is imported locally, for its coercion to functions.) *)
Section DisoDegree.
Import bij.

Lemma min_degree_at_least_diso (G H : sgraph) (i : G ≃ H) (d : nat) :
  min_degree_at_least G d -> min_degree_at_least H d.
Proof.
have deg (x : G) : #|N(i x)| = #|N(x)|.
  rewrite -(card_imset (mem N(x)) (@bij_injective _ _ i)); apply: eq_card => w.
  apply/idP/imsetP => [|[z zx ->]]; last by rewrite in_opn edge_diso -in_opn.
  by rewrite in_opn -{1}[w](bijK' i) edge_diso -in_opn => xw; exists (i^-1 w); rewrite ?bijK'.
by move=> h y; rewrite -[y](bijK' i) deg.
Qed.

End DisoDegree.

(** With a vertex, the bound is at most the maximum degree and below the order. *)
Lemma min_degree_at_least_Delta (G : sgraph) (d : nat) (v : G) :
  min_degree_at_least G d -> d <= Delta G.
Proof. by move=> h; apply: leq_trans (h v) _; exact: leq_bigmax. Qed.

Lemma min_degree_at_least_lt_card (G : sgraph) (d : nat) (v : G) :
  min_degree_at_least G d -> d < #|G|.
Proof.
move=> h; apply: leq_ltn_trans (h v) _; rewrite -cardsT; apply: proper_card.
by apply/properP; split; [exact: subsetT | exists v; rewrite ?inE ?in_opn ?sg_irrefl].
Qed.

(** Exact (attained) minimum degree: the lower bound [min_degree_at_least G d] together with a vertex of
    degree exactly [d].  The attaining vertex makes the graph nonempty: ['K_0] has no minimum degree
    ([min_degree_K0]).  The value is unique ([min_degree_uniq]), exists as soon as [G] has a vertex
    ([min_degree_exists]) and is the greatest lower bound ([min_degree_at_leastE]); there is no numeric
    minimum with a default value.  [min_degree_attained_firstE] gives the presentation with the attaining
    vertex first.  Registry: meta/library_primitives/minimum-degree.json (A12). *)
Definition min_degree (G : sgraph) (d : nat) : Prop :=
  min_degree_at_least G d /\ exists v : G, #|N(v)| = d.

Lemma min_degree_lower (G : sgraph) (d : nat) : min_degree G d -> min_degree_at_least G d.
Proof. by case. Qed.

Lemma min_degree_attained (G : sgraph) (d : nat) : min_degree G d -> exists v : G, #|N(v)| = d.
Proof. by case. Qed.

Lemma min_degree_attained_firstE (G : sgraph) (d : nat) :
  min_degree G d <-> (exists v : G, #|N(v)| = d) /\ min_degree_at_least G d.
Proof. by split; case=> h1 h2; split. Qed.

Lemma min_degree_uniq (G : sgraph) (d d' : nat) : min_degree G d -> min_degree G d' -> d = d'.
Proof.
case=> hd [v vd] [hd' [w wd']]; apply/eqP; rewrite eqn_leq.
have h1 := hd w; have h2 := hd' v; rewrite wd' in h1; rewrite vd in h2.
by rewrite h1 h2.
Qed.

(** A graph with a vertex has a minimum degree: the degree of a vertex of least degree. *)
Lemma min_degree_exists (G : sgraph) (v : G) : exists d, min_degree G d.
Proof.
have [x _ hx] := @arg_minnP G v predT (fun x : G => #|N(x)|) isT.
by exists #|N(x)|; split; [move=> w; exact: hx | exists x].
Qed.

Lemma min_degree_exists_card (G : sgraph) : 0 < #|G| -> exists d, min_degree G d.
Proof. by case/card_gt0P=> v _; exact: (min_degree_exists v). Qed.

(** The empty graph has no minimum degree. *)
Lemma min_degree_K0 (d : nat) : ~ min_degree 'K_0 d.
Proof. by case=> _ [[]]. Qed.

(** A [d]-regular graph with a vertex has minimum degree [d]. *)
Lemma regular_min_degree (G : sgraph) (d : nat) (v : G) : regular G d -> min_degree G d.
Proof. by move=> h; split; [exact: regular_min_degree_at_least | exists v; exact: h]. Qed.

(** The minimum degree is the greatest lower bound. *)
Lemma min_degree_at_leastE (G : sgraph) (d d' : nat) :
  min_degree G d -> min_degree_at_least G d' <-> d' <= d.
Proof.
case=> hd [v vd]; split=> [h|le]; first by rewrite -vd; exact: h.
exact: min_degree_at_least_le le hd.
Qed.

Lemma min_degree_Delta (G : sgraph) (d : nat) : min_degree G d -> d <= Delta G.
Proof. by case=> hd [v _]; exact: (min_degree_at_least_Delta v hd). Qed.

Lemma min_degree_lt_card (G : sgraph) (d : nat) : min_degree G d -> d < #|G|.
Proof. by case=> hd [v _]; exact: (min_degree_at_least_lt_card v hd). Qed.

Lemma min_degree_Kn (n : nat) : min_degree 'K_n.+1 n.
Proof.
split; first exact: min_degree_at_least_Kn.
have lt : #|N(ord0 : 'K_n.+1)| < #|'K_n.+1|.
  rewrite -cardsT; apply: proper_card; apply/properP; split; first exact: subsetT.
  by exists ord0; rewrite ?inE ?in_opn ?sg_irrefl.
by exists ord0; apply/eqP; rewrite eqn_leq deg_Kn andbT -ltnS; move: lt; rewrite card_ord.
Qed.

(** Isomorphisms preserve degrees, hence the minimum degree.  ([bij] is imported locally.) *)
Section DisoMinDegree.
Import bij.

Lemma diso_degree (G H : sgraph) (i : G ≃ H) (x : G) : #|N(i x)| = #|N(x)|.
Proof.
rewrite -(card_imset (mem N(x)) (@bij_injective _ _ i)); apply: eq_card => w.
apply/idP/imsetP => [|[z zx ->]]; last by rewrite in_opn edge_diso -in_opn.
by rewrite in_opn -{1}[w](bijK' i) edge_diso -in_opn => xw; exists (i^-1 w); rewrite ?bijK'.
Qed.

Lemma min_degree_diso (G H : sgraph) (i : G ≃ H) (d : nat) : min_degree G d -> min_degree H d.
Proof.
case=> hd [v vd]; split; first exact: min_degree_at_least_diso hd.
by exists (i v); rewrite diso_degree.
Qed.

End DisoMinDegree.

(** Subcubic simple graphs: every vertex has at most three neighbours, the pointwise upper bound
    [forall v, #|N(v)| <= 3].  It is equivalent, unconditionally, to [Delta G <= 3] ([subcubicP]); the empty
    graph is subcubic (its [Delta] is 0).  This simple-graph bound is distinct from the multigraph incidence
    contracts [mcubic]/[loopless_cubic] and from the exact minimum [min_degree].
    Registry: meta/library_primitives/subcubic.json (A14). *)
Definition subcubic (G : sgraph) : Prop := forall v : G, #|N(v)| <= 3.

(** The finite-maximum bridge. *)
Lemma subcubicP (G : sgraph) : subcubic G <-> Delta G <= 3.
Proof. by split=> [h|/bigmax_leqP h v]; [apply/bigmax_leqP => v _; exact: h | exact: h]. Qed.

Lemma subcubic_K0 : subcubic 'K_0.
Proof. by case. Qed.

Lemma regular_subcubic (G : sgraph) (d : nat) : regular G d -> d <= 3 -> subcubic G.
Proof. by move=> h d3 v; rewrite h. Qed.

(** Complete graphs on at most four vertices are subcubic; [K_5] is not. *)
Lemma subcubic_Kn (n : nat) : n <= 3 -> subcubic 'K_n.+1.
Proof.
move=> n3 v; apply: leq_trans n3.
have lt : #|N(v)| < #|'K_n.+1|.
  rewrite -cardsT; apply: proper_card; apply/properP; split; first exact: subsetT.
  by exists v; rewrite ?inE ?in_opn ?sg_irrefl.
by move: lt; rewrite card_ord ltnS.
Qed.

Lemma not_subcubic_K5 : ~ subcubic 'K_5.
Proof. by move/(_ ord0); move: (@deg_Kn 4 ord0); case: #|_| => [|[|[|[|]]]]. Qed.

Section DisoSubcubic.
Import bij.

Lemma subcubic_diso (G H : sgraph) (i : G ≃ H) : subcubic G -> subcubic H.
Proof. by move=> h y; rewrite -[y](bijK' i) diso_degree. Qed.

End DisoSubcubic.

(** Girth ≥ [g]: every GENUINE cycle (size > 2; in a simple graph every cycle has
    size ≥ 3) has length ≥ [g].  The [2 < size c] guard is load-bearing — without
    it the empty/size-2 [ucycle] artefacts would make [girth_geq] unsatisfiable for
    [g ≥ 3].  Acyclic graphs satisfy it for all [g]. *)
Definition girth_geq (G : sgraph) (g : nat) : Prop :=
  forall c : seq G, ucycle (--) c -> 2 < size c -> g <= size c.

(** ** Homomorphisms, cores, and products (U3 surface)

    A [graph homomorphism] is an adjacency-preserving vertex map; [homs_to] is the
    existence of one; a [core] is a graph all of whose endomorphisms are bijective
    (for finite graphs, automorphisms).  The cartesian (box) product [□] is promoted
    here from hamiltonicity-theory/U2 (used by prisms); the tensor / direct /
    categorical product [×] is the product Hedetniemi's conjecture is about. *)

Definition is_hom (G H : sgraph) (f : G -> H) : Prop := forall x y : G, x -- y -> f x -- f y.
Definition homs_to (G H : sgraph) : Prop := exists f : G -> H, is_hom f.
Definition is_core (G : sgraph) : Prop := forall f : G -> G, is_hom f -> bijective f.

(** Cartesian (box) product G □ H. *)
Definition box_rel (G H : sgraph) : rel (G * H) :=
  fun p q => ((p.1 == q.1) && (p.2 -- q.2)) || ((p.2 == q.2) && (p.1 -- q.1)).
Lemma box_sym (G H : sgraph) : symmetric (@box_rel G H).
Proof.
by move=> p q; rewrite /box_rel ![p.1 == q.1]eq_sym ![p.2 == q.2]eq_sym
   ![p.1 -- q.1]sg_sym' ![p.2 -- q.2]sg_sym'.
Qed.
Lemma box_irrefl (G H : sgraph) : irreflexive (@box_rel G H).
Proof. by move=> p; rewrite /box_rel !eqxx /= !sg_irrefl. Qed.
Definition cartesian_product (G H : sgraph) : sgraph := SGraph (@box_sym G H) (@box_irrefl G H).

(** Tensor / direct / categorical product G × H (the product in Hedetniemi's conjecture). *)
Definition tensor_rel (G H : sgraph) : rel (G * H) :=
  fun p q => (p.1 -- q.1) && (p.2 -- q.2).
Lemma tensor_sym (G H : sgraph) : symmetric (@tensor_rel G H).
Proof. by move=> p q; rewrite /tensor_rel ![p.1 -- q.1]sg_sym' ![p.2 -- q.2]sg_sym'. Qed.
Lemma tensor_irrefl (G H : sgraph) : irreflexive (@tensor_rel G H).
Proof. by move=> p; rewrite /tensor_rel !sg_irrefl. Qed.
Definition tensor_product (G H : sgraph) : sgraph := SGraph (@tensor_sym G H) (@tensor_irrefl G H).

(** ** Powers, subdivisions, fractional powers

    Pure, colouring-free [sgraph] constructions, promoted here because both
    chromatic-theory/U1 (fractional powers) and homomorphism-theory/U3 (frac-3/3-power)
    use them.  [graph_power G m] = the m-th power (distinct vertices at distance ≤ m
    adjacent); [subdivision G n] = the n-subdivision (n−1 internal vertices per edge);
    [frac_power G m n] = G^{m/n} = (G^{1/n})^m.  NB: [subdivision G n] degenerates for
    [n ≤ 1] (the meaningful regime is [n ≥ 2]); callers guard accordingly. *)
Section Power.
Variables (G : sgraph) (m : nat).
Fixpoint ball (k : nat) (x : G) : {set G} :=
  if k is k'.+1 then ball k' x :|: \bigcup_(z in ball k' x) N(z) else [set x].
Definition reach_le (x y : G) : bool := y \in ball m x.
Definition pow_rel : rel G := fun x y => (x != y) && (reach_le x y || reach_le y x).
Lemma pow_sym : symmetric pow_rel.
Proof. by move=> x y; rewrite /pow_rel eq_sym orbC. Qed.
Lemma pow_irrefl : irreflexive pow_rel.
Proof. by move=> x; rewrite /pow_rel eqxx. Qed.
Definition graph_power : sgraph := SGraph pow_sym pow_irrefl.
End Power.

Section Subdivision.
Variables (G : sgraph) (n : nat).
Definition oedge (p : G * G) : bool := (p.1 -- p.2) && (enum_rank p.1 < enum_rank p.2)%N.
Local Notation EdgeT := {p : G * G | oedge p}.
Definition lo (e : EdgeT) : G := (val e).1.
Definition hi (e : EdgeT) : G := (val e).2.
Definition SubVert : Type := (G + (EdgeT * 'I_n.-1))%type.
Definition sub_r0 (x y : SubVert) : bool :=
  match x, y with
  | inl _, inl _ => false
  | inl a, inr (e, i) => ((a == lo e) && (val i == 0)) || ((a == hi e) && (val i == n.-1.-1))
  | inr _, inl _ => false
  | inr (e, i), inr (e', j) => (e == e') && ((val i).+1 == val j)
  end.
Definition sub_rel (x y : SubVert) : bool := sub_r0 x y || sub_r0 y x.
Lemma sub_sym : symmetric sub_rel.
Proof. by move=> x y; rewrite /sub_rel orbC. Qed.
Lemma sub_irrefl : irreflexive sub_rel.
Proof. move=> x; rewrite /sub_rel orbb; case: x => [a|[e i]] //=. by rewrite eqxx /= (gtn_eqF (ltnSn _)). Qed.
Definition subdivision : sgraph := SGraph sub_sym sub_irrefl.
End Subdivision.

Definition frac_power (G : sgraph) (m n : nat) : sgraph := graph_power (subdivision G n) m.

(** ** List colouring / choosability (promoted from chromatic-theory/U4)

    The vertex list-colouring surface, reusable across colouring milestones (U4 list, U5
    edge/total via the line-graph, U8 χ-boundedness). [list_colourable L] = a proper colouring
    exists picking each vertex's colour from its list [L] (over an ARBITRARY finite palette [C],
    quantified per use — no fixed colour universe); [choosable G k] = L-colourable for every list
    assignment with all lists of size ≥ k; [is_choice_number G m] = the choice number ch(G),
    stated relationally (least k with k-choosability) to stay proof-free. *)
Definition list_colourable (G : sgraph) (C : finType) (L : G -> {set C}) : Prop :=
  exists f : G -> C,
    (forall v : G, f v \in L v) /\ (forall x y : G, x -- y -> f x != f y).
(** [list_colourable_on L W]: the vertices of [W] (ONLY) can be properly coloured
    from their lists.  The colouring is PARTIAL — [f : G -> option C], required to
    be [Some c ∈ L v] on [W] and left free ([None]) off [W] — so it does NOT force
    a total function into the palette.  This keeps [W = set0] (equivalently the
    [t = 0] corner) vacuously TRUE even over an empty palette [C := 'I_0], where a
    total [G -> C] would spuriously fail to exist. *)
Definition list_colourable_on (G : sgraph) (C : finType) (L : G -> {set C}) (W : {set G}) : Prop :=
  exists f : G -> option C,
    (forall v : G, v \in W -> exists c, f v = Some c /\ c \in L v) /\
    (forall x y : G, x \in W -> y \in W -> x -- y -> f x != f y).
Definition choosable (G : sgraph) (k : nat) : Prop :=
  forall (C : finType) (L : G -> {set C}),
    (forall v : G, k <= #|L v|) -> list_colourable L.
Definition is_choice_number (G : sgraph) (m : nat) : Prop :=
  choosable G m /\ (forall k, choosable G k -> m <= k).

(** ** Edge & total colouring via the line / total graph (promoted from U4)

    The line graph L(G) and total graph T(G) of a loopless multigraph, reducing edge-
    and total-colouring to VERTEX colouring of these sgraphs: a proper k-edge-colouring of
    G is a proper k-vertex-colouring of [line_graph G], so the chromatic index χ'(G) =
    χ(L(G)) and the total chromatic number χ''(G) = χ(T(G)).  Shared by U5 (edge/total
    colouring) and later cycle/matching material. *)

(** A loopless multigraph: no edge joins a vertex to itself. *)
Definition loopless (G : mgraph) : Prop := forall e : edge G, source e != target e.

(** Line graph L(G): vertices = edges of G, two distinct edges adjacent iff they share an
    endpoint (parallel edges share both, hence adjacent — the correct multigraph line graph). *)
Definition share_endpoint (G : mgraph) (e1 e2 : edge G) : bool :=
  [exists v : G, incident v e1 && incident v e2].
Definition line_rel (G : mgraph) : rel (edge G) :=
  fun e1 e2 => (e1 != e2) && @share_endpoint G e1 e2.
Lemma line_rel_sym (G : mgraph) : symmetric (@line_rel G).
Proof.
move=> e1 e2; rewrite /line_rel eq_sym; congr (_ && _).
by apply/existsP/existsP=> -[v Hv]; exists v; rewrite andbC.
Qed.
Lemma line_rel_irrefl (G : mgraph) : irreflexive (@line_rel G).
Proof. by move=> e; rewrite /line_rel eqxx. Qed.
Definition line_graph (G : mgraph) : sgraph := SGraph (@line_rel_sym G) (@line_rel_irrefl G).

(** Total graph T(G): vertices = V(G) ⊎ E(G); vertex–vertex adjacent iff joined by an edge,
    edge–edge iff sharing an endpoint, vertex–edge iff incident. *)
Definition madj (G : mgraph) (x y : G) : bool :=
  (x != y) && [exists e : edge G, incident x e && incident y e].
Definition total_rel (G : mgraph) : rel (G + edge G)%type :=
  fun a b =>
    match a, b with
    | inl x, inl y => @madj G x y
    | inr e, inr f => @line_rel G e f
    | inl x, inr e => incident x e
    | inr e, inl x => incident x e
    end.
Lemma total_rel_sym (G : mgraph) : symmetric (@total_rel G).
Proof.
move=> [x|e] [y|f] //=.
- rewrite /madj eq_sym; congr (_ && _).
  by apply/existsP/existsP=> -[w Hw]; exists w; rewrite andbC.
- by rewrite line_rel_sym.
Qed.
Lemma total_rel_irrefl (G : mgraph) : irreflexive (@total_rel G).
Proof. by move=> [x|e] /=; [rewrite /madj eqxx | rewrite line_rel_irrefl]. Qed.
Definition total_graph (G : mgraph) : sgraph := SGraph (@total_rel_sym G) (@total_rel_irrefl G).

(** χ'(G) = chromatic index = χ(L(G)); χ''(G) = total chromatic number = χ(T(G)). *)
Definition chromatic_index (G : mgraph) : nat := χ([set: line_graph G]).
Definition total_chromatic_number (G : mgraph) : nat := χ([set: total_graph G]).

(** k-edge-colourable = the line graph is k-vertex-colourable; likewise for total colouring. *)
Definition edge_colourable (G : mgraph) (k : nat) : Prop := chromatic_index G <= k.
Definition total_colourable (G : mgraph) (k : nat) : Prop := total_chromatic_number G <= k.

(** Multigraph maximum degree (parallel edges counted) — distinct from the sgraph [Delta].
    Promoted from chromatic-theory U4 ∩ U5. *)
Definition mDelta (G : mgraph) : nat := \max_(v : G) #|edges_at v|.

(** Multigraph INCIDENCE regularity: every vertex lies on exactly [r] edges, counted by incidence
    ([#|edges_at v|]), so a loop at [v] counts once and parallel edges count separately.  [mcubic G] is
    the case [r = 3] and carries no loopless guard: three loops at one vertex form an [mcubic] graph.
    [loopless_cubic G] adds the guard.  Under it, incidence degree equals the arc-end degree that counts a
    loop twice (Cycle's [mdeg], via [Cycle.foundations.connectivity.mdeg_loopless]); that is how the guarded
    Cycle contract is bridged, without a Cycle import here.  A multigraph without vertices is regular for
    every [r] ([mregular_void]).  Registry: meta/library_primitives/multigraph-regularity.json (A13). *)
Definition mregular (G : mgraph) (r : nat) : Prop := forall v : G, #|edges_at v| = r.

Definition mcubic (G : mgraph) : Prop := mregular G 3.

Definition loopless_cubic (G : mgraph) : Prop := loopless G /\ mcubic G.

Lemma mregular_void (G : mgraph) (r : nat) : #|G| = 0 -> mregular G r.
Proof. by move=> h v; move: (card0_eq h v); rewrite !inE. Qed.

(** With a vertex, the degree of a regular multigraph is unique and is its maximum degree. *)
Lemma mregular_uniq (G : mgraph) (r r' : nat) (v : G) : mregular G r -> mregular G r' -> r = r'.
Proof. by move=> h h'; rewrite -(h v) (h' v). Qed.

Lemma mregular_mDelta (G : mgraph) (r : nat) (v : G) : mregular G r -> mDelta G = r.
Proof.
move=> h; apply/eqP; rewrite eqn_leq; apply/andP; split.
  by apply/bigmax_leqP => x _; rewrite h.
by rewrite -(h v); exact: leq_bigmax.
Qed.

Lemma loopless_cubic_mcubic (G : mgraph) : loopless_cubic G -> mcubic G.
Proof. by case. Qed.

(** Incidence regularity is invariant under any vertex bijection and edge bijection that preserve
    incidence (in particular under multigraph isomorphisms; upstream [mgraph.iso] needs edge labels with
    an [elabelType] structure, which the [unit] labels of [mgraph] lack). *)
Lemma mregular_bij (F G : mgraph) (f : F -> G) (g : edge F -> edge G) (r : nat) :
  bijective f -> bijective g -> (forall (x : F) (e : edge F), incident (f x) (g e) = incident x e) ->
  mregular F r -> mregular G r.
Proof.
case=> f' ff' f'f [g' gg' g'g] inc hF y; rewrite -(f'f y).
have -> : edges_at (f (f' y)) = [set g e | e in edges_at (f' y)].
  apply/setP => e; apply/idP/imsetP => [he|[e0 he0 ->]]; last by move: he0; rewrite !inE inc.
  by exists (g' e); [move: he; rewrite !inE -{1}(g'g e) inc | rewrite g'g].
by rewrite card_imset ?hF //; exact: (can_inj gg').
Qed.

(** ** Connectivity & structural predicates (promoted across areas)

    [k_connected] (Whitney form, from U2/U3/U9), [triangle_free] (from U3/U9), and [uwalk] —
    an UNDIRECTED multigraph walk traversing each edge in either direction, fixing the
    source→target bias of coq-graph-theory's [walk] (from U9; cycle-theory connectivity reuses it). *)

(** k-connectivity: more than k vertices, and deleting any fewer than k leaves it connected.
    Uses [ [set: G] :\: S ] (= [~: S]) — the form U2/U9 already use. *)
Definition k_connected (G : sgraph) (k : nat) : Prop :=
  (k < #|G|) /\ forall S : {set G}, #|S| < k -> connected ([set: G] :\: S).

(** Consistency of the Whitney form at [k = 1]: 1-connected = at least two
    vertices and connected (companion of [common.k_edge_connected1]). *)
Lemma k_connected1 (G : sgraph) :
  k_connected G 1 <-> (1 < #|G|) /\ connected [set: G].
Proof.
split=> -[cG hG]; split => //.
- by have := hG set0; rewrite cards0 setD0 => /(_ isT).
- by move=> S; rewrite ltnS leqn0 cards_eq0 => /eqP ->; rewrite setD0.
Qed.

(** Triangle-free: no three mutually adjacent vertices. *)
Definition triangle_free (G : sgraph) : Prop :=
  forall x y z : G, x -- y -> y -- z -> z -- x -> False.

(** Triangle-freeness is girth at least four: a triangle is exactly a [ucycle] of size 3, the only genuine
    cycle that the [2 < size c] guard of [girth_geq] leaves below size 4.  The equivalence holds on every
    simple graph (irreflexivity makes the three vertices distinct) but is not a conversion.  The three
    lemmas moved here, with their proofs, from Topological.foundations.girth, which keeps them under their
    qualified names.  Registry: meta/library_primitives/triangle-free.json (A15). *)

(** A triangle of [G] is a [ucycle] of size 3. *)
Lemma triangle_ucycle (G : sgraph) (x y z : G) :
  x -- y -> y -- z -> z -- x -> ucycle (--) [:: x; y; z].
Proof.
move=> xy yz zx; rewrite /ucycle /= xy yz zx !inE !andbT /=.
by rewrite (sg_edgeNeq xy) (sg_edgeNeq yz) eq_sym (sg_edgeNeq zx).
Qed.

(** Conversely a [ucycle] of size 3 is a triangle. *)
Lemma ucycle3_triangle (G : sgraph) (c : seq G) :
  ucycle (--) c -> size c = 3 ->
  exists x y z : G, [/\ c = [:: x; y; z], x -- y, y -- z & z -- x].
Proof.
case: c => [|x [|y [|z [|w s]]]] // /andP[] /=.
by rewrite !andbT => /andP[xy /andP[yz zx]] _ _; exists x, y, z; split.
Qed.

(** Girth at least 4 is exactly triangle-freeness. *)
Lemma girth_geq4_equiv_triangle_free (G : sgraph) :
  girth_geq G 4 <-> triangle_free G.
Proof.
split=> [g4 x y z xy yz zx|tf c uc c2].
  by move: (g4 [:: x; y; z] (triangle_ucycle xy yz zx) (isT : 2 < 3)).
have {}c2 : 3 <= size c by exact: c2.
rewrite ltn_neqAle c2 andbT eq_sym; apply/eqP => c3.
by have [x [y [z [_ xy yz zx]]]] := ucycle3_triangle uc c3; exact: (tf _ _ _ xy yz zx).
Qed.

(** Clique number of the whole graph: upstream [ω([set: G])] ([omega_mem], re-exported above) is the largest
    size of a clique.  [omega_setT_maxE] is its bigmax presentation over all cliques: on the full vertex set
    the subset filter of [cliques] always holds, so the equality is unconditional ([K_0] gives 0 on both
    sides).  No separate clique-number primitive is defined.
    Registry: meta/library_primitives/clique-number.json (A16). *)
Lemma omega_setT_maxE (G : sgraph) : ω([set: G]) = \max_(S : {set G} | cliqueb S) #|S|.
Proof.
apply: eq_bigl => S; rewrite inE; case: (cliqueb S); rewrite ?andbT ?andbF //.
by apply/subsetP => x _; rewrite !inE.
Qed.

(** Undirected walk in a loopless multigraph: each edge traversed in EITHER direction. *)
Fixpoint uwalk (G : mgraph) (x y : G) (w : seq (edge G)) {struct w} : bool :=
  match w with
  | [::] => x == y
  | e :: w' =>
      ((source e == x) && uwalk (target e) y w') ||
      ((target e == x) && uwalk (source e) y w')
  end.

(** ** Degeneracy, average degree, exact girth (promoted across areas)

    [k_degenerate]/[k_degenerate_on] (from topological/U13 ∩ graph-theory-misc/U13),
    [average_degree_geq G a b] = avg degree ≥ a/b via the handshake sum of degrees
    (from minor/U7 ∩ graph-theory-misc/U13; note Σ_v #|N(v)| = 2|E|), and [has_girth] = exact
    girth (girth ≥ g AND a genuine g-cycle), the companion of [girth_geq] (from graph-theory-misc/U13). *)

(** [G] is k-degenerate on [W]: every nonempty subset of [W] has a vertex of W-degree ≤ k. *)
Definition k_degenerate_on (G : sgraph) (W : {set G}) (k : nat) : Prop :=
  forall S : {set G}, S \subset W -> S != set0 -> exists x, (x \in S) /\ #|N(x) :&: S| <= k.
Arguments k_degenerate_on {G} W k.
(** Whole-graph k-degeneracy (= k-degeneracy on the full vertex set). *)
Definition k_degenerate (G : sgraph) (k : nat) : Prop :=
  k_degenerate_on [set: G] k.

(** Average degree ≥ a/b (cross-multiplied over ℕ; Σ_v #|N(v)| = 2|E|). *)
Definition average_degree_geq (G : sgraph) (a b : nat) : Prop :=
  a * #|G| <= b * (\sum_(v in G) #|N(v)|).

(** Exact girth g: girth ≥ g and a genuine g-cycle exists. *)
Definition has_girth (G : sgraph) (g : nat) : Prop :=
  girth_geq G g /\ (exists c : seq G, ucycle (--) c /\ 2 < size c /\ size c = g).

(** ** Combinatorial planarity (Wagner's theorem) — the G2-lite façade

    [wagner_planar G]: the finite simple graph G has NEITHER K5 NOR K3,3 as a minor. By Wagner's
    theorem this is EXACTLY planarity, so it is a statement-faithful planarity predicate that needs
    NO coq-graph-theory-planar / coq-fourcolor (axiom-free). Use this to state any conjecture whose
    hypothesis is just "G is a planar graph" (replacing the over-strong abstract-predicate placeholder).
    It does NOT capture a fixed embedding / faces / genus — rows about plane triangulations (faces),
    toroidal/surface embeddings, or crossing number still need the real planar layer. *)
Definition wagner_planar (G : sgraph) : Prop :=
  ~ minor G 'K_5 /\ ~ minor G (KB 3 3).

(** A minor never has more vertices than its host: a minor model assigns each
    minor-vertex a NONEMPTY, pairwise-DISJOINT branch set, so a representative
    map [H -> G] is injective.  (Promoted from topological/grounding_D3cr on its
    second consumer, graph-theory-misc/D7.) *)
Lemma minor_card (G H : sgraph) : minor G H -> #|H| <= #|G|.
Proof.
case=> phi mm.
have [ne _ disj _] := minor_rmap_map mm.
set psi := (fun x : H => [set y | phi y == Some x]) in ne disj *.
case: (set_0Vmem [set: H]) => [HE|[x0 _]].
  by rewrite -cardsT HE cards0.
have [w0 _] : exists z : G, z \in psi x0 by apply/set0Pn; exact: ne x0.
pose g (x : H) : G := oapp idfun w0 [pick z in psi x].
have gP : forall x, g x \in psi x.
  move=> x; rewrite /g; case: pickP => [z zP|e]; first exact: zP.
  by case/set0Pn: (ne x) => z; rewrite (e z).
have ginj : injective g.
  move=> x y exy; apply/eqP; apply: contraT => xy.
  have D := disj x y xy.
  have : g y \in psi x :&: psi y by rewrite inE -{1}exy !gP.
  by rewrite (disjoint_setI0 D) inE.
exact: leq_card ginj.
Qed.

(** ** Bipartiteness and the cycle family (cross-area finite invariants) *)

(** Bipartite: a 2-colouring with no monochromatic edge. *)
Definition bipartite (G : sgraph) : Prop := exists f : G -> bool, forall x y : G, x -- y -> f x != f y.

Lemma bipartite_relationE (G : sgraph) :
  bipartite_relation (@edge_rel G) = bipartite G.
Proof. by []. Qed.

(** The cycle C_n on ['I_n] (promoted from homomorphism/U3; reused by extremal D2). *)
Section CycleGraph.
Variable n : nat.
Definition cyc_rel (i j : 'I_n) : bool :=
  (i != j) && (((val i).+1 %% n == val j) || ((val j).+1 %% n == val i)).
Lemma cyc_sym : symmetric cyc_rel.
Proof. by move=> i j; rewrite /cyc_rel eq_sym orbC. Qed.
Lemma cyc_irrefl : irreflexive cyc_rel.
Proof. by move=> i; rewrite /cyc_rel eqxx. Qed.
Definition cycle_graph : sgraph := SGraph cyc_sym cyc_irrefl.
End CycleGraph.

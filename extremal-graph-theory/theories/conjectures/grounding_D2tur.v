(** * Extremal.conjectures.grounding_D2tur — grounding lemmas for milestone D2tur.

    SIMPLE, Qed-closed sanity results validating the new primitives introduced in
    [D2tur.v].  For each new definition we record a SATISFIABLE witness (the primitive is
    inhabited / non-vacuous) and at least one textbook identity it must satisfy.  These
    are statement-validation lemmas, not the (open) conjectures themselves.

    Witness carriers are the small complete graphs ['K_0], ['K_1], ['K_2] and the singleton
    ordinal vertex type ['I_1], which make the degenerate/boundary cases computable while
    still exercising the definitional content (edge counting, spanning trees, Hamiltonian
    paths, family-freeness, increasing-label paths, bipartitions, homomorphism counts,
    clique counts, minor-freeness).

    Coverage by primitive:
    - [oedges] / [edge_count]: [oedges_K0], [edge_count_K0] (witnesses) and the textbook
      doubling identity [oedges_double] : [oedges G = 2 * edge_count G] (each undirected
      edge is two ordered pairs; [edge_count] reuses base's [oedge]);
    - [all_pairs]: [all_pairs_irrefl], [all_pairs_mem];
    - [tree_on]: [tree_on_I1] (witness), [tree_on_sub] (identity);
    - [tree_weight]: [tree_weight_set0];
    - [shortest_tree_on]: [shortest_tree_on_I1] (witness), [shortest_tree_on_tree];
    - [greedy_decomp]: [greedy_decomp0] (the empty decomposition is greedy);
    - [ham_path_edges]: [ham_path_edges_I1];
    - [family_free]: [family_free_empty] (witness), [family_free_singleton];
    - [is_turan_number]: [is_turan_number_empty] (ex(0,F)=0, exercising maximality);
    - [incr_path]: [incr_path_K2] (a genuine increasing edge between ord0 and ord1) and
      the boundary identity [incr_path_nil];
    - [good_edge_labeling]: [good_edge_labeling_K0];
    - [proper_subgraph]: [proper_subgraph_K0_K1];
    - [gel_critical]: [gel_critical_not_gel], [gel_critical_proper] (projections; a genuine
      critical-graph witness is a deep object, deferred to applications);
    - [bipartite]: [bipartite_K2] (the canonical bipartite K_2), [bipartite_K1],
      [bipartite_edgeless];
    - [hom_count]: [hom_count_self_ge1] (the identity map is a homomorphism) and
      [hom_count_reflects_is_hom] (the counted bool reflects base's [is_hom]);
    - [clique_count]: [clique_count_gt0] (a graph with a vertex has a clique),
      [clique_count_K0];
    - [Kt_minor_free]: [Kt_minor_free_K0_1] ([K_0] has no [K_1] minor);
    - [spanning_tree_count]: [spanning_tree_count_K0] (= 1, the empty tree);
    - [is_alpha]: [is_alpha_1_0] (alpha(1) = 0 via [K_0]). *)

From GTBase Require Import base.
From GraphTheory Require Import digraph sgraph minor.
From Extremal.conjectures Require Import D2tur.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A pair-set over a vertexless graph is empty.  Used to compute the counting
    primitives on ['K_0]. *)
Lemma card_emptyG (G : sgraph) (P : pred (G * G)) :
  #|G| = 0 -> #|[set p : G * G | P p]| = 0.
Proof. move=> H0; apply: eq_card0 => p; rewrite inE; move: (H0); by rewrite (cardD1 p.1). Qed.

(** ** [oedges] / [edge_count] — textbook doubling identity [oedges G = 2 * edge_count G]:
    the ordered-pair count is twice the (base-[oedge]) undirected edge count.  The swap
    [(x,y) |-> (y,x)] is an involution pairing the [enum_rank]-increasing oriented edges
    with the decreasing ones, and adjacency is irreflexive so the two halves are disjoint. *)
Lemma oedges_double (G : sgraph) : oedges G = 2 * edge_count G.
Proof.
rewrite /oedges /edge_count.
have -> : GTBase.common.edge_count G = #|[set p : G * G | oedge p]|.
  by rewrite -GTBase.common.edge_count_rank.
pose sw := fun p : G * G => (p.2, p.1).
have sw_inj : injective sw by move=> [a b] [c d] [] -> ->.
have swA : [set p : G * G | p.1 -- p.2] = [set p | oedge p] :|: sw @: [set p | oedge p].
  apply/setP => p; rewrite !inE.
  apply/idP/idP.
  - move=> adp.
    have ne : p.1 != p.2 by apply: contraTneq adp => ->; rewrite sgP.
    have rne : enum_rank p.1 != enum_rank p.2 by rewrite (inj_eq enum_rank_inj).
    case: (ltngtP (enum_rank p.1) (enum_rank p.2)) => [lt|gt|eq].
    + by apply/orP; left; rewrite /oedge adp lt.
    + apply/orP; right; apply/imsetP; exists (sw p); last by case: p {adp ne rne gt}.
      by rewrite inE /oedge /sw /= sg_sym adp gt.
    + by move: rne; rewrite (val_inj eq) eqxx.
  - move=> /orP[op | /imsetP[q] Hq ->].
    + by move: op; rewrite /oedge => /andP[].
    + by move: Hq; rewrite inE /oedge /sw /= => /andP[adq _]; rewrite sg_sym.
rewrite swA cardsU.
have -> : [set p : G * G | oedge p] :&: sw @: [set p | oedge p] = set0.
  apply/setP => p; rewrite !inE.
  apply/negbTE/negP => /andP[op /imsetP[q] Hq eqp].
  move: op; rewrite eqp; move: Hq; rewrite inE /oedge /sw /=.
  by move=> /andP[_ gt] /andP[_ lt]; move: (ltn_trans lt gt); rewrite ltnn.
by rewrite cards0 subn0 (card_imset _ sw_inj) addnn -mul2n.
Qed.

(** Boundary witnesses on the vertexless graph. *)
Lemma oedges_K0 : oedges 'K_0 = 0.
Proof. by apply: card_emptyG; rewrite card_ord. Qed.

Lemma edge_count_K0 : edge_count 'K_0 = 0.
Proof. exact: GTBase.common.edge_count_Kn 0. Qed.

(** ** [all_pairs] — irreflexive (no loop) and contains every distinct pair. *)
Lemma all_pairs_irrefl (V : finType) (x : V) : (x, x) \notin all_pairs V.
Proof. by rewrite inE /= eqxx. Qed.

Lemma all_pairs_mem (V : finType) (x y : V) : x != y -> (x, y) \in all_pairs V.
Proof. by move=> xy; rewrite inE. Qed.

(** ** [tree_on] — witness: the empty edge set is a spanning tree of the 1-vertex graph
    (|V|-1 = 0 edges, the single vertex is trivially connected to itself). *)
Lemma tree_on_I1 : tree_on (all_pairs 'I_1) (set0 : {set 'I_1 * 'I_1}).
Proof.
rewrite /tree_on; apply/and5P; split.
- exact: sub0set.
- by apply/forallP => p; rewrite !in_set0.
- by apply/forallP => x; rewrite in_set0.
- by apply/forallP => x; apply/forallP => y; rewrite (ord1 x) (ord1 y); exact: connect0.
- by rewrite cards0 card_ord.
Qed.

(** Identity: a spanning tree is drawn from the available edge set. *)
Lemma tree_on_sub (V : finType) (A E : {set V * V}) : tree_on A E -> E \subset A.
Proof. by move=> /and5P[]. Qed.

(** ** [tree_weight] — the empty tree has weight 0. *)
Lemma tree_weight_set0 (V : finType) (w : V -> V -> nat) :
  tree_weight w (set0 : {set V * V}) = 0.
Proof. by rewrite /tree_weight big_set0. Qed.

(** ** [shortest_tree_on] — witness: on the 1-vertex graph the empty tree (weight 0) is a
    minimum-weight spanning tree. *)
Lemma shortest_tree_on_I1 (w : 'I_1 -> 'I_1 -> nat) :
  shortest_tree_on w (all_pairs 'I_1) (set0 : {set 'I_1 * 'I_1}).
Proof. split; first exact: tree_on_I1. by move=> E' _; rewrite tree_weight_set0. Qed.

(** Identity: a shortest spanning tree is in particular a spanning tree. *)
Lemma shortest_tree_on_tree (V : finType) (w : V -> V -> nat) (A E : {set V * V}) :
  shortest_tree_on w A E -> tree_on A E.
Proof. by case. Qed.

(** ** [greedy_decomp] — witness: the empty (length-0) decomposition is greedy. *)
Lemma greedy_decomp0 (V : finType) (w : V -> V -> nat) (D : nat -> {set V * V}) :
  greedy_decomp w D 0.
Proof. by move=> i; rewrite ltn0. Qed.

(** ** [ham_path_edges] — witness: the 1-vertex graph has a (length-1) Hamiltonian path in
    any edge set (the empty walk visits the unique vertex). *)
Lemma ham_path_edges_I1 (E : {set 'I_1 * 'I_1}) : ham_path_edges E.
Proof. by exists ord0, [::]; split=> //; rewrite /= card_ord. Qed.

(** ** [family_free] — witness: every graph is free of the empty family. *)
Lemma family_free_empty (G : sgraph) (Fam : 'I_0 -> sgraph) : family_free G Fam.
Proof. by move=> []. Qed.

(** Identity: freeness from the singleton family {F} is just non-containment of F. *)
Lemma family_free_singleton (G F : sgraph) :
  ~ subgraph F G -> family_free G (fun _ : 'I_1 => F).
Proof. by move=> H i. Qed.

(** ** [is_turan_number] — witness/identity: ex(0, F) = 0 for the empty family, exercising
    both the extremal-graph existence and the maximality clause (every 0-vertex graph is
    edgeless). *)
Lemma is_turan_number_empty : is_turan_number 0 (fun _ : 'I_0 => 'K_0) 0.
Proof.
split.
- exists 'K_0; split; [by rewrite card_ord | exact: edge_count_K0 | exact: family_free_empty].
- move=> m' [G [Hc Hm _]].
  by rewrite -Hm /edge_count -GTBase.common.edge_count_rank (@card_emptyG G (@oedge G) Hc).
Qed.

(** ** [incr_path] — boundary identity: the empty path is never an increasing path. *)
Lemma incr_path_nil (G : sgraph) (l : G -> G -> nat) (u v : G) :
  ~~ incr_path l u v [::].
Proof. by apply/negP => /and5P[_ _ _ _ H]; rewrite eqxx in H. Qed.

Local Notation o1 := (Ordinal (isT : 1 < 2)).

(** Witness: in ['K_2] the single edge ord0 -- ord1 is an increasing-label path. *)
Lemma incr_path_K2 : incr_path (G := 'K_2) (fun _ _ => 0) ord0 o1 [:: o1].
Proof. by rewrite /incr_path /= /edge_rel /=. Qed.

(** ** [good_edge_labeling] — witness: the vertexless graph is good-edge-labelable (all
    quantifiers over its vertices/edges are vacuous). *)
Lemma good_edge_labeling_K0 : good_edge_labeling 'K_0.
Proof. exists (fun _ _ => 0); split; by move=> []. Qed.

(** ** [proper_subgraph] — witness: ['K_0] is a proper subgraph of ['K_1] (the empty graph
    embeds, but a 1-vertex graph cannot embed into the vertexless graph). *)
Lemma proper_subgraph_K0_K1 : proper_subgraph 'K_0 'K_1.
Proof.
split.
- by exists (fun _ : 'K_0 => ord0 : 'K_1); move=> [].
- by move=> [h _ _]; case: (h ord0).
Qed.

(** ** [gel_critical] — structural identities (projections).  A genuine critical-graph
    witness requires the actual good-edge-labeling theory and is deferred. *)
Lemma gel_critical_not_gel (G : sgraph) :
  gel_critical G -> ~ good_edge_labeling G.
Proof. by case. Qed.

Lemma gel_critical_proper (G : sgraph) :
  gel_critical G -> forall H : sgraph, proper_subgraph H G -> good_edge_labeling H.
Proof. by case. Qed.

(** ** [bipartite] — identity: an edgeless graph is bipartite. *)
Lemma bipartite_edgeless (G : sgraph) :
  (forall x y : G, ~~ x -- y) -> bipartite G.
Proof. by move=> H; exists (fun _ : G => false) => x y xy; move: (H x y); rewrite xy. Qed.

(** Witness (degenerate): the 1-vertex graph is bipartite. *)
Lemma bipartite_K1 : bipartite 'K_1.
Proof. by apply: bipartite_edgeless => x y; rewrite (ord1 x) (ord1 y) sgP. Qed.

(** In ['I_2], the only vertex other than ord0 is ord1. *)
Lemma I2_eq1 (x : 'I_2) : x != ord0 -> x = o1.
Proof. by case: x => -[|[|m]] mlt // _; apply: val_inj. Qed.

(** Witness (canonical): ['K_2] is bipartite, with the part [{ord0}]. *)
Lemma bipartite_K2 : bipartite 'K_2.
Proof.
exists (fun x : 'K_2 => x \in [set ord0]) => x y; rewrite /edge_rel /= !inE => xy.
by case: (x =P ord0) xy => [->|/eqP /I2_eq1 ->];
   case: (y =P ord0) => [->|/eqP /I2_eq1 ->] //=.
Qed.

(** ** [hom_count] — the counted boolean predicate reflects base's [is_hom] (so the count
    is exactly the number of graph homomorphisms). *)
Lemma hom_count_reflects_is_hom (H G : sgraph) (f : {ffun H -> G}) :
  reflect (is_hom f) [forall x : H, [forall y : H, (x -- y) ==> (f x -- f y)]].
Proof.
apply: (iffP idP).
- by move=> Hf x y xy; move/forallP/(_ x)/forallP/(_ y): Hf => /implyP; apply.
- by move=> Hf; apply/forallP=> x; apply/forallP=> y; apply/implyP=> xy; exact: Hf.
Qed.

(** Witness: the identity map is a homomorphism, so hom(H,H) >= 1. *)
Lemma hom_count_self_ge1 (H : sgraph) : 1 <= hom_count H H.
Proof.
apply/card_gt0P; exists [ffun x => x]; rewrite inE.
apply/forallP=> x; apply/forallP=> y; apply/implyP=> xy.
by rewrite !ffunE.
Qed.

(** ** [clique_count] — witness: a graph with a vertex has at least one (singleton) clique. *)
Lemma clique_count_gt0 (G : sgraph) : 0 < #|G| -> 0 < clique_count G.
Proof.
move=> /card_gt0P[x _]; apply/card_gt0P; exists [set x]; rewrite inE.
apply/andP; split; first by apply/cliqueP; exact: clique1.
by rewrite -cards_eq0 cards1.
Qed.

(** Boundary identity: the vertexless graph has no nonempty clique. *)
Lemma clique_count_K0 : clique_count 'K_0 = 0.
Proof.
apply: eq_card0 => S; rewrite !inE.
have -> : S = set0 by apply/setP => -[x]; case: x.
by rewrite eqxx andbF.
Qed.

(** ** [Kt_minor_free] — witness: the vertexless graph has no [K_1] minor (no branch set
    can cover the single vertex of [K_1]). *)
Lemma Kt_minor_free_K0_1 : Kt_minor_free 'K_0 1.
Proof. by move=> [phi [H1 _ _]]; have [x _] := H1 ord0; case: x. Qed.

(** ** [spanning_tree_count] — witness/identity: the vertexless graph has exactly one
    spanning tree (the empty edge set: 2*(0-1) = 0 ordered edges). *)
Lemma spanning_tree_count_K0 : spanning_tree_count 'K_0 = 1.
Proof.
rewrite /spanning_tree_count.
have key : forall E : {set 'K_0 * 'K_0}, E = set0.
  by move=> E; apply/setP => -[x]; case: x.
rewrite -[X in _ = X](cards1 (set0 : {set 'K_0 * 'K_0})).
apply: eq_card => E; rewrite !inE (key E) eqxx.
apply/and5P; split.
- by apply/forallP => p; rewrite in_set0.
- by apply/forallP => p; rewrite !in_set0.
- by apply/forallP; move=> [].
- by apply/forallP; move=> [].
- by rewrite cards0 card_ord.
Qed.

(** ** [is_alpha] — witness: alpha(1) = 0, realised by the vertexless graph (1 spanning
    tree, 0 vertices, vacuously minimal). *)
Lemma is_alpha_1_0 : is_alpha 1 0.
Proof.
split.
- by exists 'K_0; split; [rewrite card_ord | exact: spanning_tree_count_K0].
- by move=> k' _.
Qed.

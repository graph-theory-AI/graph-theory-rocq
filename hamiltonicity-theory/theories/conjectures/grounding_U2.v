(** * Hamilton.conjectures.grounding_U2 — grounding lemmas for milestone U2.

    SIMPLE, Qed-closed sanity results validating the new primitives introduced
    in [U2.v].  For each genuinely new definition we record a SATISFIABLE
    witness and at least one textbook identity (e.g. 'K_1 carries a Hamiltonian
    path, 'K_2 carries a Hamilton cycle, the Cayley graph on the full connection
    set is the "different vertices" relation, complete graphs are
    vertex-transitive, K_1 is not (uniquely) Hamiltonian, K_2 IS uniquely
    Hamiltonian).  These are statement-VALIDATION lemmas, not the (open)
    conjectures themselves.

    NB: rows 5, 7, 8 now state planarity via the combinatorial [wagner_planar]
    (no K5/K3,3 minor) from base — a faithful, axiom-free predicate used opaquely,
    with no extra geometric primitive to ground here; we ground the combinatorial
    primitives those rows reuse ([cartesian_product], [hamilton_decomposition_into_two],
    [edge_set], [bipartite] — base's 2-colouring form, [k_connected]).  Row 6
    (toroidal) is DONE since Wave 1: it uses the real [toroidal] from
    [Topological.foundations.embedding] (grounded there — [embedding_exists],
    genus arithmetic), so no extra grounding is needed here. *)

From GTBase Require Import base.
From mathcomp Require Import fingroup perm.
From Hamilton.conjectures Require Import U2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** [hamiltonian_path] — witness + identity.
    Witness: the single vertex of 'K_1 is a Hamiltonian path.
    Identity: the empty walk is a Hamiltonian path exactly of the empty graph. *)
Lemma ham_path_K1 : hamiltonian_path 'K_1 [:: ord0].
Proof. by rewrite /hamiltonian_path /= card_ord. Qed.

Lemma ham_path_nil (G : sgraph) : hamiltonian_path G [::] = (#|G| == 0).
Proof. by rewrite /hamiltonian_path /= eq_sym. Qed.

(** ** [hamiltonian_cycle] / [is_hamiltonian] — witness.
    The 2-cycle [ord0; ord1] is a Hamilton cycle of 'K_2, so 'K_2 is
    Hamiltonian. *)
Lemma ham_cycle_K2 : hamiltonian_cycle 'K_2 [:: @ord0 1; @Ordinal 2 1 isT].
Proof. by rewrite /hamiltonian_cycle /ucycleb /= card_ord. Qed.

Lemma is_hamiltonian_K2 : is_hamiltonian 'K_2.
Proof. by exists [:: @ord0 1; @Ordinal 2 1 isT]; exact: ham_cycle_K2. Qed.

(** ** [cycle_edges] — identity: the empty cycle realises no edge. *)
Lemma cycle_edges_nil (G : sgraph) : cycle_edges G [::] = set0.
Proof.
by rewrite /cycle_edges; apply/setP => e; rewrite !inE;
   apply/imsetP => -[x]; rewrite inE.
Qed.

(** ** [k_connected] — witness: 'K_1 is 0-connected (the vacuous separator
    clause + a nonempty vertex set). *)
Lemma k_connected_K1_0 : k_connected 'K_1 0.
Proof. by split; [rewrite card_ord | move=> S; rewrite ltn0]. Qed.

(** ** [graph_automorphism] — witness: the identity map is always an
    automorphism. *)
Lemma graph_automorphism_id (G : sgraph) : graph_automorphism (id : G -> G).
Proof. by split; [exists id | ]. Qed.

(** ** [vertex_transitive] — witness: complete graphs are vertex-transitive,
    via the transposition swapping the two chosen vertices (textbook). *)
Lemma vertex_transitive_complete n : vertex_transitive 'K_n.
Proof.
move=> x y; exists (tperm x y); split; last exact: tpermL.
split; first by exists (tperm x y); apply: tpermK.
by move=> u v; rewrite /edge_rel /= /complete_rel /= (inj_eq perm_inj).
Qed.

(** ** [bipartite] (base's 2-colouring form) — witness: 'K_2 (an edge) is
    bipartite, coloured by membership in [{ord0}]. *)
Lemma bipartite_K2 : bipartite 'K_2.
Proof.
exists (fun x : 'K_2 => x \in [set @ord0 1]) => x y.
rewrite /edge_rel /= /complete_rel /= !inE => xy.
by case: x xy => -[|[|x]] xlt //=; case: y => -[|[|y]] ylt //=.
Qed.

(** ** [cartesian_product] / [box_rel] — textbook identity: in [G □ H], two
    vertices sharing the first coordinate are adjacent iff their second
    coordinates are adjacent in H. *)
Lemma box_same_fst (G H : sgraph) (a : G) (x y : H) :
  (@edge_rel (cartesian_product G H) (a, x) (a, y)) = (x -- y).
Proof. by rewrite /edge_rel /= /box_rel !eqxx sg_irrefl andbF orbF. Qed.

(** ** [line_graph] — identity + witness.
    Identity: L('K_1) has no vertices (the edgeless graph has no edges).
    Witness: L('K_2) has a vertex (the single edge of 'K_2). *)
Lemma line_graph_K1_empty : #|line_graph 'K_1| = 0.
Proof.
rewrite card_sig; apply: eq_card0 => p; rewrite !inE.
case: p => a b; rewrite /lg_oedge /=.
by rewrite /edge_rel /= /complete_rel /= [a]ord1 [b]ord1 eqxx.
Qed.

Lemma line_graph_K2_inhab : 0 < #|line_graph 'K_2|.
Proof.
apply/card_gt0P.
have h : @lg_oedge 'K_2 (@ord0 1, @Ordinal 2 1 isT).
  by rewrite /lg_oedge /= !enum_rank_ord /=.
by exists (Sub (@ord0 1, @Ordinal 2 1 isT) h).
Qed.

(** ** [symmetric_set] — witness: the whole group is a symmetric connection
    set. *)
Lemma symmetric_set_T (gT : finGroupType) : symmetric_set [set: gT].
Proof. by move=> x; rewrite !inE. Qed.

(** ** [cayley_graph] / [cayley_rel] — textbook identity: with the full
    connection set, the Cayley graph is the complete graph on the group (two
    elements are adjacent iff they differ). *)
Lemma cayley_full (gT : finGroupType) (x y : gT) :
  @edge_rel (cayley_graph [set: gT]) x y = (x != y).
Proof. by rewrite /edge_rel /= /cayley_rel !in_setT orbT andbT. Qed.

(** ** [edge_set] — identity (edgeless) + identity (single edge).
    'K_1 has no edges; 'K_2 has exactly one edge, the whole vertex set. *)
Lemma edge_set_K1 : edge_set 'K_1 = set0.
Proof.
apply/setP => e; rewrite /edge_set sg_edge_setE !inE; apply/negbTE.
rewrite negb_exists; apply/forallP => x; rewrite negb_exists; apply/forallP => y.
rewrite negb_and; apply/orP; left.
by rewrite /edge_rel /= /complete_rel /= negbK [x]ord1 [y]ord1.
Qed.

Lemma edge_set_K2 : edge_set 'K_2 = [set [set: 'K_2]].
Proof.
apply/setP => e; rewrite /edge_set sg_edge_setE !inE; apply/existsP/eqP.
- move=> [x] /existsP[y] /andP[xy /eqP->].
  have xy' : x != y by move: xy; rewrite /edge_rel /= /complete_rel /=.
  by apply/eqP; rewrite eqEcard subsetT cardsT card_ord cards2 xy'.
- move=> ->; exists (@ord0 1); apply/existsP; exists (@Ordinal 2 1 isT).
  apply/andP; split; first by rewrite /edge_rel /= /complete_rel /=.
  by apply/eqP/setP => z; rewrite !inE; case: z => -[|[|z]] zlt.
Qed.

(** ** No Hamilton cycle in 'K_1 (a single vertex): the only size-1 closed walk
    is the self-loop [x], excluded by irreflexivity.  This grounds the negative
    side of [is_hamiltonian], [uniquely_hamiltonian] and
    [hamilton_decomposition_into_two]. *)
Lemma no_ham_cycle_K1 (c : seq 'K_1) : ~~ hamiltonian_cycle 'K_1 c.
Proof.
rewrite /hamiltonian_cycle card_ord.
case: c => [|x [|y c]] //=; first by rewrite /ucycleb /= sg_irrefl.
by rewrite andbF.
Qed.

(** ** [is_hamiltonian] — negative witness: 'K_1 is not Hamiltonian. *)
Lemma not_is_hamiltonian_K1 : ~ is_hamiltonian 'K_1.
Proof. by case=> c; apply/negP/no_ham_cycle_K1. Qed.

(** ** [uniquely_hamiltonian] — negative witness ('K_1, no Hamilton cycle) and a
    POSITIVE witness ('K_2 has a single Hamilton cycle up to its edge set). *)
Lemma not_uniquely_hamiltonian_K1 : ~ uniquely_hamiltonian 'K_1.
Proof. by case=> c [hc _]; move: hc; apply/negP/no_ham_cycle_K1. Qed.

(** Helpers: on a 2-element list the cyclic successor swaps the endpoints. *)
Lemma next_K2_fst (a b : 'K_2) : next [:: a; b] a = b.
Proof. by rewrite next_nth mem_head /= eqxx /=. Qed.

Lemma next_K2_snd (a b : 'K_2) : a != b -> next [:: a; b] b = a.
Proof.
by move=> ab; rewrite next_nth !inE eqxx orbT /= (negbTE ab) eqxx /=.
Qed.

(** Every Hamilton cycle of 'K_2 realises the same (single) edge: the whole
    vertex set.  Hence 'K_2 is uniquely Hamiltonian. *)
Lemma ham_edges_K2 (c : seq 'K_2) :
  hamiltonian_cycle 'K_2 c -> cycle_edges 'K_2 c = [set [set: 'K_2]].
Proof.
move=> /andP[/andP[_ uc] /eqP]; rewrite card_ord => sz.
move: uc; case: c sz => [|a [|b [|c0 c1]]] //= _ uc.
have ab : a != b by move: uc; rewrite inE andbT.
have setab : [set a; b] = [set: 'K_2].
  by apply/eqP; rewrite eqEcard subsetT cardsT card_ord cards2 ab.
have na := @next_K2_fst a b.
have nb := @next_K2_snd a b ab.
apply/setP => e; rewrite !inE; apply/imsetP/eqP.
- move=> [x]; rewrite inE !inE => /orP[]/eqP-> ->.
  + by rewrite na setab.
  + by rewrite nb setUC setab.
- move=> ->; exists a; first by rewrite inE mem_head.
  by rewrite na setab.
Qed.

Lemma uniquely_hamiltonian_K2 : uniquely_hamiltonian 'K_2.
Proof.
exists [:: @ord0 1; @Ordinal 2 1 isT]; split; first exact: ham_cycle_K2.
by move=> c' hc'; rewrite (ham_edges_K2 hc') (ham_edges_K2 ham_cycle_K2).
Qed.

(** ** [hamilton_decomposition_into_two] — negative witness: 'K_1 admits no
    such decomposition (it has no Hamilton cycle at all). *)
Lemma not_hamilton_decomp_K1 : ~ hamilton_decomposition_into_two 'K_1.
Proof.
by case=> c1 [c2 [hc _ _ _]]; move: hc; apply/negP/no_ham_cycle_K1.
Qed.

(** ** [wagner_planar] — inhabitation: 'K_4 is combinatorially planar (it has
    NEITHER a K5 NOR a K3,3 minor), via the [minor_card] cardinality bound
    (#|'K_5| = 5 > 4 = #|'K_4| and #|'K_3,3| = 6 > 4).  Grounds the shared
    planarity hypothesis of Rows 5, 7 and 8, otherwise unwitnessed. *)
Lemma wagner_planar_K4 : wagner_planar 'K_4.
Proof.
split => H.
- by move: (minor_card H); rewrite !card_ord.
- by move: (minor_card H); rewrite card_sum !card_ord.
Qed.

(** ** [bipartite] — guard-has-teeth: 'K_3 (an odd cycle) is NOT bipartite, so
    the bipartite hypothesis of Barnette's conjecture (Row 8) genuinely excludes
    graphs (it is not vacuously satisfiable).  Any 2-colouring of the triangle
    repeats a colour on two of the three pairwise-adjacent vertices (pigeonhole:
    3 vertices, 2 colours), contradicting the no-monochromatic-edge condition. *)
Lemma not_bipartite_K3 : ~ bipartite 'K_3.
Proof.
case=> f Hf.
have eab : (@ord0 2 : 'K_3) -- (@Ordinal 3 1 isT) by rewrite /edge_rel /= /complete_rel /=.
have ebc : (@Ordinal 3 1 isT : 'K_3) -- (@Ordinal 3 2 isT) by rewrite /edge_rel /= /complete_rel /=.
have eac : (@ord0 2 : 'K_3) -- (@Ordinal 3 2 isT) by rewrite /edge_rel /= /complete_rel /=.
move: (Hf _ _ eab) (Hf _ _ ebc) (Hf _ _ eac).
by case: (f (@ord0 2)); case: (f (@Ordinal 3 1 isT)); case: (f (@Ordinal 3 2 isT)).
Qed.

(** ** [is_hamiltonian] — independent re-encoding (Technique #3).

    The primitive [is_hamiltonian] is a SEQ / list encoding: a graph is
    Hamiltonian iff it carries a list [c] of vertices that is a uniq closed
    walk ([ucycleb (--) c], an rcons-path fold + [uniq]) visiting every vertex
    exactly once ([size c = #|G|]).

    We give a STRUCTURALLY DIFFERENT, group-theoretic characterization with no
    seq at all: a graph is Hamiltonian iff there is a permutation [sigma] of
    its vertices such that (i) every vertex is adjacent to its image
    ([forall x, x -- sigma x]) and (ii) the cyclic group [<[sigma]>] acts
    transitively on the vertices ([forall x y, exists k, (sigma ^+ k) x = y]).
    Clause (ii) is what pins down a SINGLE spanning cycle (rather than a union
    of several shorter disjoint cycles): it is a transitive-closure / orbit
    condition on the iterates of [sigma], replacing the list's [uniq] + [size]
    bookkeeping and [ucycleb]'s closed-walk fold.

    Both encodings agree on the degenerate empty graph (there [is_hamiltonian]
    holds via the empty list [[::]], and the permutation condition holds
    vacuously), so no artificial guard is needed and the equivalence is exact.

    The proof is genuinely non-trivial (NOT [by []] / reflexivity): it bridges
    the two structures in both directions.
    - seq -> perm: a uniq spanning list [c] makes [next c] a bijection (inverse
      [prev c], via [prev_next]); package it as [sigma : {perm G}]; adjacency
      from [next_cycle] on the cycle; transitivity from [fconnect_cycle] +
      [iter_findex], bridged to group powers by [permX] / [eq_iter].
    - perm -> seq: take the orbit [c := orbit sigma x0]; transitivity forces
      [order sigma x0 = #|G|] (via [fconnect_iter] + [eq_card]), giving
      [size c = #|G|] and [uniq c] ([orbit_uniq]); the closed-walk condition
      comes from [cycle_orbit] transported along [sub_cycle] using clause (i). *)
Definition is_hamiltonian_perm (G : sgraph) : Prop :=
  exists sigma : {perm G},
    (forall x : G, x -- sigma x) /\
    (forall x y : G, exists k : nat, (sigma ^+ k)%g x = y).

Lemma is_hamiltonian_permE (G : sgraph) :
  is_hamiltonian G <-> is_hamiltonian_perm G.
Proof.
split.
- (* seq -> perm *)
  case=> c /andP[/andP[Cc Uc] /eqP szc].
  have span : mem c =i predT.
    apply/(subset_cardP _)/subset_predT.
    by rewrite (card_uniqP Uc) szc.
  pose sigma : {perm G} := perm (can_inj (prev_next Uc)).
  have Es : sigma =1 next c by move=> x; rewrite permE.
  exists sigma; split.
  + move=> x; rewrite Es; apply: (next_cycle Cc); by rewrite span.
  + move=> x y.
    have Fxy : fconnect (next c) x y.
      by rewrite (fconnect_cycle (cycle_next Uc) (x:=x)) ?span // span.
    exists (findex (next c) x y).
    by rewrite permX (eq_iter Es) (iter_findex Fxy).
- (* perm -> seq *)
  case=> sigma [Hadj Htrans].
  have [n0|Hpos] := posnP #|G|.
  + exists [::]; rewrite /hamiltonian_cycle /ucycleb /=.
    by rewrite eq_sym -n0.
  + have [x0 _] : exists x : G, x \in predT.
      by apply/card_gt0P.
    pose c := orbit sigma x0.
    have Hfc : fconnect sigma x0 =i predT.
      move=> y; rewrite !inE.
      have [k Hk] := Htrans x0 y.
      by rewrite -Hk permX fconnect_iter.
    have Hord : order sigma x0 = #|G|.
      by rewrite /order (eq_card Hfc).
    exists c; rewrite /hamiltonian_cycle /ucycleb.
    have Hsz : size c = #|G| by rewrite /c size_orbit Hord.
    rewrite Hsz eqxx andbT orbit_uniq andbT.
    apply: (@sub_cycle G (coerced_frel sigma) (--)).
    * by move=> a b; rewrite /= => /eqP <-; apply: Hadj.
    * exact: (cycle_orbit (@perm_inj _ sigma) x0).
Qed.

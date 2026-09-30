(** * Digraph.conjectures.grounding_P9 — faithfulness grounding for P9

    GROUNDING (not new mathematics): small, KNOWN textbook facts that the NEW
    primitives introduced in [P9.v] must satisfy if the definitions are faithful
    encodings, together with SATISFIABILITY witnesses showing the
    Prop-valued constructions are inhabited (non-vacuous).

    Every lemma here is closed by [Qed] and (see the [Print Assumptions] audit at
    the end) axiom-free.

    Coverage (one identity and/or a satisfiable witness per new primitive):
      - [nb_arcs]            : handshake identity [nb_arcs D = \sum_v outdeg v].
      - [weakly_connected]/[tree_digraph] : [tree_digraph -> weakly_connected] and
                               the [#V-1] arc-count projection.
      - [ham]               : [ham c -> dicycle c] and [ham c -> size c = #V].
      - [cyclic_sel]        : [cyclic_sel f -> real_sel f].
      - [kstrong]/[karcstrong] : the order guards ([k < #V], [1 < #V]).
      - [arccut]            : [arccut set0 = 0], [arccut [set:] = 0].
      - [alpha]             : [~~ (v --> v) -> 0 < alpha] (independence number ≥ 1).
      - [wadj]/[nb_wcc]/[cyclomatic] : [wadj] is symmetric, [nb_wcc f <= #V],
                               [cyclomatic f <= \sum_v #|f v|].
      - [arcset_outdeg]/[arcset_indeg] : vanish on the empty arc set.
      - [single_dicycle_arcset]/[ndicycles] : nonemptiness projection and the
                               powerset bound.
      - [short_dicycle_free] : the looplessness projection AND a concrete witness
                               (every transitive tournament [TT n] is short-dicycle-free).
      - [set_partition]     : the trivial one-block partition [[:: [set:]]] is valid.
      - [arc_decomp]        : [arc_decomp fs -> all real_sel fs].
      - [contains_subdig]/[subdivides] : reflexive (every digraph contains and
                               subdivides itself), so the Prop is inhabited.
      - [oriented_tree]/[antidirected_tree] : the antidirected-⇒-tree projection.
      - [switched]/[sw_iso]/[same_deck] : [switched set0] is [D], so [sw_iso] and
                               [same_deck] are reflexive (switching equivalence is
                               an equivalence; the deck of [D] matches itself).
      - [remove_arcs]/[min_feedback] : deleting all arcs is acyclic (so the
                               feedback-arc-set argmin domain is nonempty), and the
                               [#V*#V] bound.
      - [rev_arc]           : reversing arc [a] drops [a.1 --> a.2] and inserts
                               [a.2 --> a.1].
      - [tt3]/[tt3_arcs]    : the [a-->c] projection and arc membership.
      - [underlying]/[χ] (row 18 faithfulness fix) : [χ(underlying D) <= #V]. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude digraph oriented dipath strong tournament.
From Digraph Require Import classic_core dichromatic packing colouring_variants two_extremal.
From Digraph Require Import interop_graph_theory chi_bounded subdivision P9.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Handshake: arcs counted by out-degrees *)

Lemma nb_arcs_sum_outdeg (D : diGraphType) : nb_arcs D = \sum_(v : D) outdeg v.
Proof.
rewrite /nb_arcs /outdeg -sum1dep_card.
transitivity (\sum_(v : D) \sum_(w | v --> w) 1).
- by rewrite pair_big_dep /=.
- by apply: eq_bigr => v _; rewrite sum1dep_card.
Qed.

(** ** Projections / identities at the general digraph level *)

Section EasyD.
Variable D : diGraphType.
Implicit Types (c : seq D) (f : D -> {set D}).

Lemma ham_dicycle c : ham c -> dicycle c.
Proof. by case/andP. Qed.

Lemma ham_spans c : ham c -> size c = #|D|.
Proof. by case/andP=> _ /eqP. Qed.

Lemma tree_digraph_wconn : tree_digraph D -> weakly_connected D.
Proof. by case/andP. Qed.

Lemma tree_digraph_nb_arcs : tree_digraph D -> nb_arcs D = #|D| - 1.
Proof. by case/andP=> _ /eqP. Qed.

Lemma cyclic_sel_real f : cyclic_sel f -> real_sel f.
Proof. by case/andP. Qed.

Lemma kstrong_lt (k : nat) : kstrong D k -> k < #|D|.
Proof. by case/andP. Qed.

Lemma karcstrong_card (k : nat) : karcstrong D k -> 1 < #|D|.
Proof. by case/andP. Qed.

Lemma single_dicycle_arcset_neq0 (A : {set D * D}) :
  single_dicycle_arcset A -> A != set0.
Proof. by case/and4P. Qed.

Lemma short_dicycle_free_loopless :
  short_dicycle_free D -> forall u : D, ~~ (u --> u).
Proof. by case/and3P=> /forallP H _ _ u. Qed.

Lemma cyc_arcs_fst c (p : D * D) : p \in cyc_arcs c -> p.1 \in c.
Proof. by rewrite inE => /andP[]. Qed.

Lemma wadj_sym f : symmetric (wadj f).
Proof. by move=> u w; rewrite /wadj orbC. Qed.

Lemma arccut_setT : arccut [set: D] = 0.
Proof. by apply: eq_card0 => p; rewrite inE !in_setT /=. Qed.

Lemma arccut_set0 : arccut (set0 : {set D}) = 0.
Proof. by apply: eq_card0 => p; rewrite inE in_set0. Qed.

Lemma arcset_outdeg_set0 (v : D) : arcset_outdeg set0 v = 0.
Proof. by apply: eq_card0 => w; rewrite inE in_set0. Qed.

Lemma arcset_indeg_set0 (v : D) : arcset_indeg set0 v = 0.
Proof. by apply: eq_card0 => u; rewrite inE in_set0. Qed.

Lemma arc_decomp_real (fs : seq (D -> {set D})) :
  arc_decomp fs -> all (@real_sel D) fs.
Proof. by case/andP. Qed.

(** Independence number is ≥ 1 once some vertex carries no loop (a singleton is
    then a stable set). *)
Lemma alpha_ge1 (v : D) : ~~ (v --> v) -> 0 < alpha D.
Proof.
move=> nvv.
have hs : stable [set v].
  apply/forall_inP=> x; rewrite inE => /eqP->.
  by apply/forall_inP=> y; rewrite inE => /eqP->.
by rewrite -(cards1 v); exact: leq_bigmax_cond.
Qed.

(** The one-block list [[:: [set:]]] is a genuine vertex partition. *)
Lemma set_partition_trivial : set_partition [:: [set: D]].
Proof. by apply/forallP=> v; rewrite /= in_setT. Qed.

Lemma nb_wcc_le f : nb_wcc f <= #|D|.
Proof. by rewrite /nb_wcc (leq_trans (leq_imset_card _ _)) // cardsT. Qed.

Lemma cyclomatic_le f : cyclomatic f <= \sum_(v : D) #|f v|.
Proof. by rewrite /cyclomatic leq_subLR addnC leq_add2r nb_wcc_le. Qed.

Lemma ndicycles_le : ndicycles D <= #|[set: {set D * D}]|.
Proof. by rewrite /ndicycles cardsT; apply: max_card. Qed.

Lemma min_feedback_le : min_feedback D <= #|D| * #|D|.
Proof. by rewrite /min_feedback; apply: (leq_trans (max_card _)); rewrite card_prod. Qed.

(** Deleting ALL arcs yields an acyclic digraph — so the [min_feedback] argmin
    ranges over a nonempty predicate (feedback arc sets exist). *)
Lemma remove_arcs_full_acyclic : acyclicb (remove_arcs [set: D * D]).
Proof.
apply/forallP=> v; apply/forallP=> w; apply/implyP.
by rewrite /arc /= in_setT andbF.
Qed.

(** [χ] of the underlying simple graph is ≤ the number of vertices (the row-18
    faithfulness-fix primitives [underlying] / [χ] are well-formed). *)
Lemma chi_underlying_le : χ([set: underlying D]) <= #|D|.
Proof. by rewrite (leq_trans (leq_chi _)) // cardsT. Qed.

End EasyD.

(** ** Reflexivity / inhabitation witnesses for the Prop-valued constructions *)

Lemma contains_subdig_refl (D : diGraphType) : contains_subdig D D.
Proof. by exists id; split=> //; apply: inj_id. Qed.

Lemma sw_iso_refl (D : diGraphType) : sw_iso D D.
Proof.
exists set0, id; split; first by exists id.
by move=> u v; rewrite /arc /= !in_set0.
Qed.

Lemma same_deck_refl (D : diGraphType) : same_deck D D.
Proof. by exists id; split; [exists id | move=> i; apply: sw_iso_refl]. Qed.

(** Reversing arc [a] removes the forward arc and (when [a.1 != a.2]) installs the
    backward one. *)
Lemma rev_arc_drop (D : diGraphType) (a : D * D) :
  ~~ ((a.1 : rev_arc a) --> (a.2 : rev_arc a)).
Proof. by rewrite /arc /= !eqxx. Qed.

Lemma rev_arc_added (D : diGraphType) (a : D * D) :
  a.1 != a.2 -> ((a.2 : rev_arc a) --> (a.1 : rev_arc a)).
Proof. by move=> ne; rewrite /arc /= [a.2 == a.1]eq_sym (negbTE ne) /= !eqxx. Qed.

(** Every oriented digraph subdivides itself (branch map = identity, each arc its
    own internally-empty path). *)
Lemma subdivides_refl (D : orientedDigraph) : subdivides D D.
Proof.
exists id, (fun _ v => [:: v]); split.
- exact: inj_id.
- move=> u v auv; split; last by [].
  have ne : u != v.
    apply/negP => /eqP e; subst v.
    have H : (u --> u) = false by apply: arc_asymm.
    by rewrite auv in H.
  by rewrite /dipath /= auv mem_seq1 (negbTE ne).
- by move=> u v _ x /=.
- by move=> u v u' v' _ _ _ /=.
Qed.

(** ** Tournament-level primitives: [tt3] / [tt3_arcs], short-dicycle-freeness *)

Lemma tt3_arc13 (T : tournament) (t : T * T * T) : tt3 t -> t.1.1 --> t.2.
Proof. by case/and3P. Qed.

Lemma tt3_arcs_in (T : tournament) (t : T * T * T) :
  (t.1.1, t.1.2) \in tt3_arcs t.
Proof. by rewrite !inE eqxx. Qed.

Lemma antidirected_tree_is_tree (T : orientedDigraph) :
  antidirected_tree T -> oriented_tree T.
Proof. by rewrite /antidirected_tree /oriented_tree => /andP[]. Qed.

(** Concrete witness: a transitive tournament has no directed cycle of length ≤ 3
    (it is acyclic), so [short_dicycle_free] is satisfiable. *)
Lemma TT_short_dicycle_free (n : nat) : short_dicycle_free (TT n).
Proof.
apply/and3P; split.
- by apply/forallP=> u; rewrite arcTTE ltnn.
- apply/forallP=> u; apply/forallP=> v; rewrite !arcTTE.
  by apply/negP=> /andP[uv vu]; rewrite ltnNge (ltnW uv) in vu.
- apply/forallP=> u; apply/forallP=> v; apply/forallP=> w; rewrite !arcTTE.
  apply/negP=> /and3P[uv vw wu].
  by have uw := ltn_trans uv vw; rewrite ltnNge (ltnW uw) in wu.
Qed.

(** ** Wave-E4 GUARD REPAIR grounding for row
    opg:subdivision_of_a_transitive_tournament_in_digraphs_with_large_outdegree

    The row's host now carries the guard [0 < #|D|].  Two facts justify it:
    the UNGUARDED body (spelled out below, so that nothing here refutes a
    committed row) is FALSE because the EMPTY digraph satisfies every pointwise
    out-degree requirement vacuously while admitting no injective branch map
    ([p9_subdivision_TT_unguarded_false], the wave-E3 scratch refutation
    P9_subdivision_TT_false ported); and the guarded hypothesis class is
    inhabited at every threshold by the complete digraph
    ([p9_outdeg_host_nonvacuous]). *)

Definition p9_emptyD : Type := 'I_0.
HB.instance Definition _ := Finite.on p9_emptyD.
HB.instance Definition _ := HasArc.Build p9_emptyD (fun _ _ : 'I_0 => false).

Lemma p9_emptyD_card : #|{: p9_emptyD}| = 0.
Proof. exact: card_ord. Qed.

Lemma no_subdivides_emptyD (H : diGraphType) : (0 < #|H|)%N ->
  ~ subdivides (p9_emptyD : diGraphType) H.
Proof.
move=> hH [b _]; move/card_gt0P: hH => [x _].
by case: (b x) => m; rewrite ltn0.
Qed.

Lemma p9_subdivision_TT_unguarded_false :
  ~ (exists f : nat -> nat,
       forall (k : nat) (D : diGraphType),
         (forall v : D, f k <= outdeg v) -> subdivides D (TT k : diGraphType)).
Proof.
move=> [f hf].
apply: (no_subdivides_emptyD (H := (TT 1 : diGraphType))); first by rewrite card_TT.
by apply: hf; case.
Qed.

Lemma p9_outdeg_host_nonvacuous (b : nat) :
  exists D : diGraphType, (0 < #|D|)%N /\ (forall v : D, b <= outdeg v).
Proof.
exists (dense_dg b : diGraphType); split; first by rewrite card_dense.
by move=> v; rewrite outdeg_dense.
Qed.

Print Assumptions p9_subdivision_TT_unguarded_false.
Print Assumptions p9_outdeg_host_nonvacuous.

(** ** Print Assumptions audit on representative grounded facts. *)
Print Assumptions nb_arcs_sum_outdeg.
Print Assumptions alpha_ge1.
Print Assumptions subdivides_refl.
Print Assumptions sw_iso_refl.
Print Assumptions remove_arcs_full_acyclic.
Print Assumptions rev_arc_added.
Print Assumptions chi_underlying_le.
Print Assumptions TT_short_dicycle_free.

(** ** [dipath_arcs] grounded by a concrete computation: the arc set of the
    directed path [0 -> 1] in [TT 2] is exactly the single pair [{(0,1)}]. *)
Lemma dipath_arcs_TT2 :
  dipath_arcs (Ordinal (isT : (0 < 2)%N) : TT 2) [:: Ordinal (isT : (1 < 2)%N)]
  = [set (Ordinal (isT : (0 < 2)%N), Ordinal (isT : (1 < 2)%N))].
Proof. by apply/setP=> -[u v]; rewrite /dipath_arcs !inE. Qed.

(** ** [ham] is inhabited by a concrete witness: the directed triangle
    [0 -> 1 -> 2 -> 0] is a Hamiltonian dicycle of [C3] (it is a [dicycle] and
    its length equals [#|C3|]). ([tournament.C3] is qualified because GraphTheory
    also exports an sgraph named [C3].) *)
Local Open Scope ring_scope.
Lemma ham_C3 : @ham (tournament.C3 : diGraphType) [:: 0; 1; 1 + 1].
Proof. by rewrite /ham /dicycle /= card_C3. Qed.

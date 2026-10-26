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
From Digraph Require Import cayley circulant.
From mathcomp Require Import zify.
From Stdlib Require Import Lia.

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

(** ** The non-emptiness guard of [arc_disjoint_directed_cycles_in_regular_directed_gra_statement]
    (added on 2026-10-26) is not vacuous: the directed triangle is non-empty and 1-diregular,
    so the guarded hypotheses hold together at k = 1.  The guard's teeth (the empty digraph
    refutes the unguarded body) are in
    meta/probe_hints/arc_disjoint_directed_cycles_in_regular_directed_gra_statement.v. *)
Lemma arc_disjoint_hyps_nonvacuous :
  exists D : diGraphType, (0 < #|D|)%N /\ diregular D 1%N.
Proof.
exists (tournament.C3 : diGraphType); split; first by rewrite card_C3.
apply/forallP => u; rewrite /outdeg /degree_balance.indeg; apply/andP; split; apply/eqP.
- rewrite (_ : [set w | u --> w] = [set u + 1]) ?cards1 //.
  by apply/setP => w; rewrite !inE arcC3E.
- rewrite (_ : [set w | w --> u] = [set u - 1]) ?cards1 //.
  apply/setP => w; rewrite !inE arcC3E.
  by case: u w => -[|[|[|]]] // ? [[|[|[|]]] //].
Qed.

(** ** The [loopless D] guard of [antidirected_trees_in_digraphs_statement] (added on
    2026-10-26) is not vacuous: at k = 2 the transitive tournament [TT 2] (one arc, no loop)
    is a loopless host meeting the arc bound [(2 - 2) * #|D| < nb_arcs D], and [TT 2] is also a
    two-vertex antidirected tree, so every hypothesis of the guarded body holds together.  The
    guard's teeth (a looped vertex refutes the unguarded body) are in
    meta/probe_hints/antidirected_trees_in_digraphs_statement.v. *)
Lemma TT2_antidirected_tree : antidirected_tree (TT 2).
Proof.
rewrite /antidirected_tree /tree_digraph; apply/andP; split; first (apply/andP; split).
- apply/forallP => u; apply/forallP => v.
  have [->|huv] := eqVneq u v; first exact: connect0.
  by apply: connect1; rewrite !arcTTE -neq_ltn val_eqE.
- rewrite card_TT /nb_arcs.
  apply/cards1P; exists (ord0, ord_max).
  apply/setP => -[a b]; rewrite !inE arcTTE /=.
  by case: a b => [[|[|a]] ha] [[|[|b]] hb].
- apply/forallP => -[[|[|m]] hm] //=.
  + by apply/orP; right; apply/eqP; apply: eq_card0 => u; rewrite !inE arcTTE.
  + apply/orP; left; apply/eqP; apply: eq_card0 => w; rewrite !inE arcTTE /=.
    by case: w => [[|[|w]] hw].
Qed.

Lemma antidirected_hyps_nonvacuous :
  exists (D : diGraphType) (T : orientedDigraph),
    [/\ loopless D, ((2 - 2) * #|D| < nb_arcs D)%N, antidirected_tree T & #|T| = 2%N].
Proof.
exists (TT 2 : diGraphType), (TT 2 : orientedDigraph); split.
- by move=> v; exact: arcxx.
- by rewrite mul0n; apply/card_gt0P; exists (ord0, ord_max); rewrite inE arcTTE.
- exact: TT2_antidirected_tree.
- exact: card_TT.
Qed.

(** ** The [loopless D] guard of [cyclic_spanning_subdigraph_with_small_cyclomatic_num_statement]
    (added on 2026-10-26) is not vacuous: the directed triangle is loopless and each of its
    vertices lies on its Hamiltonian dicycle ([ham_C3]), so both hypotheses of the guarded body
    hold together.  The guard's teeth (a looped vertex refutes the unguarded body) are in
    meta/probe_hints/cyclic_spanning_subdigraph_with_small_cyclomatic_num_statement.v. *)
Lemma cyclic_spanning_hyps_nonvacuous :
  exists D : diGraphType,
    loopless D /\ (forall v : D, exists c : seq D, dicycle c /\ v \in c).
Proof.
exists (tournament.C3 : diGraphType); split; first by move=> v; exact: arcxx.
move=> v; exists [:: 0; 1; 1 + 1]; split; first by case/andP: ham_C3.
by case: v => -[|[|[|]]].
Qed.

(** ** k-strong tournaments exist for every k (grounding for the partition row's guard)

    The rotational tournament [RT m'] on 'Z_n, n = 2m + 1 (m = m'.+1), has the arcs
    x -> x + 1, ..., x + m: its connection set [RTset] = {1, ..., m} hits each pair {z, -z}
    (z != 0) exactly once ([RTset_cond]).  Deleting fewer than m vertices leaves it strong
    ([RT_del_strong]): from a surviving vertex x, the first surviving vertex x + j after x in
    cyclic order is an out-neighbour, because the skipped vertices x + 1, ..., x + (j - 1) are
    deleted, so j - 1 <= #|S| < m; induction on the cyclic distance to the target closes it.
    Hence [kstrong_tournament_exists]: every k has a k-strong tournament.  It feeds both the
    teeth of the [0 < size ks] guard of [partitionning_a_tournament_into_k_strongly_connected_statement]
    (meta/probe_hints/partitionning_a_tournament_into_k_strongly_connected_statement.v) and its
    non-vacuity ([partition_hyps_nonvacuous] below). *)
Section RT.
Import GRing.Theory.
Variable m' : nat.
Local Notation m := m'.+1.
Local Notation n := (m.*2.+1).

Definition RTset : {set 'Z_n} := [set z : 'Z_n | (0 < val z <= m)%N].

Lemma RTset_cond (z : 'Z_n) : (z != 0) = (z \in RTset) (+) (- z \in RTset).
Proof.
case: (eqVneq z 0) => [->|zN0] /=; first by rewrite oppr0 addbb.
have vpos : (0 < val z)%N by rewrite lt0n -[0%N]/(val (0 : 'Z_n)) val_eqE.
have vlt : (val z < n)%N := ltn_ord z.
have voppE : val (- z) = ((n - val z) %% n)%N by [].
rewrite !inE voppE modn_small ?ltn_subrL ?vpos //.
move: (val z) vpos vlt => v vpos vlt /=.
case: (leqP v m) => hv /=.
- rewrite (_ : (0 < n - v <= m)%N = false) //.
  by apply/negbTE; rewrite negb_and -ltnNge; apply/orP; right; lia.
- by rewrite (_ : (0 < n - v <= m)%N = true) //; apply/andP; split; lia.
Qed.

(** A fresh carrier: canonical instances are keyed on the head constant, and [cayley] already
    carries the [AC] tournament instance (constructions/circulant.v). *)
Definition rt_carrier : Type := cayley RTset.
HB.instance Definition _ := Finite.on rt_carrier.
HB.instance Definition _ := HasArc.Build rt_carrier (@arc (cayley RTset)).

Fact RT_irrefl : irreflexive (arc : rel rt_carrier).
Proof.
have h1 : 1%g \notin RTset by rewrite inE.
by case: (@cayley_irreflP _ RTset) => _ /(_ h1).
Qed.

Fact RT_total (x y : rt_carrier) : (x != y) = (arc x y) (+) (arc y x).
Proof.
case: (@cayley_totalP _ RTset) => _ h; apply: h => z.
by rewrite Zp_1gE Zp_invgE RTset_cond.
Qed.

HB.instance Definition _ :=
  DiGraph_IsTournament.Build rt_carrier RT_irrefl RT_total.

Definition RT : tournament := rt_carrier.

Lemma RT_arcE (x y : RT) : (x --> y) = (y - x \in RTset).
Proof. exact: circulant_arcE. Qed.

Lemma card_RT : #|RT| = n.
Proof. exact: card_ord. Qed.

Lemma card_RTset : #|RTset| = m.
Proof.
rewrite cardsE cardE /enum_mem -enumT /= size_filter.
rewrite -(count_map val (fun v => (0 < v <= m)%N)) val_enum_ord.
have -> : (Zp_trunc n).+2 = (1 + m + m)%N by rewrite /Zp_trunc /=; lia.
rewrite iotaD iotaD !count_cat /=.
rewrite (@eq_in_count _ _ predT (iota (0 + 1).+1 m')).
  by move=> v; rewrite mem_iota => /andP [h1 h2] /=; apply/andP; split; lia.
rewrite (@eq_in_count _ _ pred0 (iota (0 + (1 + m)).+1 m')).
  by move=> v; rewrite mem_iota => /andP [h1 h2] /=; apply/negbTE; apply/negP => /andP [_ h3]; lia.
rewrite count_predT count_pred0 size_iota.
have -> : (0 + (1 + m) <= m)%N = false by apply/negbTE; rewrite -ltnNge; lia.
lia.
Qed.

Lemma val_natZn (j : nat) : (j < n)%N -> val (j%:R : 'Z_n) = j.
Proof. by move=> hj; rewrite Zp_nat /= modn_small. Qed.

Lemma RT_del_strong (S : {set RT}) : (#|S| < m)%N -> strongb (induced_digraph (~: S)).
Proof.
move=> hS; apply/strongP.
pose dist (a b : induced_digraph (~: S)) : nat := val ((val b : 'Z_n) - (val a : 'Z_n)).
suff H : forall d (a b : induced_digraph (~: S)), leq (dist a b) d -> connect arc a b.
  by move=> a b; exact: (H _ a b (leqnn _)).
elim=> [|d IH] a b hd.
  have h0 : (val b : 'Z_n) - (val a : 'Z_n) = 0.
    by apply/val_inj; move: hd; rewrite leqn0 => /eqP.
  move: h0 => /eqP; rewrite subr_eq0 => /eqP hab.
  have -> : b = a by apply/val_inj.
  exact: connect0.
case: (leqP (dist a b) d) => [hle|hgt]; first exact: IH.
have hD : dist a b = d.+1 by apply/eqP; rewrite eqn_leq hd hgt.
set x : 'Z_n := val a.
set y : 'Z_n := val b.
have hxS : (x : RT) \notin S by have := valP a; rewrite inE.
have hyS : (y : RT) \notin S by have := valP b; rewrite inE.
(* the first vertex after x, in cyclic order, that survives the deletion *)
pose P j := (0 < j)%N && ((x + j%:R : RT) \notin S).
have hPd : P d.+1.
  rewrite /P /=; have -> : x + d.+1%:R = y by rewrite -hD /dist natr_Zp addrC subrK.
  exact: hyS.
case: (ex_minnP (ex_intro P _ hPd)) => j /andP [hj0 hjS] hmin.
have hjd : (j <= d.+1)%N := hmin _ hPd.
have hDn : (d.+1 < n)%N by rewrite -hD /dist; exact: ltn_ord.
(* the skipped vertices x+1, ..., x+(j-1) are deleted, so the jump is at most m *)
have hjm : (j <= m)%N.
  rewrite leqNgt; apply/negP => hmj.
  have hsub : [set x + z | z in RTset] \subset S.
    apply/subsetP => w /imsetP [z hz ->].
    have hz' := hz; rewrite inE in hz'; case/andP: hz' => hz0 hzm.
    have hlt : (val z < j)%N by apply: (leq_ltn_trans hzm).
    have hnP : ~~ P (val z) by apply/negP => /hmin; rewrite leqNgt hlt.
    by move: hnP; rewrite /P hz0 /= natr_Zp negbK.
  have := subset_leq_card hsub.
  by rewrite (card_imset _ (addrI x)) card_RTset leqNgt hS.
have hc : (x + j%:R : RT) \in ~: S by rewrite inE.
pose c : induced_digraph (~: S) := exist _ (x + j%:R : RT) hc.
have hjn : (j < n)%N by apply: (leq_ltn_trans hjd).
have hac : a --> c.
  rewrite sub_arcE RT_arcE /= (addrC x) addrK inE val_natZn //.
  by rewrite hj0 hjm.
have e1 : y - x = d.+1%:R by rewrite -hD /dist natr_Zp.
have hcb : (dist c b <= d)%N.
  have e2 : y - (x + j%:R) = (d.+1 - j)%:R by rewrite opprD addrA e1 natrB.
  have -> : dist c b = val (y - (x + j%:R)) by [].
  have hsn : (d.+1 - j < n)%N by apply: (leq_ltn_trans (leq_subr _ _)).
  rewrite e2 (val_natZn hsn).
  lia.
exact: connect_trans (connect1 hac) (IH c b hcb).
Qed.

Lemma RT_kstrong : kstrong RT m.
Proof.
apply/andP; split; first by rewrite card_RT; lia.
by apply/forall_inP => S hS; apply: RT_del_strong.
Qed.

End RT.

(** For every k there is a k-strong tournament: the rotational tournament on 2(k+1)+1
    vertices is (k+1)-strong, hence k-strong. *)
Lemma kstrong_tournament_exists (k : nat) : exists T : tournament, kstrong T k.
Proof.
exists (RT k); apply/andP; split; first by rewrite card_RT; lia.
by apply/forall_inP => S hS; apply: RT_del_strong; apply: (ltn_trans hS).
Qed.

(** The [0 < size ks] guard of [partitionning_a_tournament_into_k_strongly_connected_statement]
    (added on 2026-10-26) is not vacuous: whatever the function g, the one-part list [:: 1] meets
    the guard and the positivity hypothesis, and some tournament is g([:: 1])-strong. *)
Lemma partition_hyps_nonvacuous (g : seq nat -> nat) :
  exists (ks : seq nat) (T : tournament),
    [/\ (0 < size ks)%N, all (fun k => 0 < k)%N ks & kstrong T (g ks)].
Proof.
have [T hT] := kstrong_tournament_exists (g [:: 1%N]).
by exists [:: 1%N], T; split.
Qed.

(** * Chromatic.conjectures.grounding_U1 — grounding lemmas for milestone U1.

    SIMPLE, Qed-closed sanity results validating the new primitives introduced
    in [U1.v]: for each new definition we record a satisfiable witness and at
    least one textbook identity (e.g. Δ('K_n.+1) = n, χ('K_n) = n,
    valency_variety('K_n.+1) = 1).  These are statement-validation lemmas, not
    the (open) conjectures themselves. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph coloring.
From Chromatic.conjectures Require Import U1.
Set SsrOldRewriteGoalsOrder.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Complete-graph helpers *)

(** In a complete graph the open neighbourhood of [x] is everything but [x]. *)
Lemma neigh_complete n (x : 'K_n) : N(x) = ~: [set x].
Proof. by apply/setP => y; rewrite !inE eq_sym. Qed.

(** Δ-ingredient: every vertex of 'K_n.+1 has degree exactly n. *)
Lemma deg_complete n (x : 'K_n.+1) : #|N(x)| = n.
Proof.
by rewrite neigh_complete (cardsCs (~: [set x])) setCK cards1 card_ord subn1.
Qed.

(** [set: 'K_n] is a clique. *)
Lemma clique_complete n : clique [set: 'K_n].
Proof. by move=> x y _ _ xy; rewrite /edge_rel /= xy. Qed.

(** ** [Delta] — textbook Δ('K_n.+1) = n. *)
Lemma Delta_complete n : Delta 'K_n.+1 = n.
Proof.
rewrite /Delta; apply/eqP; rewrite eqn_leq; apply/andP; split.
- by apply/bigmax_leqP => x _; rewrite deg_complete.
- by apply: (leq_trans _ (leq_bigmax ord0)); rewrite deg_complete.
Qed.

(** ** [regular] — witness + identity: 'K_n.+1 is n-regular. *)
Lemma regular_complete n : regular 'K_n.+1 n.
Proof. by move=> v; rewrite deg_complete. Qed.

(** ** [ceil_div] — textbook ⌈a/1⌉ = a. *)
Lemma ceil_div_1 a : ceil_div a 1 = a.
Proof. by rewrite /ceil_div addn1 subn1 /= divn1. Qed.

(** ** [common_nbr] — textbook symmetry common_nbr u v = common_nbr v u. *)
Lemma common_nbr_sym (G : sgraph) (u v : G) :
  common_nbr u v = common_nbr v u.
Proof. by rewrite /common_nbr setIC. Qed.

(** ** [chi] of a complete graph — textbook χ('K_n) = n. *)
Lemma chi_complete n : χ([set: 'K_n]) = n.
Proof.
rewrite chi_clique; first by rewrite cardsT card_ord.
exact: clique_complete.
Qed.

(** ** [girth_geq] — satisfiable witness.
    'K_2 carries an edge yet has NO genuine (length ≥ 3) cycle, so it has
    girth ≥ g for every g.  This is exactly the case the [2 < size c] guard
    fixes: the size-2 closed walk [[x; y]] is an edge, not a cycle. *)
Lemma girth_geq_K2 g : girth_geq 'K_2 g.
Proof.
move=> c /andP[_ /card_uniqP eqsz] hsz.
move: (max_card (mem c)); rewrite eqsz card_ord => h2.
by move: hsz; rewrite ltnNge h2.
Qed.

(** ** [double_critical] — witness: 'K_2 is double-critical. *)
Lemma double_critical_K2 : double_critical 'K_2.
Proof.
move=> x y xy.
have xney : x != y by move: xy; rewrite /edge_rel /=.
have e2 : [set x; y] = [set: 'K_2].
  by apply/eqP; rewrite eqEcard subsetT cardsU1 inE xney cards1 cardsT card_ord.
by rewrite e2 setDv chi0 chi_complete.
Qed.

(** ** [zero_two_graph] — witness: 'K_2 is a (0,2)-graph. *)
Lemma zero_two_K2 : zero_two_graph 'K_2.
Proof.
move=> u v uv; left.
rewrite /common_nbr !neigh_complete -setCU.
have -> : [set u] :|: [set v] = [set: 'K_2].
  by apply/eqP; rewrite eqEcard subsetT cardsU1 inE uv cards1 cardsT card_ord.
by rewrite setCT cards0.
Qed.

(** ** [n_cycles_len] — degenerate identity: 0-length count is 0. *)
Lemma n_cycles_len_0 (G : sgraph) : n_cycles_len G 0 = 0.
Proof. by rewrite /n_cycles_len muln0 divn0. Qed.

(** ** [count_cycles_mod] — identity: no cycle is 0 mod 0 (empty filter). *)
Lemma count_cycles_mod_0 (G : sgraph) : count_cycles_mod G 0 = 0.
Proof.
rewrite /count_cycles_mod big_pred0 // => L.
by rewrite dvd0n andbC; case: (val L) => [|l] //=.
Qed.

(** ** [edge_disjoint_clique_union] — witness: 'K_1 is a single K_1. *)
Lemma efl_K1 : edge_disjoint_clique_union 'K_1 1.
Proof.
exists (fun _ => [set: 'K_1]); split.
- by move=> i; rewrite cardsT card_ord.
- by move=> i; apply: clique_complete.
- by move=> i j; rewrite (ord1 i) (ord1 j) eqxx.
- by move=> x; exists ord0; rewrite inE.
- by move=> x y _; exists ord0; rewrite !inE.
Qed.

(** ** [graph_power] — identity: the 0-th power is edgeless. *)
Lemma graph_power0_edgeless (G : sgraph) (x y : graph_power G 0) :
  ~~ (x -- y).
Proof.
rewrite /edge_rel /= /pow_rel /reach_le /= !inE [y == x]eq_sym orbb andNb.
by [].
Qed.

(** ** [subdivision] — identity: original vertices are never adjacent
    (every edge is genuinely subdivided). *)
Lemma sub_inl_inl (G : sgraph) n (a b : G) :
  ~~ @edge_rel (subdivision G n) (inl a) (inl b).
Proof. by rewrite /edge_rel /= /sub_rel /=. Qed.

(** ** [frac_power] — identity: the 0-th fractional power is edgeless. *)
Lemma frac_power0_edgeless (G : sgraph) n (x y : frac_power G 0 n) :
  ~~ (x -- y).
Proof. exact: graph_power0_edgeless. Qed.

(** ** [valency_variety] — textbook identity: a regular graph has a single
    distinct degree, so valency_variety('K_n.+1) = 1. *)
Lemma undup_nseqS (a : nat) m : undup (nseq m.+1 a) = [:: a].
Proof. by elim: m => [//|m IH] /=; rewrite mem_head -IH. Qed.

Lemma undup_nseq (a : nat) m : 0 < m -> undup (nseq m a) = [:: a].
Proof. by case: m => // m _; apply: undup_nseqS. Qed.

Lemma valency_variety_complete n : valency_variety 'K_n.+1 = 1.
Proof.
rewrite /valency_variety.
have /all_pred1P -> :
    all (pred1 n) [seq #|N(x)| | x <- enum [set: 'K_n.+1]].
  by rewrite all_map; apply/allP => x _ /=; rewrite deg_complete.
rewrite undup_nseq; last by rewrite size_map -cardE cardsT card_ord.
by [].
Qed.

(** ** [omega] (ω, clique number) — textbook identity ω('K_n) = n.
    Grounds the load-bearing clique-number primitive used in the Borodin–
    Kostochka (Row 6) and Reed (Row 9) statements: the whole vertex set of the
    complete graph is a maximum clique, so its clique number equals n. *)
Lemma omega_complete n : ω([set: 'K_n]) = n.
Proof.
have cardKn : #|[set: 'K_n]| = n by rewrite cardsT card_ord.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- case: (omegaP [set: 'K_n]) => K /maxcliquesW /cliques_subset subK.
  by apply: leq_trans (subset_leq_card subK) _; rewrite cardKn.
- have H : #|[set: 'K_n]| <= ω([set: 'K_n]).
    apply: clique_bound; rewrite inE; apply/andP; split; first exact: subsetT.
    by apply/cliqueP; apply: clique_complete.
  by rewrite cardKn in H.
Qed.

(** ** Erdős–Faber–Lovász (Row 5, U1) — SETTLED-CASE truth-value forcing.

    The full statement [erdos_faber_lovasz_statement] asserts
    [edge_disjoint_clique_union G k -> χ([set: G]) = k].  The nontrivial
    UPPER bound [χ([set: G]) <= k] for all [k] is exactly the Kang–Kelly–
    Kühn–Methuku–Osthus (2023) theorem — a major result, OUT OF SCOPE and
    NOT attempted here.  We ground the right-polarity fragments that follow
    from the primitive by pure colouring theory: the always-true lower bound
    for every [k], and full equality in the two settled small cases [k=0,1].

    Reused coq-graph-theory colouring API (core/coloring.v):
      [sub_chi : A ⊆ B -> χ(A) <= χ(B)], [chi_clique : clique C -> χ(C) = #|C|],
      [leq_chi : χ(A) <= #|A|]. *)

(** (A) Always-true LOWER bound, ALL [k]: an edge-disjoint clique union with
    parameter [k] contains (for [k>0]) the [k]-vertex clique [cliqs ord0],
    whose chromatic number is [k]; monotonicity of [χ] under [⊆] lifts this to
    the whole graph.  For [k=0] the bound [0 <= χ] is trivial. *)
Lemma efl_lower_bound (G : sgraph) (k : nat) :
  edge_disjoint_clique_union G k -> (k <= χ([set: G]))%N.
Proof.
case: k => [|k]; first by move=> _; exact: leq0n.
case=> cliqs [Hcard Hclq _ _ _].
have H0 : #|cliqs ord0| = k.+1 by apply: Hcard.
have Hc0 : clique (cliqs ord0) by apply: Hclq.
apply: leq_trans _ (sub_chi (subsetT (cliqs ord0))).
rewrite chi_clique; first by rewrite H0.
exact: Hc0.
Qed.

(** (B) Settled case [k=0]: the cover clause quantifies over [i : 'I_0], which
    is empty, so no vertex can be covered — hence [G] has no vertices,
    [#|[set: G]| = 0], and [χ = 0]. *)
Lemma efl_k0 (G : sgraph) :
  edge_disjoint_clique_union G 0 -> χ([set: G]) = 0.
Proof.
case=> cliqs [_ _ _ Hcov _].
have hG : #|[set: G]| = 0.
  apply/eqP; rewrite cards_eq0 -subset0; apply/subsetP => x _; exfalso.
  case: (Hcov x) => i _.
  by move: (ltn_ord i); rewrite ltn0.
apply/eqP; rewrite -leqn0.
by apply: leq_trans (leq_chi [set: G]) _; rewrite hG.
Qed.

(** (C) Settled case [k=1]: [cliqs ord0] is a 1-vertex clique, and the cover
    clause (with the only index [ord0 : 'I_1]) forces every vertex into it, so
    [[set: G] = cliqs ord0] is a clique of size 1 and [χ = 1]. *)
Lemma efl_k1 (G : sgraph) :
  edge_disjoint_clique_union G 1 -> χ([set: G]) = 1.
Proof.
case=> cliqs [Hcard Hclq _ Hcov _].
have H0 : #|cliqs ord0| = 1 by apply: Hcard.
have Hc0 : clique (cliqs ord0) by apply: Hclq.
have Heq : [set: G] = cliqs ord0.
  apply/eqP; rewrite eqEsubset subsetT andbT; apply/subsetP => x _.
  by case: (Hcov x) => i Hxi; rewrite (ord1 i) in Hxi.
rewrite Heq chi_clique; first by rewrite H0.
exact: Hc0.
Qed.

(** (D) k=2 — SKIPPED (reported as a blocker below).  Full equality
    [χ = 2] here needs the UPPER bound [χ([set: G]) <= 2], i.e. an explicit
    2-colouring / bipartition of the union of two ≤1-vertex-sharing edges.  No
    coq-graph-theory lemma yields [χ <= 2] without constructing that colouring
    (a genuine case split on whether the two K_2's share a vertex), so this is
    left unproven rather than weakened. *)

(** ** Erdős–Lovász double-critical (Row 1, U1) — right-polarity fragments.

    The full [double_critical_graph_statement] (every connected double-critical
    [n]-chromatic graph is [K_n]) is the Erdős–Lovász conjecture; its
    load-bearing settled cases [k=4,5] are the Mozhan (1983) / Stiebitz (1987)
    structural theorems, OUT OF SCOPE and NOT attempted.  We ground the
    fragments that force the correct truth value without those theorems: the
    whole conjectured-extremal family [K_n] genuinely satisfies every hypothesis
    of the statement (teeth), and the elementary [n=1] slice of the FULL
    statement is proved TRUE.

    Reused API: [chi_clique], [sub_clique], [subsetDl], [cardsD], [clique_bound],
    [omega_leq_chi] (core/coloring.v), [connectedTI]/[connect0]/[connect1],
    [connected_card_gt1], [sg_edgeNeq], [Diso''] (core/sgraph.v, core/digraph.v),
    and the local [clique_complete]/[chi_complete]/[Delta_complete]. *)

(** (A) TEETH — the whole extremal family [K_{n+2}] is double-critical:
    deleting any adjacent pair leaves a [K_n], dropping [χ] by exactly [2].
    Strictly generalises the existing [double_critical_K2] witness (its [n=0]
    case), so the [double_critical] hypothesis is non-vacuous on every [K_n]
    with [n ≥ 2] — the conjecture targets the correct graph class. *)
Lemma double_critical_complete n : double_critical 'K_n.+2.
Proof.
move=> x y xy.
have xney : x != y by move: xy; rewrite /edge_rel /=.
have cardT : #|[set: 'K_n.+2]| = n.+2 by rewrite cardsT card_ord.
have subxy : [set x; y] \subset [set: 'K_n.+2] by apply: subsetT.
have c2 : #|[set x; y]| = 2 by rewrite cards2 xney.
have clqS : clique ([set: 'K_n.+2] :\: [set x; y]).
  apply: sub_clique; [ exact: subsetDl | exact: clique_complete ].
have cardS : #|[set: 'K_n.+2] :\: [set x; y]| = n.
  by rewrite cardsD (setIidPr subxy) c2 cardT -addn2 addnK.
by rewrite chi_clique // cardS chi_complete addn2.
Qed.

(** (B) TEETH — every complete graph [K_{n+1}] is connected, so the
    connectivity hypothesis of the statement is satisfied by exactly the
    conjectured extremal graphs. *)
Lemma connected_complete n : connected [set: 'K_n.+1].
Proof.
apply: connectedTI => x y.
case: (eqVneq x y) => [->|xney]; first exact: connect0.
by apply: connect1; rewrite /edge_rel /= xney.
Qed.

(** (C) TEETH — the extremal family [K_{n+2}] jointly satisfies ALL premises of
    the statement AND its conclusion ([K ≃ K] via [diso_id]); so each [K_n]
    ([n ≥ 2]) is a genuine fixed point of the conjecture's implication, and the
    premise/conclusion set is inhabited for every chromatic number [≥ 2]. *)
Lemma double_critical_witness n :
  0 < #|'K_n.+2| /\ connected [set: 'K_n.+2] /\ double_critical 'K_n.+2 /\
  χ([set: 'K_n.+2]) = n.+2 /\ inhabited ('K_n.+2 ≃ 'K_n.+2).
Proof.
split; first by rewrite card_ord.
split; first exact: connected_complete.
split; first exact: double_critical_complete.
split; first exact: chi_complete.
exact: (inhabits diso_id).
Qed.

(** (D) SMALL-INSTANCE — the FULL statement at [n=1], proved TRUE: a connected
    double-critical graph with [χ = 1] is [K_1].  [χ = 1] forces edgelessness
    (an edge is a 2-clique, so [ω ≥ 2 ≤ χ], contradiction); connectivity plus
    edgelessness plus non-emptiness force [#|G| = 1] (by [connected_card_gt1]);
    the single-vertex graph is then explicitly [≃ 'K_1].  A genuine settled
    slice of the conjecture, not a vacuous one. *)
Lemma double_critical_n1 (G : sgraph) :
  0 < #|G| -> connected [set: G] -> double_critical G ->
  χ([set: G]) = 1 -> inhabited (G ≃ 'K_1).
Proof.
move=> gt0 conn _ chi1.
have edgeless : forall x y : G, ~~ (x -- y).
  move=> x y; apply/negP => xy.
  have xney : x != y by rewrite (sg_edgeNeq xy).
  have cl2 : clique [set x; y].
    move=> a b; rewrite !inE => /orP[/eqP->|/eqP->] /orP[/eqP->|/eqP->] ne.
    - by move: ne; rewrite eqxx.
    - exact: xy.
    - by rewrite sgP.
    - by move: ne; rewrite eqxx.
  have clm : [set x; y] \in cliques [set: G].
    by rewrite inE subsetT /=; apply/cliqueP.
  have h2 := clique_bound clm; rewrite cards2 xney in h2.
  by move: (leq_trans h2 (omega_leq_chi [set: G])); rewrite chi1.
have le1 : #|G| <= 1.
  rewrite leqNgt; apply/negP => gt1.
  have gt1T : 1 < #|[set: G]| by rewrite cardsT.
  case/card_gt1P: gt1T => x [y] [_ _ xney].
  have xT : x \in [set: G] by rewrite inE.
  have yT : y \in [set: G] by rewrite inE.
  case: (connected_card_gt1 conn xT yT xney) => z _ xz.
  by move: (edgeless x z); rewrite xz.
have alleq : forall x y : G, x = y.
  have /card_le1_eqP h : #|[set: G]| <= 1 by rewrite cardsT.
  by move=> x y; apply: h; rewrite inE.
have [x0 _] : exists x0 : G, x0 \in [set: G].
  by apply/card_gt0P; rewrite cardsT.
pose f (_ : G) : 'K_1 := ord0.
pose g (_ : 'K_1) : G := x0.
constructor.
apply: (@Diso'' G 'K_1 f g).
- by move=> x; apply: alleq.
- by move=> y; rewrite /f (ord1 y).
- by move=> x y xy; move: (edgeless x y); rewrite xy.
- by move=> x y; rewrite /edge_rel /= (ord1 x) (ord1 y) eqxx.
Qed.

(** ** Cycles in graphs of large chromatic number (Row 3, U1).

    The full [cycles_in_graphs_of_large_chromatic_number_statement]
    ([2 < k] and [k < χ] ⟹ [(k+1)(k-1)! ≤ 2·count_cycles_mod G k]) is the
    Erdős/Gyárfás cycle-counting conjecture; every settled sub-case is itself a
    nontrivial theorem and the one decidable instance ([K_4], [k=3]) is blocked
    by a stuck [Finite.enum] cardinality — both OUT OF SCOPE.  We ground the
    fragments that pin the primitive's boundary behaviour and the guard's
    truth-value role. *)

(** (A) BOUNDARY — [count_cycles_mod 'K_2 1 = 0]: the genuine-cycle filter
    [2 < L] is empty over the tiny index range [L < #|'K_2|.+1 = 3], so the
    degenerate [k=1] count vanishes (companion to the existing [count_cycles_mod_0]
    at [k=0]).  Purely structural (empty [bigop] filter). *)
Lemma cnt_K2_1 : count_cycles_mod 'K_2 1 = 0.
Proof.
rewrite /count_cycles_mod big_pred0 // => L.
by case: L => m Hm /=; rewrite card_ord in Hm; case: m Hm => [|[|[|m]]].
Qed.

(** (B) INHABITATION — the guard regime [2 < k] and [k < χ] is satisfiable
    (witness [k=3], [G = 'K_4], [χ = 4]); the statement genuinely asserts a
    cycle-count lower bound on real graphs, not a vacuous implication. *)
Lemma cycles_guard_inhabited :
  exists (k : nat) (G : sgraph), 2 < k /\ k < χ([set: G]).
Proof. exists 3, 'K_4. rewrite chi_complete. by split. Qed.

(** (C) BOUNDARY — the [2 < k] guard is LOAD-BEARING: dropping it makes the
    proposition FALSE.  Witness [k=1], [G = 'K_2]: [1 < χ = 2] holds but the
    LHS [2·0! = 2 > 0 = 2·count] fails (using [cnt_K2_1]).  Pins the correct
    truth value (FALSE) of the un-guarded variant. *)
Lemma cycles_guard_necessary :
  ~ (forall (k : nat) (G : sgraph),
        k < χ([set: G]) -> (k.+1) * (k.-1)`! <= 2 * count_cycles_mod G k).
Proof.
move=> H; move: (H 1 'K_2).
rewrite chi_complete cnt_K2_1 muln0 => /(_ (ltnSn 1)) Hle.
have Hpos : 0 < (1.+1) * (1.-1)`! by rewrite muln_gt0 fact_gt0.
by rewrite leqNgt Hpos in Hle.
Qed.

(** ** Vertex colouring of graph fractional powers (Row 7, U1).

    The full [vertex_coloring_of_graph_fractional_powers_statement]
    (connected [G], [Δ ≥ 3], [1 < m < n] ⟹ [χ(G^{m/n}) = ω(G^{m/n})]) is
    Iradmusa's conjecture; the hard direction [χ ≤ ω] carries all the content
    and is OUT OF SCOPE.  We ground the always-true half of the equality and
    the non-emptiness of the guard. *)

(** (A) ALWAYS-TRUE DIRECTION — the [ω ≤ χ] half of the conjectured equality
    holds for ALL [G, m, n] (a maximum clique needs that many colours), so the
    only open content is the reverse inequality [χ ≤ ω]. *)
Lemma vcgfp_omega_leq_chi (G : sgraph) (m n : nat) :
  ω([set: frac_power G m n]) <= χ([set: frac_power G m n]).
Proof. exact: omega_leq_chi. Qed.

(** (B) INHABITATION — the four-fold guard (connected [G], [Δ G ≥ 3],
    [1 < m], [m < n]) is jointly satisfiable ([G = 'K_4], [Δ = 3], [m=2],
    [n=3]), so the statement is not vacuously true; the [Δ ≥ 3] clause genuinely
    excludes paths/cycles/[K_2]. *)
Lemma vcgfp_guard_inhabited :
  exists (G : sgraph) (m n : nat),
    [/\ connected [set: G], 3 <= Delta G, 1 < m & m < n].
Proof.
exists 'K_4; exists 2; exists 3; split.
- exact: connected_complete.
- by rewrite (Delta_complete 3).
- by [].
- by [].
Qed.

(** ============================================================================
    TECHNIQUE #3 — independent re-encoding of [valency_variety] and a proved [=].

    [valency_variety G] is defined as the LENGTH OF A DEDUPLICATED LIST of
    natural-number degrees: [size (undup [seq #|N x| | x <- enum setT])].  The
    independent second encoding counts the same quantity — the number of
    distinct vertex-degrees — but as the CARDINALITY OF A FINSET IMAGE inside a
    bounded ordinal type: every degree [#|N x|] is [≤ #|G|], hence lands
    faithfully (via [inord]) in ['I_(#|G|.+1)], and

        valency_variety G  =  #| [set inord #|N x| | x in [set: G]] |.

    The two are structurally different formalisations (nat-list [undup] length
    vs. [{set 'I_(#|G|.+1)}] image cardinality), and the equality is NOT
    definitional.  Its load-bearing content is exactly the faithfulness of the
    [inord] embedding: degrees are [< #|G|.+1] ([max_card]), so [inord] is
    INJECTIVE on the attained degrees ([inordK]) and no two distinct degrees are
    collapsed — a wrong bound (or a missing [undup]) would break the equality.
    The bridge is a genuine induction: [size_undup_map_in] proves that mapping a
    list by a function injective on its elements preserves the deduplicated
    length, via a per-element membership case analysis. *)

(** Generic helper: the finset-cardinality of a seq's membership predicate
    equals the length of its deduplication. *)
Lemma card_mem_undup (T : finType) (s : seq T) : #|mem s| = size (undup s).
Proof.
rewrite -(eq_card (mem_undup s)).
by apply/card_uniqP; exact: undup_uniq.
Qed.

(** Generic helper: a map by a function injective ON THE LIST's ELEMENTS
    preserves deduplicated length.  (Induction with a membership case split;
    NOT a consequence of the global-injectivity [undup_map_inj].) *)
Lemma size_undup_map_in (T rT : eqType) (g : T -> rT) (s : seq T) :
  {in s &, injective g} -> size (undup (map g s)) = size (undup s).
Proof.
elim: s => [//| x s' IH] inj_s /=.
have inj_s' : {in s' &, injective g}.
  move=> a b Ha Hb eq; apply: (inj_s a b _ _ eq); by rewrite inE ?Ha ?Hb orbT.
have memeq : (g x \in map g s') = (x \in s').
  apply/idP/idP.
  - move=> /mapP[y Hy Heq].
    have xin : x \in (x :: s') by rewrite inE eqxx.
    have yin : y \in (x :: s') by rewrite inE Hy orbT.
    by rewrite (inj_s x y xin yin Heq).
  - by move=> Hx; apply/mapP; exists x.
rewrite memeq; case: ifP => _.
- exact: IH inj_s'.
- by rewrite /= IH.
Qed.

(** The re-encoding, proved equal to [valency_variety]. *)
Lemma valency_varietyE (G : sgraph) :
  valency_variety G = #| [set (inord #|N(x)| : 'I_(#|G|.+1)) | x in [set: G]] |.
Proof.
rewrite /valency_variety imset_card card_mem_undup.
have -> : [seq inord #|N(x)| | x in [set: G]]
        = map (inord : nat -> 'I_(#|G|.+1)) [seq #|N(x)| | x <- enum [set: G]].
  by rewrite -map_comp.
symmetry; apply: size_undup_map_in.
have bound : forall d, d \in [seq #|N(x)| | x <- enum [set: G]] -> d < #|G|.+1.
  by move=> d /mapP[x _ ->]; rewrite ltnS; exact: max_card.
move=> a b Ha Hb Hab.
by rewrite -(inordK (bound a Ha)) -(inordK (bound b Hb)) Hab.
Qed.

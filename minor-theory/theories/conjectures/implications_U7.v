(** * Minor.conjectures.implications_U7 — implication/refutation edges for U7

    Relative theorems among the six U7 nodes (graph minors & immersions), each
    of the shape [Theorem A_statement -> B_statement], proved WITHOUT resolving
    either endpoint.  Axiom-free: only [Qed]-closed results live here; every
    candidate edge that does NOT close is documented (not stated) so the file
    stays free of [Admitted]/[Axiom].

    EDGE-POLICY SUMMARY (plan §6).  The §6 verified-literature table contains NO
    edge among U7's minor nodes (its verified edges are all in the cycle/flow
    area: Petersen-colouring ⟹ Berge–Fulkerson / CDC, etc.).  Hence NO
    verified-literature edge is scheduled here.  The two structurally natural
    candidate edges between the planarity-gated rows (Row 4 [high_connectivity_
    no_k_n] and Row 5 [jorgensens]) are RE-DERIVED below and both FAIL the [Qed]
    gate — they remain status=candidate, proved=false.  No false edge is forced.

    What IS proved: a structural bridge lemma [apex_iff_pad1] showing that, at
    [n = 6] (so [n - 5 = 1]), the conclusion of Row 4 ([planar_after_deleting
    is_planar G 1]) and the conclusion of Row 5 ([apex is_planar G]) coincide.
    This is the technical heart of WHY the two rows are "morally" the same
    problem at [n = 6] — yet, as the failed candidates show, it is NOT enough to
    turn either full statement into the other (Row 4 has a "sufficiently large"
    size bound [exists N]; Row 5 quantifies all graphs, and Row 4 quantifies all
    [n] while Row 5 fixes [n = 6]). *)

From GTBase Require Import base.
From GraphTheory Require Import minor connectivity coloring.
From Minor.foundations Require Import minor_dec.
From Minor.conjectures Require Import U7 X5.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Structural bridge (proved, [Qed])

    [apex is_planar G] (delete exactly one vertex to reach planarity) is
    logically the same as [planar_after_deleting is_planar G 1] (delete a
    1-element vertex set to reach planarity).  Pure set-cardinality bookkeeping:
    a 1-element set is [[set v]] for a unique [v].  Independent of the meaning of
    the abstract [is_planar] predicate (G2 gate), so it needs no planarity API.

    This is the [n - 5 = 1] instance ([n = 6]) of Row 4's conclusion matching
    Row 5's conclusion; it is the reusable core a future proof of either
    direction would invoke once the quantifier obstructions below are removed. *)
Lemma apex_iff_pad1 (is_planar : sgraph -> Prop) (G : sgraph) :
  apex is_planar G <-> planar_after_deleting is_planar G 1.
Proof.
rewrite /apex /planar_after_deleting. split.
- move=> [v Hv]. exists [set v]. split=> //. exact: cards1.
- move=> [S [HS Hp]]. have /cards1P [v Hv] : #|S| == 1 by rewrite HS.
  exists v. by rewrite -Hv.
Qed.

(** ** Candidate edges between Row 4 and Row 5 — RE-DERIVED, both FAIL the gate.

    Citation/context.  Jørgensen's conjecture (Row 5: every 6-connected graph
    with no [K_6] minor is apex; Jørgensen 1994, OPG "Jørgensen's Conjecture")
    is the [n = 6] case of the OPEN problem in Row 4 (every SUFFICIENTLY LARGE
    n-connected graph with no [K_n] minor is [(n-5)]-apex).  The "sufficiently
    large" version at [n = 6] is in fact a THEOREM (Kawarabayashi–Norin–Thomas–
    Wollan, "K_6 minors in large 6-connected graphs"), whereas Row 5's
    all-graphs version is open.  That gap is exactly why neither full statement
    implies the other:

    (1) [high_connectivity_no_k_n_statement -> jorgensens_statement] FAILS.
        Re-derivation: after [move=> HC is_planar G Hconn HnK6] and
        [move: (HC is_planar 6) => [N HN]], the goal is [apex is_planar G] but
        [HN] only fires under the hypothesis [N <= #|G|], which is NOT available
        — Row 5 admits arbitrarily SMALL 6-connected graphs that Row 4's [exists
        N] size bound never constrains.  (Even with [apex_iff_pad1] bridging the
        conclusions, the size hypothesis is missing.)  status=candidate,
        proved=false; do not state.

    (2) [jorgensens_statement -> high_connectivity_no_k_n_statement] FAILS.
        Re-derivation: after [move=> J is_planar n; exists 0; move=> G _ Hconn
        HnKn], the goal is [planar_after_deleting is_planar G (n - 5)] for an
        ARBITRARY [n], with [G] only [n]-connected and [K_n]-minor-free, while
        [J] supplies information solely for [n = 6] / [K_6].  No way to discharge
        the [n <> 6] cases.  status=candidate, proved=false; do not state.

    A third, genuinely-true mathematical link — [jorgensens_statement] ⟹ "every
    7-connected graph has a [K_6] minor" (the CONNECTIVITY conjunct of Row 1):
    a 7-connected graph minus one vertex is 6-connected, but a planar graph is
    at most 5-connected, so a 7-connected graph cannot be apex; hence a
    7-connected [K_6]-minor-free graph (which Row 5 would force to be apex)
    cannot exist — needs the EXTERNAL planarity fact "planar ⟹ connectivity ≤ 5"
    (unavailable: [is_planar] is abstract, G2 gate) AND targets only the
    connectivity conjunct of Row 1's CONJUNCTION (the minimum-degree conjunct is
    not derivable from Jørgensen, since high min degree does not force
    6-connectivity).  status=candidate, proved=false; needs_external. *)

(** ** e043 : Hadwiger-type independence bound ⟹ the seagull problem (PROVED)

    Corpus argument (gc:e043).  Let [h] be the largest [k] with a [K_k] minor of
    [G].  Then [G] has no [K_(h+1)] minor, so the source row at [t = h] gives
    [n <= h * α(G) <= 2h], hence [ceil(n/2) <= h] and, by monotonicity of
    complete-graph minors, [G] has a [K_ceil(n/2)] minor.

    Re-derivation used here.  The "largest [k]" is avoided: one applies the
    source at the single value [t = ceil(n/2) - 1].  The step "G has no
    [K_(t+1)] minor OR we are done" is the elimination of a double negation,
    which is legitimate because [minor] is DECIDABLE on finite simple graphs
    ([Minor.foundations.minor_dec.minorNN], proved there from [minorRE] /
    [minor_of_rmap] and the Boolean [connectedb] / [neighbor]) — so no classical
    axiom is used.  Arithmetic: with [m := ceil(n/2) >= 2] and [t := m - 1] we
    get [n <= t * α(G) <= 2t = 2m - 2], i.e. [n + 2 <= 2m], while
    [2 * ceil(n/2) <= n + 1] always holds ([leq_trunc_div]) — contradiction.  The
    degenerate range [ceil(n/2) <= 1] needs no source at all: a nonempty graph
    has a [K_1] minor. *)
Theorem hadwiger_independence_minor_implies_seagull :
  hadwiger_independence_minor_statement -> seagull_statement.
Proof.
move=> src G G0 a2.
have K1 : minor G 'K_1 := minor_K1 G0.
have hceil : ceil_div #|G| 2 * 2 <= #|G| + 1.
  by rewrite /ceil_div addn2 subn1 /= -addn1; exact: leq_divM.
have [m1|m2] := leqP (ceil_div #|G| 2) 1; first exact: minor_K_le m1 K1.
apply: minorNN => nm.
have m_gt0 : 0 < ceil_div #|G| 2 := ltnW m2.
have m0 : 0 < (ceil_div #|G| 2).-1 by rewrite -subn1 subn_gt0.
have e : ((ceil_div #|G| 2).-1).+1 = ceil_div #|G| 2 := prednK m_gt0.
have key : #|G| <= (ceil_div #|G| 2).-1 * α(G).
  by apply: (src _ #|G| G m0 erefl); rewrite e; exact: nm.
have key2 : #|G| + 2 <= ceil_div #|G| 2 * 2.
  rewrite -e mulSn [2 + _]addnC leq_add2r.
  by apply: leq_trans key _; exact: leq_mul (leqnn _) a2.
by move: (leq_trans key2 hceil); rewrite leq_add2l.
Qed.

(** Machine-readable edge records (extracted by meta/build_edge_graph.py): *)
(*@EDGE from=hadwiger_independence_minor_statement to=seagull_statement kind=implies status=verified proved=true proof=hadwiger_independence_minor_implies_seagull cite="gc:e043" note="Seagull is the alpha<=2 case: apply the source at t = ceil(n/2)-1, which gives n <= t*alpha(G) <= 2t = 2*ceil(n/2)-2, contradicting 2*ceil(n/2) <= n+1; the case ceil(n/2)<=1 is the K_1 minor of a nonempty graph. The 'G has no K_(t+1) minor' step is a double-negation elimination, licensed axiom-free by decidability of minor (Minor.foundations.minor_dec.minorNN)." *)
(*@EDGE from=high_connectivity_no_k_n_statement to=jorgensens_statement kind=implies status=refuted-direction cite="OPG minor-theory" note="REFUTED-DIRECTION (metadata wave M, 2026-09-24): fails Qed: the exists-N size bound never constrains small 6-connected graphs; both endpoints G2-blocked (abstract planarity). Earlier note: FAILS Qed: size hypothesis missing; both endpoints G2-blocked (abstract is_planar)" *)
(*@EDGE from=jorgensens_statement to=high_connectivity_no_k_n_statement kind=implies status=refuted-direction cite="OPG minor-theory" note="REFUTED-DIRECTION (metadata wave M, 2026-09-24): fails Qed: no way to discharge the n <> 6 cases. Earlier note: FAILS Qed: needs the n<>6 cases; both endpoints G2-blocked" *)
(*@EDGE from=jorgensens_statement to=forcing_a_k_6_minor_statement kind=implies status=candidate cite="Jorgensen 1994" note="needs_external: planar=>connectivity<=5 (G2); targets only the connectivity conjunct" *)
Print Assumptions hadwiger_independence_minor_implies_seagull.

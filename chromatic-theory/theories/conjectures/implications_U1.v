(** * Chromatic.conjectures.implications_U1 — milestone U1 dependency-graph EDGES

    Machine-checked implication / refutation EDGES between the nine committed
    U1 conjecture statements (see [U1.v]).  As in the digraph-theory
    [implications.v] / [implications2.v] layer, every edge here is meant to be
    a *relative* theorem: a [Qed]-closed [Theorem A_statement -> B_statement]
    that is provable WITHOUT resolving (proving or refuting) either endpoint —
    it only transports one conjectural hypothesis to another, or applies one
    committed conjecture on a restricted subclass.  Any bridge fact that would
    need resolving a conjecture or heavy out-of-scope machinery is carried as an
    EXPLICIT hypothesis (never [Admitted], never [Axiom]), keeping the edge
    fully [Qed]-closed and the file axiom-free.

    ────────────────────────────────────────────────────────────────────────
    AUDIT RESULT: no [verified-literature] edge among the nine U1 nodes.
    ────────────────────────────────────────────────────────────────────────

    The nine U1 nodes are a deliberately diverse, mutually INDEPENDENT slice of
    the open/partial/solved graph-colouring corpus (the Jensen–Toft / "open
    problems in graph colouring" curation):

      Row 1  double_critical_graph_statement                 (characterization)
      Row 2  three_chromatic_0_2_graphs_statement            (∃-existence)
      Row 3  cycles_in_graphs_of_large_chromatic_number_…    (∀ lower count)
      Row 4  high_girth_low_degree_4_chromatic_graphs_…      (∃-existence)
      Row 5  erdos_faber_lovasz_statement                    (∀ χ = k)
      Row 6  the_borodin_kostochka_statement                 (∀ χ upper bound)
      Row 7  vertex_coloring_of_graph_fractional_powers_…    (∀ χ = ω)
      Row 8  melnikovs_valency_variety_statement             (∀ χ lower bound)
      Row 9  reeds_omega_delta_and_chi_statement             (∀ χ upper bound)

    No pair carries a clean relative implication that is provable without
    resolving an endpoint:

    • Row 6 (Borodin–Kostochka) vs Row 9 (Reed) — INDEPENDENT, both directions
      are FALSE, so NEITHER may be asserted (and a genuinely false edge must
      FAIL to compile — we do not force it):
        – Reed ⟹ B-K is FALSE / withdrawn: refuted at Δ = 9, ω = 8, where a
          graph with χ = 9 satisfies Reed (2·9 = 18 ≤ 9+1+8+1 = 19) yet
          violates B-K (max(Δ−1, ω) = max(8, 8) = 8 < 9).  This is the headline
          forbidden edge.
        – B-K ⟹ Reed is ALSO FALSE: B-K only constrains graphs with Δ ≥ 9 (so
          it cannot bound χ for the Δ < 9 graphs that Reed quantifies over),
          and even at Δ ≥ 9 its bound max(Δ−1, ω) is WEAKER than Reed's
          ⌈(Δ+1+ω)/2⌉+ when ω is small (e.g. Δ = 100, ω = 2: B-K gives χ ≤ 99,
          Reed demands 2χ ≤ 104 i.e. χ ≤ 52).  So B-K_statement cannot prove
          Reed_statement either.
      Both directions are reported as refuted-direction edges and intentionally
      kept OUT of this compiling file.

    • An upper-bound conjecture (Row 6 / Row 9) can never IMPLY a lower-bound
      conjecture (Row 8, Melnikov), nor the reverse — bounds run opposite ways.

    • The two ∃-existence rows do not transport: a high-girth 4-regular
      4-chromatic graph (Row 4) is not a (0,2)-graph (girth ≥ 5 forces ≤ 1
      common neighbour, breaking the "0 or 2" law), and a (0,2)-graph with
      χ = 3 (Row 2) is neither 4-regular nor 4-chromatic — so Row 2 ⇎ Row 4.

    • Rows 1, 5, 7 (characterization / equality statements) share no common
      hypothesis class with any other node, so none specializes to another.

    Consequently this file commits ZERO [Theorem]s: there is no honest
    [verified-literature] edge to schedule, and every plausible-looking edge is
    either FALSE (must not compile) or unsupported by the literature.  The file
    still loads (axiom-free) so the milestone's edge layer is present and green;
    the refuted-direction edges are recorded in the deliverable's edge table,
    not as Rocq theorems.

    This matches the U1 prior: for chromatic-bound conjectures expect FEW or NO
    verified edges — Reed and Borodin–Kostochka are independent; we do not
    fabricate. *)

From GTBase Require Import base.
From Chromatic.foundations Require Import chi_bounding choice_number critical.
From Chromatic.conjectures Require Import U1 X7 X213.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** No edge is scheduled: see the AUDIT RESULT above.  The nine U1 nodes carry
    no [verified-literature] relative implication, and the only expected
    relationship (Reed ⇄ Borodin–Kostochka) is false in BOTH directions and is
    therefore deliberately absent (a false edge must fail to compile). *)

(** Machine-readable edge records (extracted by meta/build_edge_graph.py): *)
(*@EDGE from=reeds_omega_delta_and_chi_statement to=the_borodin_kostochka_statement kind=implies status=refuted-direction cite="false at Δ=9,ω=8 (Cranston-Rabern)" *)
(*@EDGE from=the_borodin_kostochka_statement to=reeds_omega_delta_and_chi_statement kind=implies status=refuted-direction cite="independent; neither implies the other" *)

(** ════════════════════════════════════════════════════════════════════════
    EDGES INTO U1 FROM OTHER WAVES (2026-09-24 edge pass)
    ════════════════════════════════════════════════════════════════════════
    The AUDIT RESULT above concerns U1-INTERNAL edges.  One verified corpus
    edge has a U1 row as its TARGET:

      e228  X213's Erdos-Lovasz-Tihany  ==>  Row 1 (double-critical graphs)

    It is a relative theorem and resolves neither endpoint. *)

(*@EDGE from=list_reed_choice_number_statement to=reeds_omega_delta_and_chi_statement kind=implies status=verified proved=true proof=list_reed_choice_number_implies_reeds_omega_delta_and_chi cite="gc:e004" note="Corpus relation e004 (the list analogue of Reed's conjecture implies Reed's conjecture). Now CLOSED. Three ingredients: (1) the choice number EXISTS -- X7 states its bound for a RELATIONALLY specified [is_choice_number G ch], so the edge must exhibit ch(G); this is [Chromatic.foundations.choice_number.choice_number_ex], proved by palette canonicalisation ([choosable G k] over an arbitrary palette reduces to its instances over the single palette I_(k * #|G|) with lists of size exactly k, which is a BOOLEAN predicate) plus the nonemptiness witness [choosable G #|G|] (greedy system of distinct representatives), so that [ex_minn] applies; (2) chi(G) <= ch(G), which is [Chromatic.foundations.chi_bounding.chi_le_choosable] run on the constant lists; (3) the ceiling arithmetic 2 * ceil_div a 2 = (a + 1) %/ 2 * 2 <= a + 1 ([leq_divM]) with a = Delta(G) + 1 + omega(G), which is exactly U1's doubled Reed bound. The edge resolves neither endpoint: it transports the conjectural list bound to the conjectural chromatic bound." *)
Theorem list_reed_choice_number_implies_reeds_omega_delta_and_chi :
  list_reed_choice_number_statement -> reeds_omega_delta_and_chi_statement.
Proof.
move=> LR G posG.
have [ch icn] := choice_number_ex posG.
have chile : χ([set: G]) <= ch by apply: chi_le_choosable; case: icn.
apply: (leq_trans (_ : 2 * χ([set: G]) <= 2 * ch)).
  by rewrite leq_mul2l chile orbT.
apply: (leq_trans (_ : 2 * ch <= 2 * ceil_div (Delta G + 1 + ω([set: G])) 2)).
  by rewrite leq_mul2l (LR G ch icn) orbT.
rewrite /ceil_div -addnBA // subn1 /= mulnC.
exact: leq_divM.
Qed.

(*@EDGE from=erdos_lovasz_tihany_statement to=double_critical_graph_statement kind=implies status=verified proved=true proof=erdos_lovasz_tihany_implies_double_critical_graph cite="gc:e228" note="Corpus relation e228 (confirmed, Bondy-Murty A.45 implies the Open Problem Garden double-critical row). Proof: let k = chi(G). If G has a k-clique K then, since a double-critical graph is vertex-critical (foundations/critical.v double_critical_del1: v has a neighbour u, deleting both drops chi by two, putting u back raises it by at most one), no vertex can lie outside K -- K would survive the deletion with chi(K) = k -- so K is the whole vertex set and G is a complete graph (clique_of_chi_full, then GraphTheory's diso_Kn), with #|G| = chi(G) = n. Otherwise omega(G) < k, and then k >= 3 (omega <= 1 would make G edgeless and chi <= 1), so Erdos-Lovasz-Tihany applies with k1 = 2 and k2 = k-1 and yields disjoint A, B with chi(A) = 2 and chi(B) = k-1; an edge xy inside A (chi_gt1_edge) has B contained in V(G) minus {x,y}, so k-1 = chi(B) <= chi(G - x - y) = k-2, a contradiction. The two bridge facts recorded as missing by the earlier candidate annotation are exactly double_critical_del1 and clique_of_chi_full, now proved in foundations/critical.v from chiD1, chi_clique and sub_chi." *)
Theorem erdos_lovasz_tihany_implies_double_critical_graph :
  erdos_lovasz_tihany_statement -> double_critical_graph_statement.
Proof.
move=> ELT G n posG con dc chin.
have memT : forall x : G, x \in [set: G] by move=> x; rewrite inE.
have clT : clique [set: G].
  case: (ltnP 1 #|G|) => [cd|cd1]; last first.
    have /eqP c1 : #|G| == 1 by rewrite eqn_leq cd1 posG.
    move: c1; rewrite -cardsT => /eqP /cards1P[x0 e].
    by move=> u v; rewrite e !inE => /eqP-> /eqP->; rewrite eqxx.
  have crit := @double_critical_del1 G dc con cd.
  have wle := omega_leq_chi [set: G].
  case: (ltnP (ω([set: G])) (χ([set: G]))) => [wlt|wge]; last first.
    have wE : ω([set: G]) = χ([set: G]) by apply/eqP; rewrite eqn_leq wle wge.
    have [K KM] : exists K : {set G}, K \in maxcliques [set: G].
      by case: (omegaP [set: G]) => K KM; exists K.
    have cardK : #|K| = χ([set: G]) by rewrite (card_maxclique KM) wE.
    exact: (@clique_of_chi_full G K (maxclique_clique KM) cardK crit).
  have posW : 0 < ω([set: G]).
    by rewrite lt0n omega_eq0 -card_gt0 cardsT.
  have chi2 : 1 < χ([set: G]) by exact: leq_ltn_trans posW wlt.
  have w2 : 1 < ω([set: G]).
    case: (ltnP 1 (ω([set: G]))) => // w1.
    by move: (@chi_le1_stable G [set: G] (@omega_le1_stableT G w1)); rewrite leqNgt chi2.
  have chi3 : 2 < χ([set: G]) by exact: leq_ltn_trans w2 wlt.
  have [m chiE] : exists m, χ([set: G]) = m.+3.
    by exists (χ([set: G]) - 3); rewrite -addn3 (subnK chi3).
  have nocl : forall S : {set G}, clique S -> #|S| < m.+3.
    move=> S clS; rewrite -chiE; apply: leq_ltn_trans _ wlt.
    by apply: clique_bound; rewrite inE subsetT /=; exact/cliqueP.
  have kk : m.+3 + 1 = 2 + m.+2 by rewrite addn1.
  have k2ge : 2 <= m.+2 by [].
  have [A [B [dis chiA chiB]]] := ELT G m.+3 2 m.+2 chiE nocl kk (leqnn 2) k2ge.
  have chiA2 : 1 < χ(A) by rewrite chiA.
  have [x [y [xA yA xy]]] := @chi_gt1_edge G A chiA2.
  have dcxy := dc x y xy.
  have disI : A :&: B = set0 by apply/eqP; rewrite setI_eq0; exact: dis.
  have dis0 : forall z : G, z \in A -> z \in B -> False.
    by move=> z zA zB; move: (in_set0 z); rewrite -disI !inE zA zB.
  have subB : B \subset [set: G] :\: [set x; y].
    apply/subsetP=> b bB; apply/setDP; split; first exact: memT.
    rewrite !inE negb_or; apply/andP; split.
      by apply: contraTneq bB => ->; apply/negP => xB; exact: (dis0 x xA xB).
    by apply: contraTneq bB => ->; apply/negP => yB; exact: (dis0 y yA yB).
  have h2 : χ([set: G] :\: [set x; y]) = m.+1.
    by move: dcxy; rewrite chiE addn2 => /succn_inj /succn_inj.
  by move: (sub_chi subB); rewrite chiB h2 ltnn.
have cardn : #|G| = n by rewrite -chin (chi_clique clT) cardsT.
rewrite -cardn; constructor; apply: diso_Kn => x y xy.
exact: clT (memT x) (memT y) xy.
Qed.

Print Assumptions erdos_lovasz_tihany_implies_double_critical_graph.

Print Assumptions list_reed_choice_number_implies_reeds_omega_delta_and_chi.

(** * Chromatic.conjectures.implications_U5 — milestone U5 dependency-graph EDGES

    Machine-checked implication / refutation EDGES between the nine committed U5
    conjecture statements (see [U5.v]).  As in the digraph-theory
    [implications.v] / [implications2.v] layer and the sibling [implications_U1.v]
    / [implications_U4.v], every scheduled edge here is a *relative* theorem: a
    [Qed]-closed [Theorem A_statement -> B_statement] provable WITHOUT resolving
    (proving or refuting) either endpoint.  Bridge facts that would need resolving
    a conjecture or heavy out-of-scope machinery are carried as EXPLICIT
    hypotheses (never [Admitted], never [Axiom]); the file stays axiom-free
    ([Print Assumptions goldbergs_implies_seymours_r_graph] = "Closed under the
    global context").

    ════════════════════════════════════════════════════════════════════════════
    SCHEDULED EDGE (verified-literature):  Goldberg ⟹ Seymour's r-graph
    ════════════════════════════════════════════════════════════════════════════

      goldbergs_statement  ⟹  seymours_r_graph_statement

    Endpoints (verbatim from [U5.v]):
      • Goldberg (Row 4):
          forall G : mgraph,
            chromatic_index G <= maxn (mDelta G).+1 (overfull_parameter G).
      • Seymour r-graph (Row 2):
          forall (r : nat) (G : mgraph),
            is_r_graph G r -> edge_colourable G r.+1
        where [is_r_graph G r] = (forall v, #|edges_at v| = r) /\
                                 (forall X, odd #|X| -> r <= #|edge_boundary X|)
        and   [edge_colourable G k] := [chromatic_index G <= k].

    Mathematics.  For an r-graph G the Goldberg bound collapses to r+1, because
    BOTH of its two terms are <= r+1:
      (i)  [mDelta G <= r]: every vertex has exactly r incident edges, so the
           bigmax over the (possibly empty) vertex set is <= r ([mDelta_le]);
      (ii) [overfull_parameter G <= r]: for every vertex set S,
             ⌈|E(S)| / ⌊|S|/2⌋⌉ <= r ([overfull_le]),
           which follows from the density bound  |E(S)| <= r·⌊|S|/2⌋
           ([edge_set_bound]).  That bound is the degree-sum / double-counting
           identity  (handshake)
             Σ_{v∈S} deg(v) = 2·|E(S)| + |∂S|              ([handshake])
           specialised to the r-regular case  (= r·|S|), combined with the
           odd-cut hypothesis  |∂S| >= r  when |S| is odd  (and  |∂S| >= 0
           otherwise).  In either parity  2·|E(S)| <= 2·r·⌊|S|/2⌋.
           [The handshake needs G loopless; the singleton odd-cut condition
            |∂{v}| >= r = deg(v) forces exactly that — [rgraph_loopless].]

    Hence  chromatic_index G <= maxn (mDelta G).+1 (overfull_parameter G)
                              <= maxn r.+1 r = r.+1 = edge_colourable G r.+1.

    Citation.  This is the standard specialisation of the Goldberg–Seymour
    Conjecture to r-graphs: Goldberg's Conjecture implies Seymour's r-graph
    Conjecture (χ'(G) ≤ r+1 for every r-graph).  See M. Stiebitz, D. Scheide,
    B. Toft, L. M. Favrholdt, *Graph Edge Coloring: Vizing's Theorem and
    Goldberg's Conjecture* (Wiley, 2012), Ch. 1 (the Goldberg–Seymour Conjecture
    and its consequences); P. D. Seymour, "On multicolourings of cubic graphs and
    conjectures of Fulkerson and Tutte", Proc. London Math. Soc. (3) 38 (1979)
    423–460.  Status: verified-literature (re-derived in full below; the [Qed]
    gate confirms it under the EXACT [U5.v] formulations).

    ────────────────────────────────────────────────────────────────────────────
    AUDIT of the other node pairs (no further verified-literature U5-internal
    edge exists).
    ────────────────────────────────────────────────────────────────────────────

    The §6 verified-literature edge table (OPG_FULL_FORMALIZATION_PLAN) lists only
    cycle-area edges (Petersen-colouring ⟹ Berge–Fulkerson / CDC, Berge–Fulkerson
    ⟹ CDC, strong-CDC ⟹ CDC, strong-embedding ⟹ CDC, 4-flow ⟺ 3-edge-colouring of
    cubic graphs [D1]); none has both endpoints among the nine U5 nodes (the U5
    "3-edge-colouring conjecture", Row 3, is the OPG reduction conjecture, NOT the
    Tutte 4-flow ⟺ 3-edge-colouring statement, which is the separate deferred node
    D1).  The §6 candidate edges touching U5 leave the milestone:
      • edge-list-colouring (LCC) ↔ Goldberg region — the LCC endpoint is U4
        (edge_list_coloring_statement), CROSS-milestone.
      • list-total ↔ Total-Colouring (Behzad) — the list-total endpoint is U4;
        moreover §6 records "list-total ⟹ Behzad" as FALSE-as-formalized
        (χ''_ℓ = χ'' does not yield the χ'' ≤ Δ+2 bound).  FORBIDDEN — not stated.
    The remaining pairs are unrelated: star χ'-index (Row 8) vs acyclic edge
    colouring (Row 7) carry INCOMPARABLE colour budgets (the star node fixes 6
    colours on Δ≤3 graphs, the acyclic node demands Δ+2 colours on ALL graphs), so
    neither implies the other; strong edge colouring (Row 1), the hypergraph Vizing
    generalization (Row 5), universal Steiner triple systems (Row 6) and Behzad
    (Row 9) share no textbook implication with another U5 node.  Hence exactly ONE
    verified-literature edge is internal to U5, and it is scheduled above. *)

From GraphTheory Require Import mgraph.
From GTBase Require Export base.
From Chromatic.foundations Require Import chi_bounding.
From Chromatic.conjectures Require Import U5 X33.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Multigraph double-counting toolkit (loopless handshake) *)

(** [incident] unfolded to the two endpoints. *)
Lemma incidentE (G : mgraph) (x : G) (e : edge G) :
  incident x e = (source e == x) || (target e == x).
Proof.
rewrite /incident; apply/existsP/orP.
- by case=> b Hb; case: b Hb => Hb; [right|left].
- by case=> H; [exists false|exists true].
Qed.

(** Degree as a sum of incidence indicators. *)
Lemma card_edges_at (G : mgraph) (v : G) :
  #|edges_at v| = \sum_(e : edge G) (incident v e).
Proof.
rewrite /edges_at -sum1dep_card big_mkcond /=.
by apply: eq_bigr => e _; case: (incident v e).
Qed.

(** A single point's indicator summed over a set is its membership bit. *)
Lemma indic_sum (G : mgraph) (S : {set G}) (a : G) :
  \sum_(v in S) (a == v) = (a \in S).
Proof.
under eq_bigr => v _ do rewrite eq_sym -in_set1.
rewrite preliminaries.sum_cardI; case Ha: (a \in S).
- have -> : S :&: [set a] = [set a]; [apply/setIidPr; by rewrite sub1set Ha | by rewrite cards1].
- have -> : S :&: [set a] = set0; [apply/eqP; by rewrite setI_eq0 disjoint_sym disjoints1 Ha | by rewrite cards0].
Qed.

(** For a loopless edge, the number of its endpoints inside S is the sum of the
    two endpoint-membership bits. *)
Lemma per_edge (G : mgraph) (S : {set G}) (e : edge G) :
  source e != target e ->
  \sum_(v in S) (incident v e) = (source e \in S) + (target e \in S).
Proof.
move=> Hne.
under eq_bigr => v _ do rewrite incidentE.
have key : forall v : G,
    ((source e == v) || (target e == v) : nat) = (source e == v) + (target e == v).
  move=> v; case Hs: (source e == v); case Ht: (target e == v) => //=.
  by move: Hne; rewrite (eqP Hs) (eqP Ht) eqxx.
under eq_bigr => v _ do rewrite key.
by rewrite big_split /= !indic_sum.
Qed.

(** Cardinality of a boolean-comprehension subset as a sum of its indicator. *)
Lemma cardE_sum (T : finType) (P : pred T) :
  #|[set e | P e]| = \sum_(e : T) (P e).
Proof.
rewrite -sum1dep_card big_mkcond /=.
by apply: eq_bigr => e _; case: (P e).
Qed.

(** Handshake / degree-sum identity for a loopless multigraph:
      Σ_{v∈S} deg(v) = 2·|E(S)| + |∂S|. *)
Lemma handshake (G : mgraph) (S : {set G}) :
  loopless G ->
  \sum_(v in S) #|edges_at v| = 2 * #|edge_set S| + #|edge_boundary S|.
Proof.
move=> Hll.
under eq_bigr => v _ do rewrite card_edges_at.
rewrite exchange_big /=.
under eq_bigr => e _ do rewrite (per_edge S (Hll e)).
rewrite /edge_set /edge_boundary !cardE_sum big_distrr /= -big_split /=.
by apply: eq_bigr => e _; case: (source e \in S); case: (target e \in S).
Qed.

(** ** From [is_r_graph] to the density bound *)

(** The odd-cut condition at singletons forces losslessness: |∂{v}| >= r = deg(v)
    leaves no room for a loop (a loop is incident to v but not in ∂{v}). *)
Lemma rgraph_loopless (G : mgraph) (r : nat) :
  is_r_graph G r -> loopless G.
Proof.
move=> [Hreg Hbd] e; apply/eqP => Hst.
have Hodd : odd #|[set source e]| by rewrite cards1.
have Hr := Hbd [set source e] Hodd.
have He_in : e \in edges_at (source e) by rewrite inE incidentE eqxx.
have Ht : target e == source e by rewrite eq_sym; apply/eqP.
have He_notin : e \notin edge_boundary [set source e].
  by rewrite inE !in_set1 eqxx Ht.
have Hsub2 : edge_boundary [set source e] \subset edges_at (source e) :\ e.
  apply/subsetP => f Hf; rewrite in_setD1; apply/andP; split.
  - by apply/eqP => Hfe; move: Hf; rewrite Hfe (negbTE He_notin).
  - move: Hf; rewrite !inE incidentE.
    by case: (source f == source e); case: (target f == source e).
have Hle : #|edge_boundary [set source e]| <= #|edges_at (source e) :\ e|.
  exact: subset_leq_card.
have Hr1 : 0 < r.
  by rewrite -(Hreg (source e)) card_gt0; apply/set0Pn; exists e.
have Hcard : #|edges_at (source e) :\ e| = r.-1.
  by move: (cardsD1 e (edges_at (source e))); rewrite He_in (Hreg (source e)) add1n => ->.
rewrite Hcard in Hle.
by move: (leq_trans Hr Hle); rewrite -{1}(prednK Hr1) ltnn.
Qed.

(** Density bound for an r-graph:  |E(S)| <= r·⌊|S|/2⌋  for every vertex set S. *)
Lemma edge_set_bound (G : mgraph) (r : nat) (S : {set G}) :
  is_r_graph G r -> #|edge_set S| <= r * (#|S| %/ 2).
Proof.
move=> Hrg; have Hll := rgraph_loopless Hrg; case: Hrg => Hreg Hbd.
have E : 2 * #|edge_set S| + #|edge_boundary S| = r * #|S|.
  rewrite -(handshake S Hll).
  under eq_bigr => v _ do rewrite (Hreg v).
  by rewrite sum_nat_const mulnC.
have Hro : r * (odd #|S|) <= #|edge_boundary S|.
  case Hpar: (odd #|S|); last by rewrite muln0.
  by rewrite muln1; apply: Hbd; rewrite Hpar.
have HS : r * #|S| = 2 * (r * (#|S| %/ 2)) + r * (odd #|S|).
  rewrite {1}(divn_eq #|S| 2) modn2 mulnDr; congr (_ + _).
  by rewrite mulnA mulnC.
have Hkey : 2 * #|edge_set S| <= 2 * (r * (#|S| %/ 2)).
  rewrite -(leq_add2r #|edge_boundary S|) E HS leq_add2l; exact: Hro.
by move: Hkey; rewrite !mul2n leq_double.
Qed.

(** Ceiling-division bound:  a <= r·q  ⟹  ⌈a/q⌉ <= r. *)
Lemma ceil_div_le (a q r : nat) : a <= r * q -> (a + q - 1) %/ q <= r.
Proof.
move=> Ha.
case: q Ha => [|q] Ha; first by rewrite divn0.
have ->: a + q.+1 - 1 = a + q by rewrite addnS subn1.
rewrite -ltnS ltn_divLR // mulSn addSn ltnS [a + q]addnC leq_add2l.
exact: Ha.
Qed.

(** ** The two Goldberg terms collapse to r+1 on an r-graph *)

Lemma mDelta_le (G : mgraph) (r : nat) : is_r_graph G r -> mDelta G <= r.
Proof.
move=> [Hreg _]; rewrite /mDelta; apply/bigmax_leqP => v _.
by rewrite (Hreg v).
Qed.

Lemma overfull_le (G : mgraph) (r : nat) : is_r_graph G r -> overfull_parameter G <= r.
Proof.
move=> Hrg; rewrite /overfull_parameter; apply/bigmax_leqP => S _.
rewrite /ceil_div; apply: ceil_div_le; apply: edge_set_bound; exact: Hrg.
Qed.

(** ** The scheduled edge *)

(** Goldberg ⟹ Seymour's r-graph conjecture is NOT a verified (Qed) edge against the FAITHFUL
    Seymour statement (χ' ≤ r).  Goldberg's bound is max(Δ+1, w) = max(r+1, r) = r+1 for an r-graph,
    so it yields only χ' ≤ r+1, NOT the χ' = r Seymour asserts.  The r-graph density facts
    [mDelta_le] / [overfull_le] above are genuine (both Goldberg terms ≤ r+1) but do not close the
    gap from r+1 to r.  An earlier draft stated Seymour as [edge_colourable G r.+1] (χ' ≤ r+1),
    against which the edge was trivially provable — but that endpoint WEAKENED the conjecture (now
    corrected to [edge_colourable G r]).  Recorded as a candidate; the genuine Goldberg–Seymour
    relationship is the deep Chen–Jing–Zang theorem, not this elementary bound. *)
(*@EDGE from=goldbergs_statement to=seymours_r_graph_statement kind=implies status=refuted-direction cite="Goldberg 1973; Seymour, On multicolourings of cubic graphs, Proc. LMS (3) 38 (1979) 423-460" note="REFUTED-DIRECTION (metadata wave M, 2026-09-24): Goldberg gives chi' <= r+1, not chi' = r; corpus e001 claims the wrong direction (reported upstream, meta/CORPUS_FEEDBACK.md). Earlier note: Goldberg bound gives chi'<=r+1, not the chi'=r faithful Seymour requires; deep relationship (Chen-Jing-Zang 2019), not an elementary Qed" *)

(** ** e002: X33's list total colouring bound ==> Behzad (verified)

    The carrier bridge that the earlier candidate note asked for, now proved:
    [bz_h] maps base's multigraph total graph of a SIMPLE multigraph [G]
    homomorphically into X33's total graph of the underlying simple graph
    [usimple G] (vertices to vertices, an edge to its endpoint pair -- distinct
    edges go to distinct pairs exactly because [msimple] forbids parallel edges);
    [bz_Delta] bounds [Delta (usimple G)] by [mDelta G] (every neighbour is the
    other end of an incident edge); [bz_upper] pulls X33's colouring back along
    [bz_h]; [bz_lower] is the Behzad LOWER bound (a maximum-degree vertex and its
    incident edges form a clique of the total graph).

    Closing the edge needed a guard in the TARGET statement: the unguarded
    [behzads_statement] was refutable on the EMPTY multigraph (simple, with
    [mDelta = 0] and total chromatic number [0], so the lower bound [1 <= 0]
    fails).  Wave E2b added the guard [0 < #|G|] to Row 9 of U5.v (see its
    GUARD REPAIR note and [grounding_U5.behzads_unguarded_body_refutable]);
    with it, [bz_lower] and [bz_upper] give the edge directly. *)

Section BehzadBridge.
Variable G : mgraph.

Lemma bz_incidentP (x : G) (e : edge G) :
  incident x e -> x \in [set source e; target e].
Proof. by case/existsP => -[] /eqP <-; rewrite !inE eqxx ?orbT. Qed.

Lemma bz_ends_in (lo : loopless G) (e : edge G) :
  [set source e; target e] \in x33_edge_set (usimple G).
Proof.
rewrite inE; apply/existsP; exists (source e); apply/existsP; exists (target e).
rewrite eqxx andbT; change (madj (source e) (target e)); rewrite /madj (lo e) /=.
apply/existsP; exists e; apply/andP; split; apply/existsP; [exists false | exists true] => //.
Qed.

Definition bz_h (lo : loopless G) (x : total_graph G) : x33_total_graph (usimple G) :=
  match x with
  | inl v => inl v
  | inr e => inr (exist _ [set source e; target e] (bz_ends_in lo e))
  end.

Lemma bz_h_hom (lo : loopless G) : injective (@edge_ends G) ->
  forall x y : total_graph G, x -- y -> bz_h lo x -- bz_h lo y.
Proof.
move=> inj [x|e] [y|f] //=.
- exact: bz_incidentP.
- exact: bz_incidentP.
case/andP => ef /existsP[v /andP[ve vf]]; apply/andP; split.
  by apply: contra ef => /eqP h; apply/eqP; exact: inj h.
by apply/set0Pn; exists v; rewrite inE (bz_incidentP ve) (bz_incidentP vf).
Qed.

Lemma bz_Delta : Delta (usimple G) <= mDelta G.
Proof.
apply/bigmax_leqP => x _.
pose oth (e : edge G) : G := if source e == x then target e else source e.
have sub : N(x) \subset oth @: edges_at x.
  apply/subsetP => y; rewrite inE /= /madj => /andP[xy /existsP[e /andP[xe ye]]].
  apply/imsetP; exists e; first by rewrite inE.
  move: xe ye => /existsP[b /eqP bx] /existsP[c /eqP cy].
  case: b c bx cy => -[] /= bx cy.
  - by move: xy; rewrite -bx -cy eqxx.
  - by rewrite /oth cy eq_sym (negbTE xy).
  - by rewrite /oth bx eqxx cy.
  - by move: xy; rewrite -bx -cy eqxx.
apply: leq_trans (subset_leq_card sub) _.
apply: leq_trans (leq_imset_card _ _) _.
rewrite /mDelta; exact: (@leq_bigmax G (fun v : G => #|edges_at v|) x).
Qed.

Lemma bz_upper : total_list_colouring_delta_plus_two_statement -> msimple G ->
  total_chromatic_number G <= (mDelta G).+2.
Proof.
move=> X [lo inj].
pose k := Delta (usimple G) + 2.
have hL : forall v : x33_total_graph (usimple G), k <= #|[set: 'I_k]|.
  by move=> _; rewrite cardsT card_ord.
have [g [_ hg]] := X (usimple G) 'I_k (fun _ => [set: 'I_k]) hL.
have hp : forall x y : total_graph G, x -- y -> g (bz_h lo x) != g (bz_h lo y).
  by move=> x y xy; apply: hg; exact: (@bz_h_hom lo inj x y xy).
apply: leq_trans (chi_le_palette hp) _.
by rewrite card_ord /k addn2 ltnS ltnS bz_Delta.
Qed.

Lemma bz_lower : 0 < #|G| -> (mDelta G).+1 <= total_chromatic_number G.
Proof.
move=> gpos.
have [v vE] := @eq_bigmax G (fun u => #|edges_at u|) gpos.
pose K : {set total_graph G} := inl v |: [set inr e | e in edges_at v].
have inj_inr : injective (@inr G (edge G)) by move=> e f [->].
have clK : clique K.
  move=> x y; rewrite !inE => /orP[/eqP->|/imsetP[e eE ->]] /orP[/eqP->|/imsetP[f fE ->]].
  - by rewrite eqxx.
  - by move=> _; move: fE; rewrite inE.
  - by move=> _; move: eE; rewrite inE.
  move=> ef; rewrite /= /line_rel; apply/andP; split.
    by apply: contra ef => /eqP->.
  by apply/existsP; exists v; move: eE fE; rewrite !inE => -> ->.
have cK : #|K| = (#|edges_at v|).+1.
  rewrite cardsU1 card_imset //; case: imsetP => // -[e _] //.
rewrite /total_chromatic_number /mDelta vE -cK -(chi_clique clK).
exact: sub_chi (subsetT K).
Qed.

End BehzadBridge.

Theorem total_list_colouring_delta_plus_two_implies_behzads :
  total_list_colouring_delta_plus_two_statement -> behzads_statement.
Proof.
move=> X G sG gpos; apply/andP; split; first exact: bz_lower.
exact: bz_upper X sG.
Qed.

(** ── Machine-readable edge records (extracted by meta/build_edge_graph.py) ───
    The forbidden / cross-milestone relationships audited above, recorded so the
    extractor never re-derives or mis-schedules them. *)

(*@EDGE from=total_list_colouring_delta_plus_two_statement to=behzads_statement kind=implies status=verified proof=total_list_colouring_delta_plus_two_implies_behzads cite="gc:e002" note="X33 (chi''_l of the total graph of a simple graph <= Delta+2) implies Behzad on nonempty simple multigraphs. Carrier bridge: bz_h maps base's total graph of a simple multigraph G homomorphically into X33's total graph of usimple G (msimple forbids parallel edges, so distinct edges map to distinct endpoint pairs); bz_Delta: Delta(usimple G) <= mDelta G; bz_upper: pull X33's list colouring with constant lists back along bz_h and bound chi by the palette (chi_bounding.chi_le_palette); bz_lower: the max-degree vertex and its incident edges form a clique of size mDelta+1 in the total graph. Uses the E2b guard 0 < #|G| on behzads_statement (the unguarded row was refuted by the empty multigraph)." *)
(*@EDGE from=edge_list_coloring_statement to=goldbergs_statement kind=implies status=refuted-direction cite="OPG_FULL_FORMALIZATION_PLAN §6 (edge-list-colouring/LCC <-> Goldberg region)" note="REFUTED-DIRECTION (metadata wave M, 2026-09-24): no logical implication: list chromatic index equal to chromatic index does not bound chi' by the Goldberg density. Earlier note: CROSS-MILESTONE: edge-list-colouring is U4; not a U5-internal edge" *)
(*@EDGE from=list_total_colouring_statement to=behzads_statement kind=implies status=refuted-direction cite="OPG_FULL_FORMALIZATION_PLAN §6" note="FORBIDDEN and CROSS-MILESTONE (list-total is U4): chi''_l = chi'' does not yield the chi'' <= Delta+2 bound" *)

Print Assumptions total_list_colouring_delta_plus_two_implies_behzads.

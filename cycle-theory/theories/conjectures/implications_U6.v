(** * Cycle.conjectures.implications_U6 — milestone U6 dependency-graph EDGES

    Machine-checked implication / refutation EDGES between the eleven committed
    U6 conjecture statements (see [U6.v]).  As in the digraph-theory
    [implications.v] layer and the sibling chromatic [implications_U1.v] /
    [implications_U5.v], every scheduled edge here is a *relative* theorem: a
    [Qed]-closed [Theorem A_statement -> B_statement] provable WITHOUT resolving
    (proving or refuting) either endpoint.  Bridge facts that would otherwise
    need resolving a conjecture or heavy out-of-scope machinery are carried as
    EXPLICIT hypotheses (never [Admitted], never [Axiom]); the file stays
    axiom-free.

    ════════════════════════════════════════════════════════════════════════════
    SCHEDULED EDGE (verified-literature):  Faithful cycle covers ⟹ CDC
    ════════════════════════════════════════════════════════════════════════════

      faithful_cycle_covers_statement  ⟹  cycle_double_cover_statement

    Endpoints (verbatim from [U6.v]):
      • Faithful cycle covers (Row 9):
          forall (G : mgraph) (p : edge G -> nat),
            0 < #|G| -> 0 < #|edge G| -> admissible p ->
            (forall e, ~~ odd (p e)) -> exists L, faithful_cover p L.
      • Cycle double cover (Row 11):
          forall G : mgraph,
            0 < #|G| -> 0 < #|edge G| -> bridgeless G -> exists L, cdc L.

    Mathematics.  Take the constant weighting [p ≡ 2].  Then
      (i)  [p] is EVEN everywhere ([~~ odd 2]);
      (ii) [p] is ADMISSIBLE: across every cut [δ(S)] the total is
             [\sum_(f in δS) 2 = 2·|δS|], which is even, and for each
             [e ∈ δS] one needs [2·p(e) = 4 ≤ 2·|δS|], i.e. [|δS| ≥ 2].
           A cut of size 1 around [e] would mean every UNDIRECTED walk between
           the endpoints of [e] crosses [δS] only through [e] — i.e. [e] is a
           bridge, a genuine cut edge ([ueseparates] over [uwalk], see
           [Cycle.foundations.connectivity]).  Since [G] is bridgeless, no cut
           containing an edge is a singleton, so [|δS| ≥ 2]
           ([bridgeless_cut2] below, via the combinatorial [uwalk_crosses]: an
           undirected walk whose endpoints straddle [S] must use a [δS]-edge).
    A faithful cover for [p ≡ 2] is, by definition, a list of circuits covering
    each edge exactly [p(e) = 2] times — that is exactly a cycle double cover.

    Citation.  The Faithful Cover Conjecture (Seymour; Alspach–Goddyn–Zhang,
    "Graphs with the circuit cover property", Trans. AMS 344 (1994) 131–154)
    specialises at [p ≡ 2] to the Cycle Double Cover Conjecture (Seymour 1979;
    Szekeres 1973).  Status: verified-literature (re-derived in full below; the
    [Qed] gate confirms it under the EXACT [U6.v] formulations).

    ────────────────────────────────────────────────────────────────────────────
    AUDIT of the other node pairs (no further verified-literature U6-internal
    edge compiles under the committed formulations).
    ────────────────────────────────────────────────────────────────────────────

    The §6 verified-literature table lists, for the cycle area:
      Petersen-colouring ⟹ Berge–Fulkerson / ⟹ CDC, Berge–Fulkerson ⟹ CDC
      (all U10 endpoints — CROSS-milestone), strong-k-CDC ⟹ CDC,
      circular/strong-embedding ⟹ CDC (no embedding node in U6), and the
      D1 4-flow ⟺ 3-edge-colouring.  Only strong-5-CDC ⟹ CDC is U6-internal
      (Row 10 ⟹ Row 11), but it does NOT compile under the committed
      formulations: Row 10 [strong_5_cycle_double_cover_statement] is restricted
      to CUBIC graphs and produces EVEN-SUBGRAPH cover members, whereas Row 11
      [cdc] quantifies over ALL bridgeless graphs and demands single-CIRCUIT
      members — so the universally-quantified Row-10 hypothesis cannot be applied
      to an arbitrary (non-cubic) bridgeless graph, and the member shapes differ.
      Forcing that edge would mis-state it; recorded below as a candidate, not
      scheduled.  Likewise the (5,2)-cover (Row 7) and CDC (Row 11) differ in
      member shape (even subgraph vs circuit) and in the fixed size-5 budget, so
      neither implies the other.  Hence exactly ONE verified-literature edge is
      internal to U6, and it is scheduled above. *)

From GraphTheory Require Import mgraph.
From GTBase Require Export base.
From Cycle.foundations Require Import cycle_space comp_reduce.
From Cycle.conjectures Require Import U6 X212 U10.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Bridgeless ⟹ every cut around an edge has size ≥ 2 *)

Lemma bridgeless_cut2 (G : mgraph) (S : {set G}) (e : edge G) :
  bridgeless G -> e \in cut S -> 2 <= #|cut S|.
Proof.
move=> Hbl Hin.
rewrite leqNgt; apply/negP => Hlt.
have Hge1 : 0 < #|cut S| by apply/card_gt0P; exists e.
have Hc1 : #|cut S| = 1.
  by apply/eqP; rewrite eqn_leq Hge1 andbT -ltnS.
have Heq : cut S = [set e].
  by apply/eqP; rewrite eq_sym eqEcard sub1set Hin cards1 Hc1.
apply: (Hbl e); rewrite /is_bridge => w Hw.
have Hxy : (source e \in S) != (target e \in S).
  by move: Hin; rewrite inE; case: (source e \in S); case: (target e \in S).
have [f Hfw Hfc] := uwalk_crosses Hw Hxy.
by exists f; [rewrite -Heq | exact: Hfw].
Qed.

(** ** Bridgeless ⟹ the constant weighting [p ≡ 2] is admissible *)

Lemma bridgeless_admissible2 (G : mgraph) :
  bridgeless G -> admissible (fun _ : edge G => 2).
Proof.
move=> Hbl S e Hin.
have H2 := bridgeless_cut2 Hbl Hin.
rewrite sum_nat_const; split.
- by rewrite leq_mul2r /=.
- by rewrite oddM andbF.
Qed.

(** ** The scheduled edge *)

(*@EDGE from=faithful_cycle_covers_statement to=cycle_double_cover_statement kind=implies status=verified-literature proved=true proof=faithful_cycle_covers_implies_cycle_double_cover cite="Seymour 1979; Alspach-Goddyn-Zhang, Graphs with the circuit cover property, Trans. AMS 344 (1994) 131-154; Szekeres 1973" note="Faithful Cover Conjecture at the even weighting p==2 is exactly the Cycle Double Cover Conjecture; bridgeless => p==2 admissible via the walk/cut crossing lemma" *)
Theorem faithful_cycle_covers_implies_cycle_double_cover :
  faithful_cycle_covers_statement -> cycle_double_cover_statement.
Proof.
move=> Hf G Hn He Hbl.
have Hadm := bridgeless_admissible2 Hbl.
have Heven : forall e : edge G, ~~ odd ((fun _ : edge G => 2) e) by [].
have [L HL] := Hf G (fun _ : edge G => 2) Hn He Hadm Heven.
by exists L; exact: HL.
Qed.

(** ================================================================= *)
(** ** (5,2)-cycle cover  =>  cycle double cover  (Row 7 => Row 11)

    The only gap between the two committed bodies is the MEMBER SHAPE: Row 7
    produces five EVEN SUBGRAPHS covering every edge twice, Row 11 demands a
    list of single CIRCUITS doing so.  The bridge is the foundation theorem
    [cycle_space.even_circuit_decomposition] (F14): every even subgraph is
    partitioned by a list of circuits.  Refining the five members one by one
    ([cycle_space.even_list_circuit_decomposition]) keeps every per-edge
    multiplicity, so the concatenated list of circuits still covers each edge
    exactly twice — a cycle double cover.  No hypothesis is lost: both rows
    assume exactly [0 < #|G|], [0 < #|edge G|] and [bridgeless G]. *)

(*@EDGE from=m_n_cycle_covers_statement to=cycle_double_cover_statement kind=implies status=verified proof=m_n_cycle_covers_implies_cycle_double_cover cite="gc:e084" note="Same hypothesis class (bridgeless, one vertex, one edge); the (5,2)-cover's five EVEN SUBGRAPHS are refined into CIRCUITS by the foundation theorem cycle_space.even_circuit_decomposition (F14: a nonempty even subgraph contains a circuit, by a maximal simple route whose last vertex has an unused incident edge, and induction on the edge count), which preserves every per-edge multiplicity, so the concatenation is a cdc" *)
Theorem m_n_cycle_covers_implies_cycle_double_cover :
  m_n_cycle_covers_statement -> cycle_double_cover_statement.
Proof.
move=> Hm G Hn He Hbl.
have [L [Lsize Leven Lcount]] := Hm G Hn He Hbl.
have [M [Mcirc Mcount]] := even_list_circuit_decomposition Leven.
exists M; split; first exact: Mcirc.
by move=> e; rewrite Mcount Lcount.
Qed.

(** ================================================================= *)
(** ** The cubic reduction of the (5,2)-cover property (external) *)

(** The conclusion shared by Row 7 and (up to the extra "contains the given
    circuit" clause) Row 10: a double cover by five even subgraphs. *)
Definition u6_five_even_cover (G : mgraph) : Prop :=
  exists L : seq {set edge G},
    [/\ size L = 5,
        (forall C, C \in L -> even_subgraph C)
      & (forall e : edge G, count (fun C : {set edge G} => e \in C) L = 2)].

(** External theorem: F. Jaeger, A survey of the cycle double cover conjecture,
    in Cycles in Graphs, Ann. Discrete Math. 27 (1985) 1-12
    (DOI 10.1016/S0304-0208(08)72993-1), Section 2; see also C.-Q. Zhang,
    Integer Flows and Cycle Covers of Graphs, Marcel Dekker 1997, Chapter 3
    (the reduction of the cycle-double-cover and k-cycle-double-cover problems
    to CUBIC bridgeless graphs, by suppressing vertices of degree two and
    splitting vertices of degree at least four, a splitting that preserves
    bridgelessness by Fleischner's lemma and under which a cover of the cubic
    expansion restricts to a cover of the original graph).
    Claim: if every cubic bridgeless multigraph with at least one vertex and at
    least one edge has a double cover by five even subgraphs, then so does every
    bridgeless multigraph with at least one vertex and at least one edge.
    Not formalized here: it is carried as an explicit hypothesis of the two
    conditional edges below (never an [Axiom], never [Admitted]), which is why
    they are [status=conditional external=...] rather than [verified]. *)
Definition external_five_even_cover_cubic_reduction_statement : Prop :=
  (forall G : mgraph,
     (0 < #|G|)%N -> (0 < #|edge G|)%N -> cubic G -> bridgeless G ->
     u6_five_even_cover G) ->
  (forall G : mgraph,
     (0 < #|G|)%N -> (0 < #|edge G|)%N -> bridgeless G -> u6_five_even_cover G).

(** A cubic multigraph with an edge contains a circuit: no vertex has degree 1
    (all have degree 3), so [cycle_space.has_circuit] applies to the full edge
    set. *)
Lemma cubic_has_circuit (G : mgraph) :
  (0 < #|edge G|)%N -> cubic G ->
  exists D : {set edge G}, is_circuit D.
Proof.
move=> He [_ Hreg].
have Cdeg : forall v : G, subdeg [set: edge G] v != 1.
  move=> v; have e3 : subdeg [set: edge G] v = 3 by exact: Hreg v.
  by rewrite e3.
have Tn0 : [set: edge G] != set0 by rewrite -card_gt0 cardsT.
by have [D [_ Dcirc]] := has_circuit Tn0 Cdeg; exists D.
Qed.

(*@EDGE from=strong_5_cycle_double_cover_statement to=m_n_cycle_covers_statement kind=implies status=conditional external="external_five_even_cover_cubic_reduction_statement" proof=strong_5_cycle_double_cover_implies_m_n_cycle_covers cite="gc:e085" note="Row 10 is cubic-only and needs a circuit to start from: cubic_has_circuit supplies one (cycle_space.has_circuit on the full edge set, every degree being 3, hence never 1), and dropping Row 10's extra 'some member contains C' clause leaves exactly a (5,2)-cover of every cubic bridgeless graph; the cubic-to-general step is the cited external reduction" *)
Theorem strong_5_cycle_double_cover_implies_m_n_cycle_covers :
  external_five_even_cover_cubic_reduction_statement ->
  strong_5_cycle_double_cover_statement -> m_n_cycle_covers_statement.
Proof.
move=> Hred Hs; apply: Hred => G Hn He Hc Hbl.
have [D Dcirc] := cubic_has_circuit He Hc.
have [L [Lsize Leven Lcount _]] := Hs G D Hn Hc Hbl Dcirc.
by exists L; split.
Qed.

(*@EDGE from=strong_5_cycle_double_cover_statement to=cycle_double_cover_statement kind=implies status=conditional external="external_five_even_cover_cubic_reduction_statement" proof=strong_5_cycle_double_cover_implies_cycle_double_cover cite="gc:e086" note="Composition of gc:e085 (Row 10 => Row 7, cubic reduction carried as the external) with the unconditional gc:e084 (Row 7 => Row 11, the even-subgraph-to-circuits refinement F14)" *)
Theorem strong_5_cycle_double_cover_implies_cycle_double_cover :
  external_five_even_cover_cubic_reduction_statement ->
  strong_5_cycle_double_cover_statement -> cycle_double_cover_statement.
Proof.
move=> Hred Hs; apply: m_n_cycle_covers_implies_cycle_double_cover.
exact: strong_5_cycle_double_cover_implies_m_n_cycle_covers Hred Hs.
Qed.

(** ================================================================= *)
(** ** Small cycle double cover (bm-013) => cycle double cover (external) *)

(** External theorem: F. Jaeger, A survey of the cycle double cover conjecture,
    in Cycles in Graphs, Ann. Discrete Math. 27 (1985) 1-12
    (DOI 10.1016/S0304-0208(08)72993-1), Section 2; see also C.-Q. Zhang,
    Integer Flows and Cycle Covers of Graphs, Marcel Dekker 1997, Chapter 3
    (the cycle double cover conjecture reduces to SIMPLE, indeed simple cubic
    3-connected, graphs: a loop is a circuit and may be covered twice on its
    own, vertices of degree two are suppressed and parallel edges are subdivided
    or split away without affecting bridgelessness).
    Claim: if every simple bridgeless multigraph with at least one vertex has a
    cycle double cover, then so does every bridgeless multigraph with at least
    one vertex and at least one edge.
    Not formalized here: it is carried as an explicit hypothesis of the
    conditional edge below (never an [Axiom], never [Admitted]), which is why
    that edge is [status=conditional external=...] rather than [verified]. *)
Definition external_cdc_simple_reduction_statement : Prop :=
  (forall G : mgraph,
     (0 < #|G|)%N -> simple_mgraph G -> bridgeless G ->
     exists L : seq {set edge G}, cdc L) ->
  (forall G : mgraph,
     (0 < #|G|)%N -> (0 < #|edge G|)%N -> bridgeless G ->
     exists L : seq {set edge G}, cdc L).

(*@EDGE from=small_cycle_double_cover_statement to=cycle_double_cover_statement kind=implies status=conditional external="external_cdc_simple_reduction_statement" proof=small_cycle_double_cover_implies_cycle_double_cover cite="gc:e209" note="bm-013 gives, for every SIMPLE bridgeless multigraph, a cycle double cover with at most #|G|-1 members; forgetting the size bound gives the simple case of Row 11, and the simple-to-general step is the cited external reduction of the CDC to simple graphs" *)
Theorem small_cycle_double_cover_implies_cycle_double_cover :
  external_cdc_simple_reduction_statement ->
  small_cycle_double_cover_statement -> cycle_double_cover_statement.
Proof.
move=> Hred Hs; apply: Hred => G Hn Hsimp Hbl.
by have [L [HL _]] := Hs G Hn Hsimp Hbl; exists L.
Qed.

(** ================================================================= *)
(** ** Orientable five cycle double cover (bm-026) => (5,2)-cover and CDC

    Two gaps separate [X212.orientable_five_cycle_double_cover_statement] from
    Row 7 and Row 11 of [U6.v].

    (i) The ORIENTATIONS and the [{set (edge G)}]-valued family indexed by
    ['I_5] are simply forgotten: the five members, listed as
    [map C (index_enum 'I_5)], are even subgraphs, and the index count
    [#|[set i | e \in C i]| = 2] is the list count
    ([cycle_space.card_count_enum]).

    (ii) The HYPOTHESIS CLASS: bm-026 assumes [two_edge_connected G]
    ([mconnected] and [bridgeless]) while Rows 7 and 11 assume only
    [bridgeless].  This gap is CLOSED, not carried: by
    [comp_reduce.five_even_cover_connected_reduce], a bridgeless [G] is
    collapsed onto the connected bridgeless multigraph [Hc r0] obtained by
    identifying one representative vertex per component with a single vertex,
    which has the SAME EDGE TYPE, so a double cover of [Hc r0] by five even
    subgraphs IS one of [G]: at a non-representative vertex the two
    subgraph-degrees are literally equal, and at a representative the
    [G]-degree is even because the degree sum over its whole component is even
    (no [G]-edge crosses a component, [comp_reduce.cut_mcomp]) while every other
    summand is.

    Row 11 is then reached by composing with the unconditional gc:e084. *)

(*@EDGE from=orientable_five_cycle_double_cover_statement to=m_n_cycle_covers_statement kind=implies status=verified proof=orientable_five_cycle_double_cover_implies_m_n_cycle_covers cite="gc:e238" note="Forget the orientations and reindex the 'I_5-family as the list map C (index_enum 'I_5) (cycle_space.card_count_enum turns the index count into the list count); the two_edge_connected-versus-bridgeless gap is closed by comp_reduce.five_even_cover_connected_reduce, which collapses one representative vertex per component onto a single vertex, keeping the edge type, bridgelessness and connectivity, and transports evenness back by the component degree-sum argument" *)
Theorem orientable_five_cycle_double_cover_implies_m_n_cycle_covers :
  orientable_five_cycle_double_cover_statement -> m_n_cycle_covers_statement.
Proof.
move=> Ho G Hn He Hbl.
apply: (five_even_cover_connected_reduce _ Hn Hbl) => H HnH HconnH HblH.
have [C [d [Ceven _ Ccount _]]] := Ho H HnH (conj HconnH HblH).
exists (map C (index_enum 'I_5)); split.
- by rewrite size_map size_index_enum_ord.
- by move=> D /mapP[i _ ->]; exact: Ceven i.
- move=> e; rewrite count_map -card_count_enum -cardsE.
  exact: Ccount e.
Qed.

(*@EDGE from=orientable_five_cycle_double_cover_statement to=cycle_double_cover_statement kind=implies status=verified proof=orientable_five_cycle_double_cover_implies_cycle_double_cover cite="gc:e218" note="Composition of gc:e238 (forget the orientations, close the two_edge_connected-versus-bridgeless gap by the component collapse comp_reduce.five_even_cover_connected_reduce) with gc:e084 (refine the five even subgraphs into circuits by F14, cycle_space.even_circuit_decomposition)" *)
Theorem orientable_five_cycle_double_cover_implies_cycle_double_cover :
  orientable_five_cycle_double_cover_statement -> cycle_double_cover_statement.
Proof.
move=> Ho; apply: m_n_cycle_covers_implies_cycle_double_cover.
exact: orientable_five_cycle_double_cover_implies_m_n_cycle_covers Ho.
Qed.

(** ================================================================= *)
(** ** gc:e090 / gc:e091 -- Petersen colouring => (5,2)-cover => CDC

    A Petersen colouring [f] of a cubic graph maps the three edges at every
    vertex to three pairwise adjacent Petersen edges, i.e. (the Petersen graph
    being triangle-free, [petersen_triangle_free]) to a CLAW
    ([petersen_claw]).  The Petersen graph has a double cover by five even
    subgraphs, given below by labelling each Petersen edge with the 2-subset of
    ['I_5] of the members containing it ([plab]); at every Petersen vertex the
    three labels are the three 2-subsets of a 3-set, so every member meets
    every claw in 0 or 2 edges ([plab_claw_even]) and every edge lies in
    exactly two members ([plab_card]).  Pulling the five members back along
    [f] gives five even subgraphs of the cubic graph covering every edge
    exactly twice ([petersen_pullback_cover]).  The finite Petersen data is
    checked on 5-bit CODES of the 2-subsets ([pcode]), by closed [compute]
    checks on small numbers ([pnbr_check], [plab_check], [pclaw_check]), never
    by computing on finite sets.  The source row is cubic-only, so reaching
    Row 7 for all bridgeless graphs uses the same cited cubic reduction as
    gc:e085, [external_five_even_cover_cubic_reduction_statement]. *)

(** ** Claws of the Petersen graph *)

Lemma padj_neq (x y : petersenV) : padj x y -> x != y.
Proof. by apply: contraTneq => ->; rewrite padj_irrefl. Qed.

(** Two distinct members of a two-element support span it. *)
Lemma set2_span (T : finType) (x z u w : T) :
  u \in [set x; z] -> w \in [set x; z] -> u != w -> [set x; z] = [set u; w].
Proof.
rewrite !inE => /orP[] /eqP -> /orP[] /eqP ->; rewrite ?eqxx // => _.
by apply/setP => t; rewrite !inE orbC.
Qed.

Lemma psuppE (q : Pedge) : psupp q = [set (val q).1; (val q).2].
Proof. by []. Qed.

Lemma psupp_adj (q : Pedge) (u w : petersenV) :
  u \in psupp q -> w \in psupp q -> u != w -> padj u w.
Proof.
have hq : padj (val q).1 (val q).2 := valP q.
have hq' : padj (val q).2 (val q).1 by rewrite padj_sym.
by rewrite !inE => /orP[] /eqP -> /orP[] /eqP ->; rewrite ?eqxx.
Qed.

(** The Petersen graph (Kneser KG(5,2)) is triangle-free: three pairwise
    disjoint 2-subsets of a 5-set do not exist. *)
Lemma petersen_triangle_free (a b c : petersenV) :
  padj a b -> padj b c -> padj a c -> False.
Proof.
rewrite /padj => hab hbc hac.
have ca : #|val a| = 2 by apply/eqP; exact: valP a.
have cb : #|val b| = 2 by apply/eqP; exact: valP b.
have cc : #|val c| = 2 by apply/eqP; exact: valP c.
have h1 : #|val a :|: val b| = 4.
  by rewrite cardsU (disjoint_setI0 hab) cards0 ca cb.
have hd : (val a :|: val b) :&: val c = set0.
  by rewrite setIUl (disjoint_setI0 hac) (disjoint_setI0 hbc) setU0.
have h2 : #|val a :|: val b :|: val c| = 6.
  by rewrite cardsU hd cards0 h1 cc.
by move: (max_card (val a :|: val b :|: val c)); rewrite h2 card_ord.
Qed.

(** Three pairwise adjacent Petersen edges form a claw: they share a vertex,
    and their other ends are three distinct neighbours of it. *)
Lemma petersen_claw (q1 q2 q3 : Pedge) :
  mut_adj3 Padj q1 q2 q3 ->
  exists p y1 y2 y3 : petersenV,
    [/\ psupp q1 = [set p; y1], psupp q2 = [set p; y2], psupp q3 = [set p; y3],
        [/\ padj p y1, padj p y2 & padj p y3]
      & [/\ y1 != y2, y2 != y3 & y1 != y3]].
Proof.
case/and3P => /andP[n12 /set0Pn[p hp12]] /andP[n23 /set0Pn[r hr23]]
             /andP[n13 /set0Pn[s hs13]].
move: hp12 hr23 hs13; rewrite !in_setI => /andP[p1 p2] /andP[r2 r3] /andP[s1 s3].
(* other end of an edge through a given vertex *)
have other : forall (q : Pedge) (u : petersenV), u \in psupp q ->
    exists y, psupp q = [set u; y] /\ padj u y.
  move=> q u hu.
  have hq := valP q.
  move: (hu); rewrite !inE => /orP[] /eqP hux.
  - exists (val q).2; rewrite -hux in hq; split => //.
    by rewrite /psupp hux.
  - exists (val q).1; rewrite -hux padj_sym in hq; split => //.
    by rewrite /psupp hux; apply/setP => t; rewrite !inE orbC.
case: (boolP (p \in psupp q3)) => p3.
  have [y1 [e1 a1]] := other q1 p p1.
  have [y2 [e2 a2]] := other q2 p p2.
  have [y3 [e3 a3]] := other q3 p p3.
  exists p, y1, y2, y3; split => //.
  split; [move: n12 | move: n23 | move: n13];
    by rewrite ?e1 ?e2 ?e3; apply: contra => /eqP ->.
exfalso.
have rp : r != p by apply: contraNneq p3 => <-.
have sp : s != p by apply: contraNneq p3 => <-.
have e1 : psupp q1 = [set p; s].
  by rewrite psuppE (set2_span p1 s1) // eq_sym.
have e2 : psupp q2 = [set p; r].
  by rewrite psuppE (set2_span p2 r2) // eq_sym.
have rs : r != s by apply: contraNneq n12 => hrs; rewrite e1 e2 hrs.
apply: (@petersen_triangle_free p s r).
- by apply: (@psupp_adj q1); rewrite // eq_sym.
- by apply: (@psupp_adj q3); rewrite // eq_sym.
- by apply: (@psupp_adj q2); rewrite // eq_sym.
Qed.

(** ** Bit codes of the subsets of ['I_5]

    A subset [X] of ['I_5] is coded by the number [pcode X = sum_(i in X) 2^i];
    membership is the [i]-th bit.  All finite checks below are closed boolean
    computations on these small NUMBERS, never on finite sets. *)

Definition pbit (k c : nat) : bool := odd (c %/ 2 ^ k).
Definition ppopc (c : nat) : nat :=
  pbit 0 c + pbit 1 c + pbit 2 c + pbit 3 c + pbit 4 c.
Definition pcode (X : {set 'I_5}) : nat := \sum_(i < 5) (i \in X) * 2 ^ i.
Definition penc (b0 b1 b2 b3 b4 : bool) : nat :=
  b0 + b1 * 2 + b2 * 4 + b3 * 8 + b4 * 16.

Lemma sum5 (F : 'I_5 -> nat) :
  \sum_(i < 5) F i
  = F (inord 0) + (F (inord 1) + (F (inord 2) + (F (inord 3) + F (inord 4)))).
Proof.
rewrite !big_ord_recl big_ord0 addn0.
by congr (_ + (_ + (_ + (_ + _)))); congr F; apply: val_inj; rewrite /= inordK.
Qed.

Lemma pcodeE (X : {set 'I_5}) :
  pcode X = penc (inord 0 \in X) (inord 1 \in X) (inord 2 \in X)
                 (inord 3 \in X) (inord 4 \in X).
Proof. by rewrite /pcode sum5 /penc !inordK // expn0 muln1 expn1 !addnA. Qed.

Lemma penc_bits (b0 b1 b2 b3 b4 : bool) :
  [/\ pbit 0 (penc b0 b1 b2 b3 b4) = b0, pbit 1 (penc b0 b1 b2 b3 b4) = b1,
      pbit 2 (penc b0 b1 b2 b3 b4) = b2, pbit 3 (penc b0 b1 b2 b3 b4) = b3
    & pbit 4 (penc b0 b1 b2 b3 b4) = b4].
Proof. by case: b0; case: b1; case: b2; case: b3; case: b4; split. Qed.

Lemma pbit_code (X : {set 'I_5}) (i : 'I_5) : pbit i (pcode X) = (i \in X).
Proof.
rewrite pcodeE.
case: (penc_bits (inord 0 \in X) (inord 1 \in X) (inord 2 \in X)
                 (inord 3 \in X) (inord 4 \in X)) => h0 h1 h2 h3 h4.
rewrite -[i in RHS]inord_val.
move: (nat_of_ord i) (ltn_ord i) => k.
by case: k => [|[|[|[|[|k]]]]] hk //; rewrite ?h0 ?h1 ?h2 ?h3 ?h4.
Qed.

Lemma pbit_code_lt (X : {set 'I_5}) (k : nat) :
  (k < 5)%N -> pbit k (pcode X) = (inord k \in X).
Proof. by move=> hk; rewrite -(pbit_code X (inord k)) inordK. Qed.

Lemma card_pcode (X : {set 'I_5}) : #|X| = ppopc (pcode X).
Proof.
rewrite /ppopc !pbit_code_lt // -sum1_card big_mkcond sum5 /=.
by rewrite !addnA.
Qed.

Lemma pcode_inj (X Y : {set 'I_5}) : pcode X = pcode Y -> X = Y.
Proof. by move=> h; apply/setP => i; rewrite -!pbit_code h. Qed.

Lemma pbit_set (c k : nat) :
  (k < 5)%N -> pbit k (pcode [set i : 'I_5 | pbit i c]) = pbit k c.
Proof. by move=> hk; rewrite pbit_code_lt // inE inordK. Qed.

Definition pC2 : seq nat := [:: 3; 5; 6; 9; 10; 12; 17; 18; 20; 24].

Lemma pcode_C2 (X : {set 'I_5}) : #|X| = 2 -> pcode X \in pC2.
Proof.
move=> h.
suff /implyP : (ppopc (pcode X) == 2) ==> (pcode X \in pC2).
  by apply; rewrite -card_pcode h.
rewrite pcodeE /ppopc.
case: (penc_bits (inord 0 \in X) (inord 1 \in X) (inord 2 \in X)
                 (inord 3 \in X) (inord 4 \in X)) => -> -> -> -> ->.
by case: (inord 0 \in X); case: (inord 1 \in X); case: (inord 2 \in X);
   case: (inord 3 \in X); case: (inord 4 \in X).
Qed.

Definition pdisj (c d : nat) : bool :=
  all (fun k => ~~ (pbit k c && pbit k d)) (iota 0 5).

Lemma pdisj_code (X Y : {set 'I_5}) :
  [disjoint X & Y] -> pdisj (pcode X) (pcode Y).
Proof.
move=> h; apply/allP => k; rewrite mem_iota add0n => /andP[_ hk].
rewrite !pbit_code_lt //.
by case hx : (inord k \in X) => //=; rewrite (disjointFr h hx).
Qed.

(** ** The (5,2)-cover of the Petersen graph, as a table on codes

    [ptbl a b] (for [a < b] the codes of two adjacent Petersen vertices) is the
    code of the 2-subset of ['I_5] labelling that Petersen edge: the edge lies
    in the members [i] of the five even subgraphs with [i] in its label.  At
    every vertex the three labels are the three 2-subsets of a 3-set, so every
    member meets every claw in 0 or 2 edges. *)
Definition ptbl (a b : nat) : nat :=
  match a, b with
  | 3, 12 => 3 | 3, 20 => 5 | 3, 24 => 6 | 5, 10 => 3 | 5, 18 => 9
  | 5, 24 => 10 | 6, 9 => 20 | 6, 17 => 24 | 6, 24 => 12 | 9, 18 => 24
  | 9, 20 => 12 | 10, 17 => 10 | 10, 20 => 9 | 12, 17 => 18 | 12, 18 => 17
  | _, _ => 0
  end.

Definition plc (a b : nat) : nat := ptbl (minn a b) (maxn a b).

(** The three neighbours of each Petersen vertex, on codes. *)
Definition pnbr (c : nat) : seq nat :=
  match c with
  | 3 => [:: 12; 20; 24] | 5 => [:: 10; 18; 24] | 6 => [:: 9; 17; 24]
  | 9 => [:: 6; 18; 20] | 10 => [:: 5; 17; 20] | 12 => [:: 3; 17; 18]
  | 17 => [:: 6; 10; 12] | 18 => [:: 5; 9; 12] | 20 => [:: 3; 9; 10]
  | 24 => [:: 3; 5; 6] | _ => [::]
  end.

Lemma pnbr_check :
  all (fun c => all (fun d => pdisj c d ==> (d \in pnbr c)) pC2) pC2.
Proof. by compute. Qed.

Lemma plab_check : all (fun c => all (fun d => ppopc (plc c d) == 2) (pnbr c)) pC2.
Proof. by compute. Qed.

Lemma pclaw_check :
  all (fun c => all (fun d1 => all (fun d2 => all (fun d3 =>
      [&& d1 != d2, d2 != d3 & d1 != d3] ==>
      all (fun k => ~~ odd (pbit k (plc c d1) + pbit k (plc c d2)
                            + pbit k (plc c d3))) (iota 0 5))
    (pnbr c)) (pnbr c)) (pnbr c)) pC2.
Proof. by compute. Qed.

(** ** The labels of Petersen edges *)

Definition plabX (X Y : {set 'I_5}) : {set 'I_5} :=
  [set i : 'I_5 | pbit i (plc (pcode X) (pcode Y))].

Definition plab (q : Pedge) : {set 'I_5} := plabX (val (val q).1) (val (val q).2).

Lemma plabXC (X Y : {set 'I_5}) : plabX X Y = plabX Y X.
Proof. by rewrite /plabX /plc minnC maxnC. Qed.

Lemma card_plabX (X Y : {set 'I_5}) : #|plabX X Y| = ppopc (plc (pcode X) (pcode Y)).
Proof. by rewrite card_pcode /ppopc !pbit_set. Qed.

Lemma pcode_V (p : petersenV) : pcode (val p) \in pC2.
Proof. exact: pcode_C2 (eqP (valP p)). Qed.

Lemma pcode_nbr (p y : petersenV) :
  padj p y -> pcode (val y) \in pnbr (pcode (val p)).
Proof.
move=> a; move/allP: pnbr_check => /(_ _ (pcode_V p)).
by move/allP/(_ _ (pcode_V y))/implyP; apply; exact: pdisj_code a.
Qed.

(** Every label is a 2-subset of ['I_5]: each Petersen edge lies in exactly
    two of the five members. *)
Lemma plab_card (q : Pedge) : #|plab q| = 2.
Proof.
rewrite /plab card_plabX.
have a : padj (val q).1 (val q).2 := valP q.
by move/allP: plab_check => /(_ _ (pcode_V (val q).1)) /allP /(_ _ (pcode_nbr a)) /eqP.
Qed.

Lemma plab_supp (q : Pedge) (p y : petersenV) :
  psupp q = [set p; y] -> plab q = plabX (val p) (val y).
Proof.
move=> e.
have a : padj (val q).1 (val q).2 := valP q.
have n : (val q).1 != (val q).2 := padj_neq a.
have h1 : (val q).1 \in [set p; y] by rewrite -e /psupp set21.
have h2 : (val q).2 \in [set p; y] by rewrite -e /psupp set22.
rewrite /plab; move: h1 h2 n; rewrite !inE => /orP[] /eqP -> /orP[] /eqP ->;
  rewrite ?eqxx // => _.
exact: plabXC.
Qed.

(** Every member of the Petersen (5,2)-cover meets every claw -- three
    pairwise adjacent Petersen edges -- in an even number of edges. *)
Lemma plab_claw_even (q1 q2 q3 : Pedge) (i : 'I_5) :
  mut_adj3 Padj q1 q2 q3 ->
  ~~ odd ((i \in plab q1) + (i \in plab q2) + (i \in plab q3)).
Proof.
move=> /petersen_claw [p [y1 [y2 [y3 [e1 e2 e3 [a1 a2 a3] [d12 d23 d13]]]]]].
rewrite (plab_supp e1) (plab_supp e2) (plab_supp e3) !inE.
have hd : forall y y' : petersenV, y != y' -> pcode (val y) != pcode (val y').
  by move=> y y'; apply: contraNneq => /pcode_inj/val_inj ->.
move/allP: pclaw_check => /(_ _ (pcode_V p)) /= /allP /(_ _ (pcode_nbr a1))
  /= /allP /(_ _ (pcode_nbr a2)) /= /allP /(_ _ (pcode_nbr a3)).
rewrite (hd _ _ d12) (hd _ _ d23) (hd _ _ d13) => /implyP /(_ isT).
move: (ltn_ord i); move: (nat_of_ord i) => k.
by case: k => [|[|[|[|[|k]]]]] hk // /and5P[h0 h1 h2 h3 /andP[h4 _]].
Qed.

(** ** Pulling the Petersen (5,2)-cover back along a Petersen colouring *)

(** A Petersen colouring, as in the source row. *)
Definition pcol (G : mgraph) (f : edge G -> Pedge) : Prop :=
  forall e1 e2 e3 : edge G,
    mut_adj3 (@line_rel G) e1 e2 e3 -> mut_adj3 Padj (f e1) (f e2) (f e3).

Definition ppull (G : mgraph) (f : edge G -> Pedge) (i : 'I_5) : {set edge G} :=
  [set e | i \in plab (f e)].

(** The three edges at a vertex of a cubic multigraph. *)
Lemma cubic_edges_at (G : mgraph) (Gcubic : cubic G) (v : G) :
  exists e1 e2 e3 : edge G,
    [/\ edges_at v = e1 |: [set e2; e3], e1 != e2, e2 != e3 & e1 != e3].
Proof.
case: Gcubic => hll hdeg.
have h3 : #|edges_at v| = 3.
  by rewrite -(hdeg v) /mdeg (subdeg_loopless _ _ hll) setIT.
have /card_gt0P[e1 he1] : (0 < #|edges_at v|)%N by rewrite h3.
have /cards2P[e2 [e3 [h23 h]]] : #|edges_at v :\ e1| == 2.
  by move: h3; rewrite (cardsD1 e1) he1 add1n => /eqP h; exact: h.
exists e1, e2, e3.
have h2 : e2 \in edges_at v :\ e1 by rewrite h set21.
have h3' : e3 \in edges_at v :\ e1 by rewrite h set22.
move: h2 h3'; rewrite !inE => /andP[n12 _] /andP[n13 _].
split => //; last by rewrite eq_sym.
- by rewrite -h setD1K.
- by rewrite eq_sym.
Qed.

Lemma ppull_even (G : mgraph) (f : edge G -> Pedge) (Gcubic : cubic G)
    (fcol : pcol f) (i : 'I_5) : even_subgraph (ppull f i).
Proof.
move=> v; case: (Gcubic) => hll _.
have [e1 [e2 [e3 [hE n12 n23 n13]]]] := cubic_edges_at Gcubic v.
have hinc : forall e, e \in (e1 |: [set e2; e3]) -> incident v e.
  by move=> e; rewrite -hE inE.
have ladj : forall a b, a \in (e1 |: [set e2; e3]) -> b \in (e1 |: [set e2; e3]) ->
    a != b -> line_rel a b.
  move=> a b ha hb nab; rewrite /line_rel nab /=.
  by apply/existsP; exists v; rewrite !hinc.
have hm : mut_adj3 (@line_rel G) e1 e2 e3.
  by apply/and3P; split; apply: ladj; rewrite ?inE ?eqxx ?orbT.
have := plab_claw_even i (fcol _ _ _ hm).
rewrite (subdeg_loopless _ _ hll) hE card_setI_sum.
rewrite big_setU1 /=; last by rewrite !inE negb_or n12 n13.
rewrite big_setU1 /=; last by rewrite inE.
by rewrite big_set1 !inE addnA.
Qed.

Lemma ppull_count (G : mgraph) (f : edge G -> Pedge) (e : edge G) :
  #|[set i : 'I_5 | e \in ppull f i]| = 2.
Proof.
have -> : [set i : 'I_5 | e \in ppull f i] = plab (f e).
  by apply/setP => i; rewrite !inE.
exact: plab_card.
Qed.

Lemma petersen_pullback_cover (G : mgraph) (f : edge G -> Pedge) :
  cubic G -> pcol f ->
  exists L : seq {set edge G},
    [/\ size L = 5,
        (forall C, C \in L -> even_subgraph C)
      & (forall e : edge G, count (fun C : {set edge G} => e \in C) L = 2)].
Proof.
move=> Gcubic fcol.
exists (map (ppull f) (index_enum 'I_5)); split.
- by rewrite size_map size_index_enum_ord.
- by move=> D /mapP[i _ ->]; exact: ppull_even.
- move=> e; rewrite count_map -card_count_enum -cardsE.
  exact: ppull_count.
Qed.


(*@EDGE from=petersen_coloring_statement to=m_n_cycle_covers_statement kind=implies status=conditional external="external_five_even_cover_cubic_reduction_statement" proof=petersen_coloring_implies_m_n_cycle_covers cite="gc:e090" note="Pull back the Petersen graph's double cover by five even subgraphs along the Petersen colouring: the three edges at a vertex of a cubic graph go to a claw of the (triangle-free) Petersen graph (petersen_claw), every member meets every claw evenly (plab_claw_even) and every Petersen edge lies in exactly two members (plab_card), so petersen_pullback_cover gives a (5,2)-cover of every cubic bridgeless graph; the finite Petersen facts are proved by closed compute checks on 5-bit codes. The cubic-to-general step is the cited Jaeger 1985 / Zhang reduction, carried as the same external as gc:e085." *)
Theorem petersen_coloring_implies_m_n_cycle_covers :
  external_five_even_cover_cubic_reduction_statement ->
  petersen_coloring_statement -> m_n_cycle_covers_statement.
Proof.
move=> Hred Hp; apply: Hred => G Hn He Hc Hbl.
have [f hf] := Hp G Hn (conj Hc Hbl).
exact: petersen_pullback_cover Hc hf.
Qed.

(*@EDGE from=petersen_coloring_statement to=cycle_double_cover_statement kind=implies status=conditional external="external_five_even_cover_cubic_reduction_statement" proof=petersen_coloring_implies_cycle_double_cover cite="gc:e091" note="Composition of gc:e090 (Petersen colouring => (5,2)-cover, modulo the cited cubic reduction) with the unconditional gc:e084 (split the five even subgraphs into circuits, cycle_space.even_circuit_decomposition)." *)
Theorem petersen_coloring_implies_cycle_double_cover :
  external_five_even_cover_cubic_reduction_statement ->
  petersen_coloring_statement -> cycle_double_cover_statement.
Proof.
move=> Hred Hp; apply: m_n_cycle_covers_implies_cycle_double_cover.
exact: petersen_coloring_implies_m_n_cycle_covers Hred Hp.
Qed.

(** ================================================================= *)
(** ** gc:e098 -- CDC containing a predefined 2-regular subgraph => CDC *)

(** The source row, instantiated at the EMPTY 2-regular edge set [S = set0]
    (degree 0 everywhere, and [G - E(set0) = G] is connected because a
    2-connected multigraph is connected), already yields a cycle double cover of
    every cubic 2-connected multigraph.  No non-separating circuit (Tutte 1963)
    is needed, contrary to the earlier audit: only the classical reduction of
    the CDC to cubic 2-connected graphs remains, carried as the external below. *)

(** External theorem: F. Jaeger, A survey of the cycle double cover
    conjecture, in Cycles in Graphs, Ann. Discrete Math. 27 (1985) 1-12
    (DOI 10.1016/S0304-0208(08)72993-1), Section 2 (a minimal counterexample
    to the cycle double cover conjecture is a cubic 3-connected graph -- indeed
    a snark); see also C.-Q. Zhang, Integer Flows and Cycle Covers of Graphs,
    Marcel Dekker 1997, Chapter 3.
    Claim: if every cubic 2-connected multigraph (loopless, every vertex of
    degree 3, at least three vertices, connected after deleting any one vertex)
    has a cycle double cover, then every bridgeless multigraph with at least one
    vertex and at least one edge has one.  (Weaker than the cited reduction,
    which only needs the 3-connected cubic graphs; loops are handled by covering
    each loop by itself twice.)
    Not formalized here: it is carried as an explicit hypothesis of the
    conditional edge below (never an [Axiom], never [Admitted]), which is why
    that edge is [status=conditional external=...] rather than [verified]. *)
Definition external_cdc_cubic_2connected_reduction_statement : Prop :=
  (forall G : mgraph,
     (0 < #|G|)%N -> cubic G -> two_connected G ->
     exists L : seq {set edge G}, cdc L) ->
  cycle_double_cover_statement.

(** A 2-connected multigraph is connected, i.e. [G - E(set0)] is connected. *)
Lemma two_connected_del_set0 (G : mgraph) :
  two_connected G -> connected_del_edges (@set0 (edge G)).
Proof.
move=> [h3 hdel] x y.
have [z hz] : exists z : G, z \notin [set x; y].
  case: (boolP [exists z, z \notin [set x; y]]) => [/existsP[z hz]|]; first by exists z.
  rewrite negb_exists => /forallP hall.
  have hT : [set x; y] = [set: G].
    by apply/setP => w; rewrite in_setT; exact: negbNE (hall w).
  by move: h3; rewrite -cardsT -hT cards2; case: (x != y).
have hx : x \notin [set z].
  by rewrite inE; apply: contraNneq hz => ->; rewrite !inE eqxx.
have hy : y \notin [set z].
  by rewrite inE; apply: contraNneq hz => ->; rewrite !inE eqxx orbT.
have [w [hw _]] := hdel z x y hx hy.
by exists w; split => //; apply/allP => e _; rewrite inE.
Qed.

(*@EDGE from=cycle_double_covers_containing_predefined_2_regular_statement to=cycle_double_cover_statement kind=implies status=conditional external="external_cdc_cubic_2connected_reduction_statement" proof=cycle_double_covers_containing_predefined_2_regular_implies_cycle_double_cover cite="gc:e098" note="Instantiate the source at S = set0: it is 2-regular (degree 0 everywhere, subdeg0), G - E(set0) = G is connected since a 2-connected multigraph is connected (two_connected_del_set0), and the empty circuit decomposition [::] of set0 is trivially contained in L; so the source yields a CDC of every cubic 2-connected multigraph. The cubic 2-connected-to-general step is the cited Jaeger 1985 / Zhang reduction, carried as the external. The earlier BLOCKED verdict (needing Tutte's non-separating induced circuit and a three_connected predicate) is withdrawn: S = set0 suffices." *)
Theorem cycle_double_covers_containing_predefined_2_regular_implies_cycle_double_cover :
  external_cdc_cubic_2connected_reduction_statement ->
  cycle_double_covers_containing_predefined_2_regular_statement ->
  cycle_double_cover_statement.
Proof.
move=> Hred Hs; apply: Hred => G hn hc h2.
have hk : subgraph_kregular (@set0 (edge G)) 2 by move=> v; left; exact: subdeg0.
have [L [hL _]] := Hs G set0 hn hc h2 hk (two_connected_del_set0 h2).
by exists L.
Qed.


(** ── Axiom audit ─────────────────────────────────────────────────────────── *)

Print Assumptions m_n_cycle_covers_implies_cycle_double_cover.
Print Assumptions strong_5_cycle_double_cover_implies_m_n_cycle_covers.
Print Assumptions strong_5_cycle_double_cover_implies_cycle_double_cover.
Print Assumptions small_cycle_double_cover_implies_cycle_double_cover.
Print Assumptions orientable_five_cycle_double_cover_implies_m_n_cycle_covers.
Print Assumptions orientable_five_cycle_double_cover_implies_cycle_double_cover.
Print Assumptions cycle_double_covers_containing_predefined_2_regular_implies_cycle_double_cover.
Print Assumptions petersen_pullback_cover.
Print Assumptions petersen_coloring_implies_m_n_cycle_covers.
Print Assumptions petersen_coloring_implies_cycle_double_cover.

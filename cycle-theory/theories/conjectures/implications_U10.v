(** * Cycle.conjectures.implications_U10 — milestone U10 dependency-graph EDGES

    Machine-checked implication EDGES between the three committed U10 conjecture
    statements (see [U10.v]).  As in the sibling [implications_U6.v] layer, every
    SCHEDULED edge is a *relative* theorem: a [Qed]-closed
    [Theorem A_statement -> B_statement] provable WITHOUT resolving (proving or
    refuting) either endpoint.  Bridge facts that would otherwise need resolving a
    conjecture or carrying out a heavy out-of-scope finite computation are carried
    as EXPLICIT hypotheses (never [Admitted], never [Axiom]); the file stays
    axiom-free.

    ════════════════════════════════════════════════════════════════════════════
    SCHEDULED EDGE (verified-literature):  Petersen colouring ⟹ Berge–Fulkerson
    ════════════════════════════════════════════════════════════════════════════

      petersen_coloring_statement  ⟹  the_berge_fulkerson_statement

    Endpoints (verbatim from [U10.v]):
      • Petersen colouring (Row 2):
          forall G : mgraph, 0 < #|G| -> cubic_bridgeless G ->
            exists f : edge G -> Pedge,
              forall e1 e2 e3, mut_adj3 (@line_rel G) e1 e2 e3 ->
                               mut_adj3 Padj (f e1) (f e2) (f e3).
      • Berge–Fulkerson (Row 1):
          forall G : mgraph, 0 < #|G| -> cubic_bridgeless G ->
            exists L, perfect_matching_cover 6 L.

    Mathematics (Jaeger 1985).  Let [f] be a Petersen colouring of a bridgeless
    cubic graph [G].  THE Petersen graph itself carries a Berge–Fulkerson cover:
    six perfect matchings [S_1,...,S_6] (sets of Petersen edges) covering every
    Petersen edge exactly twice.  Because the Petersen graph is cubic AND
    triangle-free, any three MUTUALLY ADJACENT Petersen edges are the three edges
    incident to a common vertex (a "claw"), and a perfect matching meets each claw
    in EXACTLY one edge.  Pull each [S_i] back along [f]:
        M_i := { e ∈ E(G) : f(e) ∈ S_i }.
    At every vertex [v] of [G] the three incident edges [e1,e2,e3] are mutually
    line-adjacent, so by the colouring property [f e1, f e2, f e3] are three
    mutually adjacent Petersen edges, i.e. a claw, of which [S_i] contains exactly
    one — hence [v] meets [M_i] in exactly one edge: every [M_i] is a PERFECT
    MATCHING of [G].  And each edge [e] lies in [M_i] iff [f e ∈ S_i], so it is
    covered exactly twice (as [f e] is, in the Petersen cover).  The six [M_i] are
    a Berge–Fulkerson cover of [G].

    The only non-elementary ingredient is the Petersen graph's OWN
    Berge–Fulkerson structure (a fixed finite object); per the plan's
    cited-but-unformalized policy (§3 leg 3) it is carried as the EXPLICIT
    hypothesis [external_petersen_BF_cover_statement] below — a statement purely
    about the Petersen edges [Pedge]/[Padj]/[mut_adj3], never about [G] — rather
    than re-enumerated here.  The genuine pull-back reduction (every claw is hit
    once ⟹ each [M_i] is perfect; covered-twice transfers) is proved in full, so
    the [Qed] gate confirms the edge under the EXACT [U10.v] formulations.

    Citation.  F. Jaeger, "A survey of the cycle double cover conjecture", in
    Cycles in Graphs, Ann. Discrete Math. 27 (1985) 1–12 (Petersen colouring ⟹
    Berge–Fulkerson).  Status: verified-literature.

    ────────────────────────────────────────────────────────────────────────────
    AUDIT of the other U10 node pairs (recorded as candidates, NOT scheduled — no
    verified-literature edge between them appears in the plan's §6 table):
      • Berge–Fulkerson ⟹ Fan–Raspaud (Row 3) and Petersen ⟹ Fan–Raspaud are
        plausible literature implications, but the committed Row-3 statement is the
        "M1 ∩ M2 contains no odd edge-cut" formulation (not the three-matchings
        empty-intersection form), so the exact endpoint match must be re-derived
        before scheduling; left as candidates below.
    ──────────────────────────────────────────────────────────────────────────── *)

From GraphTheory Require Import mgraph sgraph.
From GTBase Require Export base.
From Cycle.foundations Require Import matchings_cuts.
From Cycle.conjectures Require Import U6 U10.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The carried bridge fact: the Petersen graph's own Berge–Fulkerson cover *)

(** External theorem: D. A. Holton and J. Sheehan, The Petersen Graph, Australian
    Mathematical Society Lecture Series 7, Cambridge University Press 1993,
    Chapter 5 (the Petersen graph has exactly six perfect matchings, and every
    edge lies in exactly two of them); see also F. Jaeger, A survey of the cycle
    double cover conjecture, Ann. Discrete Math. 27 (1985) 1-12, where this
    six-matching cover is the Berge-Fulkerson cover of the Petersen graph.
    DOI 10.1017/CBO9780511662058.
    Claim: the six perfect matchings of the Petersen graph form a
    Berge-Fulkerson cover of it -- six sets of Petersen edges such that each of
    them meets every claw (every triple of pairwise adjacent Petersen edges, which
    in the triangle-free Petersen graph is a triple of edges through one vertex)
    in exactly one edge, and every Petersen edge lies in exactly two of the six.
    Not formalized here: it is carried as an explicit hypothesis of the
    conditional edge below (never an [Axiom], never [Admitted]), which is why
    that edge is [status=conditional external=...] rather than [verified]. It
    mentions no host graph. *)
Definition external_petersen_BF_cover_statement : Prop :=
  exists LP : seq {set Pedge},
    [/\ size LP = 6,
        (forall (S : {set Pedge}) (q1 q2 q3 : Pedge),
           S \in LP -> mut_adj3 Padj q1 q2 q3 ->
           ((q1 \in S) + (q2 \in S) + (q3 \in S))%N = 1)
      & (forall q : Pedge, count (fun S : {set Pedge} => q \in S) LP = 2)].

(** ** A finite-set helper: extract three distinct elements from a 3-set *)

Lemma set3 (T : finType) (A : {set T}) :
  #|A| = 3 ->
  exists a b c, [/\ a != b, a != c, b != c & A = [set a; b; c]].
Proof.
move=> H3.
have /card_gt0P [a Ha] : 0 < #|A| by rewrite H3.
move: H3; rewrite (cardsD1 a) Ha /= add1n; case=> H2.
have /card_gt0P [b Hb] : 0 < #|A :\ a| by rewrite H2.
move: H2; rewrite (cardsD1 b) Hb /= add1n; case=> H1.
have /card1P [c Hc] : #|(A :\ a) :\ b| == 1 by rewrite H1.
have hba : b != a by move: Hb; rewrite in_setD1 => /andP[].
have hc1 : c \in (A :\ a) :\ b by rewrite Hc inE.
have hcb : c != b by move: hc1; rewrite in_setD1 => /andP[].
have hca : c != a by move: hc1; rewrite !in_setD1 => /and3P[].
have Hcset : (A :\ a) :\ b = [set c].
  by apply/setP => x; rewrite Hc !inE.
exists a, b, c; split.
- by rewrite eq_sym.
- by rewrite eq_sym.
- by rewrite eq_sym.
- rewrite -(setD1K Ha) -(setD1K Hb) Hcset.
  by rewrite setUA.
Qed.

(** ** The scheduled edge *)

(*@EDGE from=petersen_coloring_statement to=the_berge_fulkerson_statement kind=implies status=conditional external="external_petersen_BF_cover_statement" proof=petersen_coloring_implies_berge_fulkerson cite="F. Jaeger, A survey of the cycle double cover conjecture, in Cycles in Graphs, Ann. Discrete Math. 27 (1985) 1-12" note="Jaeger: a Petersen colouring pulls back the Petersen graph's own six perfect matchings (carried as the explicit Petersen-side hypothesis external_petersen_BF_cover_statement) to a Berge-Fulkerson cover of G; at each cubic vertex the three incident edges form a line-adjacent triple, mapped to a Petersen claw met once by each matching, so every pullback is a perfect matching, and covered-twice transfers along f" *)
Theorem petersen_coloring_implies_berge_fulkerson :
  external_petersen_BF_cover_statement ->
  petersen_coloring_statement ->
  the_berge_fulkerson_statement.
Proof.
move=> [LP [Hsize Hone Htwice]] Hpc G Hn Hcb.
have [f Hf] := Hpc G Hn Hcb.
have [Hcubic _] := Hcb.
have [Hll Hreg] := Hcubic.
exists (map (fun S : {set Pedge} => [set e : edge G | f e \in S]) LP).
split.
- by rewrite size_map.
- (* every pullback member is a perfect matching of G *)
  move=> M /mapP[S HS ->] v.
  have Hd3 : #|edges_at v| = 3 by rewrite -(mdeg_loopless v Hll); exact: (Hreg v).
  have [e1 [e2 [e3 [n12 n13 n23 Heq]]]] := set3 Hd3.
  have inc : forall e : edge G, e \in edges_at v -> incident v e.
    by move=> e; rewrite inE.
  have m1 : e1 \in edges_at v by rewrite Heq !inE eqxx.
  have m2 : e2 \in edges_at v by rewrite Heq !inE eqxx orbT.
  have m3 : e3 \in edges_at v by rewrite Heq !inE eqxx orbT.
  have line : forall ei ej : edge G,
      ei \in edges_at v -> ej \in edges_at v -> ei != ej -> @line_rel G ei ej.
    move=> ei ej Hi Hj Hne; rewrite /line_rel Hne /=.
    by apply/existsP; exists v; apply/andP; split; [exact: inc Hi | exact: inc Hj].
  have ml : mut_adj3 (@line_rel G) e1 e2 e3.
    rewrite /mut_adj3; apply/and3P; split.
    + by apply: (line _ _ m1 m2 n12).
    + by apply: (line _ _ m2 m3 n23).
    + by apply: (line _ _ m1 m3 n13).
  have mp := Hf e1 e2 e3 ml.
  have Hsum := Hone S (f e1) (f e2) (f e3) HS mp.
  rewrite (subdeg_loopless _ _ Hll) -preliminaries.sum_cardI.
  rewrite (eq_bigr (fun e => (f e \in S : nat))); last by move=> e _; rewrite inE.
  rewrite Heq.
  have h1 : e1 \notin [set e2; e3] by rewrite !inE negb_or n12 n13.
  have h2 : e2 \notin [set e3] by rewrite in_set1 (negbTE n23).
  rewrite -setUA big_setU1 // big_setU1 // big_set1.
  by move: Hsum; rewrite -addnA.
- (* every edge of G is covered exactly twice *)
  move=> e.
  rewrite count_map.
  rewrite (eq_count (a2 := fun S : {set Pedge} => f e \in S)); last first.
    by move=> S /=; rewrite inE.
  exact: Htwice (f e).
Qed.

(** ================================================================= *)
(** ** Berge-Fulkerson =>  intersecting two perfect matchings (Row 1 => Row 3)

    A Berge-Fulkerson cover [L] has SIX members, so after picking the first two
    as [M1] and [M2] a THIRD perfect matching [M3] is still available.  Suppose
    [M1 :&: M2] contained an odd edge cut [T = cut S].  Every edge of [T] lies in
    both [M1] and [M2], i.e. at two positions of [L] already, and the cover
    condition caps the total at two, so [M3] misses [T] entirely.  But F27
    ([matchings_cuts.pm_meets_odd_cut]: the [M3]-degree sum over [S] is [#|S|],
    the handshake identity makes [#|M3 :&: cut S|] and [#|S|] equal mod 2, and
    3-regularity makes [#|cut S|] and [#|S|] equal mod 2) forces [M3] to MEET
    every odd cut.  Contradiction, so no odd cut sits inside [M1 :&: M2]. *)

(*@EDGE from=the_berge_fulkerson_statement to=intersecting_two_perfect_matchings_statement kind=implies status=verified proof=the_berge_fulkerson_implies_intersecting_two_perfect_matchings cite="gc:e092" note="Berge-Fulkerson cover of six perfect matchings: take M1, M2 the first two members; an odd cut inside M1 cap M2 would already use up both of its two allowed covering positions, so the third member M3 would miss it, contradicting F27 (matchings_cuts.pm_meets_odd_cut: a perfect matching of a 3-regular multigraph meets every odd edge cut, by the handshake identity relative to S)" *)
Theorem the_berge_fulkerson_implies_intersecting_two_perfect_matchings :
  the_berge_fulkerson_statement -> intersecting_two_perfect_matchings_statement.
Proof.
move=> HBF G Hn Hcb.
have [[Hll Hreg] Hbl] := Hcb.
have [L [Hsize Hpm Htwice]] := HBF G Hn Hcb.
have gen : forall (T : Type) (s : seq T), size s = 6 ->
    exists a b c s', s = [:: a, b, c & s'].
  move=> T [|a [|b [|c s']]] //= _.
  by exists a, b, c, s'.
have [M1 [M2 [M3 [L' HL]]]] := gen _ L Hsize.
have pm1 : is_perfect_matching M1 by apply: Hpm; rewrite HL !inE eqxx.
have pm2 : is_perfect_matching M2 by apply: Hpm; rewrite HL !inE eqxx orbT.
have pm3 : is_perfect_matching M3 by apply: Hpm; rewrite HL !inE eqxx !orbT.
exists M1, M2; split; [exact: pm1 | exact: pm2 |].
move=> [T [Tsub [S [Tcut _ Todd]]]].
have oc : odd #|cut S| by rewrite -Tcut.
have /set0Pn [e] := @pm_meets_odd_cut G M3 S Hreg pm3 oc.
rewrite inE => /andP[e3 ec].
have eT : e \in T by rewrite Tcut.
have e12 := subsetP Tsub _ eT.
rewrite inE in e12; have [e1 e2] := andP e12.
by move: (Htwice e); rewrite HL /= e1 e2 e3.
Qed.

(** ── Audited candidate (non-scheduled) edges (machine-readable) ── *)
(*@EDGE from=petersen_coloring_statement to=intersecting_two_perfect_matchings_statement kind=implies status=candidate proved=false cite="snark-colouring literature" note="Petersen colouring is expected to imply the Fan-Raspaud-type Row 3, but only via the Berge-Fulkerson route whose endpoint match to the committed odd-edge-cut formulation is unverified" *)

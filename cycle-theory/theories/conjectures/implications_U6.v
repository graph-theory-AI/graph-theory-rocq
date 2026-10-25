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
Set SsrOldRewriteGoalsOrder.

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
move=> He [Hll Hreg].
have Cdeg : forall v : G, subdeg [set: edge G] v != 1.
  move=> v; have e3 : subdeg [set: edge G] v = 3 by rewrite (subdeg_loopless _ _ Hll) setIT; exact: Hreg v.
  by rewrite e3.
have Tn0 : [set: edge G] != set0 by rewrite -card_gt0 cardsT.
by have [D [_ Dcirc]] := has_circuit Tn0 Cdeg; exists D.
Qed.

(** The reduction, with the cubic reduction as an explicit hypothesis.  (Until
    2026-10-25 this was the edge gc:e085, [status=conditional]; its annotation
    now sits on [unconditional_strong_5_cycle_double_cover_implies_m_n_cycle_covers]
    below, after [five_even_cover_cubic_reduction].) *)
Theorem strong_5_cycle_double_cover_implies_m_n_cycle_covers :
  external_five_even_cover_cubic_reduction_statement ->
  strong_5_cycle_double_cover_statement -> m_n_cycle_covers_statement.
Proof.
move=> Hred Hs; apply: Hred => G Hn He Hc Hbl.
have [D Dcirc] := cubic_has_circuit He Hc.
have [L [Lsize Leven Lcount _]] := Hs G D Hn Hc Hbl Dcirc.
by exists L; split.
Qed.

(** (Until 2026-10-25 the edge gc:e086, [status=conditional]; its annotation now
    sits on [unconditional_strong_5_cycle_double_cover_implies_cycle_double_cover]
    below.) *)
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
    Proved below as [cdc_simple_reduction] (2026-10-25, classical-lemmas
    TODO 3), by subdividing every edge twice; the reduction that takes it as a
    hypothesis is kept. *)
Definition external_cdc_simple_reduction_statement : Prop :=
  (forall G : mgraph,
     (0 < #|G|)%N -> simple_mgraph G -> bridgeless G ->
     exists L : seq {set edge G}, cdc L) ->
  (forall G : mgraph,
     (0 < #|G|)%N -> (0 < #|edge G|)%N -> bridgeless G ->
     exists L : seq {set edge G}, cdc L).

(** The reduction, with the simple-graph reduction as an explicit hypothesis.
    (Until 2026-10-25 this was the edge gc:e209, [status=conditional]; its
    annotation now sits on
    [unconditional_small_cycle_double_cover_implies_cycle_double_cover] below,
    after [cdc_simple_reduction].) *)
Theorem small_cycle_double_cover_implies_cycle_double_cover :
  external_cdc_simple_reduction_statement ->
  small_cycle_double_cover_statement -> cycle_double_cover_statement.
Proof.
move=> Hred Hs; apply: Hred => G Hn Hsimp Hbl.
by have [L [HL _]] := Hs G Hn Hsimp Hbl; exists L.
Qed.

(** ================================================================= *)
(** ** gc:e209: the reduction of the CDC to simple graphs
       (classical-lemmas TODO 3)

    Subdivide every edge twice: [sdG G] has the vertices of [G] plus two new
    vertices [inr (e, false)], [inr (e, true)] per edge [e], and each edge [e]
    becomes the path [source e -- (e, false) -- (e, true) -- target e] of the
    edges [(e, Some false)], [(e, None)], [(e, Some true)].  A loop becomes a
    triangle and parallel edges become internally disjoint paths, so [sdG G]
    is simple.  An undirected walk of [G] lifts to [sdG G] ([sd_lift]), so a
    bridge of [sdG G] would give a bridge of [G].  A circuit of [sdG G] passes
    through a new vertex with both or neither of its two edges, so it contains
    all three edges of [e] or none; its middle edges [sd_back C] form a circuit
    of [G] (degrees are preserved at the old vertices, and a walk projects
    through [sd_pi], keeping only its middle edges).  Hence a cycle double
    cover of [sdG G] maps to one of [G]. *)

Section Subdivide.
Variable G : mgraph.

Definition sd_end (b : bool) (f : edge G * option bool) : G + (edge G * bool) :=
  match f.2 with
  | None => inr (f.1, b)
  | Some c => if b == c then inl (endpoint c f.1) else inr (f.1, c)
  end.

Definition sdG : mgraph :=
  @Graph unit unit (G + (edge G * bool))%type (edge G * option bool)%type
    sd_end (fun _ => tt) (fun _ => tt).

(** The old vertex below a vertex of [sdG]. *)
Definition sd_pi (x : sdG) : G :=
  match x with inl v => v | inr (e, c) => endpoint c e end.

(** The middle edges of an edge set of [sdG]. *)
Definition sd_back (C : {set edge sdG}) : {set edge G} :=
  [set e | ((e, None) : edge sdG) \in C].

(** The three edges of [e], traversed from the [b]-end of [e]. *)
Definition sd_path (b : bool) (e : edge G) : seq (edge sdG) :=
  if b then [:: (e, Some true); (e, None); (e, Some false)]
  else [:: (e, Some false); (e, None); (e, Some true)].

Fixpoint sd_lift (x : G) (w : seq (edge G)) : seq (edge sdG) :=
  match w with
  | [::] => [::]
  | e :: w' =>
      if source e == x then sd_path false e ++ sd_lift (target e) w'
      else sd_path true e ++ sd_lift (source e) w'
  end.

Definition sd_proj (w : seq (edge sdG)) : seq (edge G) :=
  [seq f.1 | f <- w & f.2 == None].

Lemma sd_loopless : loopless sdG.
Proof.
by move=> [e [[]|]]; rewrite /source /target /= /sd_end //=; apply/eqP => -[].
Qed.

Lemma sd_simple : simple_mgraph sdG.
Proof.
(* An edge of [sdG] is determined by its two ends, and no edge runs between
   the ends of another one in the opposite direction. *)
have key : forall f1 f2 : edge sdG,
    source f1 = source f2 -> target f1 = target f2 -> f1 = f2.
  by move=> [e1 [[]|]] [e2 [[]|]]; rewrite /source /target /= /sd_end /=
    => h1 h2; congruence.
have keyr : forall f1 f2 : edge sdG,
    source f1 = target f2 -> target f1 = source f2 -> False.
  by move=> [e1 [[]|]] [e2 [[]|]]; rewrite /source /target /= /sd_end /=
    => h1 h2; congruence.
split; first exact: sd_loopless.
move=> x y.
have hI : edges x y :&: edges y x = set0.
  apply/setP => f; rewrite !inE; apply/negP.
  move=> /andP[/andP[/eqP sx /eqP ty] /andP[/eqP sy /eqP tx]].
  by move: (sd_loopless f); rewrite sx tx eqxx.
rewrite -cardsUI hI cards0 addn0.
apply/card_le1_eqP => f1 f2; rewrite !inE.
move=> /orP[/andP[/eqP s1 /eqP t1]|/andP[/eqP s1 /eqP t1]]
       /orP[/andP[/eqP s2 /eqP t2]|/andP[/eqP s2 /eqP t2]].
- by apply: key; rewrite ?s1 ?s2 ?t1 ?t2.
- by case: (keyr f2 f1); rewrite ?s1 ?s2 ?t1 ?t2.
- by case: (keyr f2 f1); rewrite ?s1 ?s2 ?t1 ?t2.
- by apply: key; rewrite ?s1 ?s2 ?t1 ?t2.
Qed.

Lemma sd_lift_uwalk (x y : G) (w : seq (edge G)) :
  uwalk x y w -> uwalk (inl x : sdG) (inl y) (sd_lift x w).
Proof.
elim: w x => [x /eqP -> /=|e w IH x h /=]; first by rewrite eqxx.
case: ifP => [/eqP hs|hs].
  do 3 (apply: uwalk_cons; first by rewrite /source /= /sd_end /= ?hs).
  apply: IH; case/orP: h => /andP[/eqP h1 h2] //.
  by rewrite h1 -hs.
case/orP: h => /andP[/eqP h1 h2]; first by rewrite h1 eqxx in hs.
do 3 (apply: uwalk_cons_rev; first by rewrite /target /= /sd_end /= ?h1).
exact: IH.
Qed.

Lemma sd_lift_mem (x : G) (w : seq (edge G)) (f : edge sdG) :
  f \in sd_lift x w -> f.1 \in w.
Proof.
elim: w x => [//|e w IH x]; rewrite in_cons.
have hp : forall b, f \in sd_path b e -> f.1 = e.
  by move=> []; rewrite /sd_path !inE => /or3P[] /eqP ->.
move=> h; have {h} : f \in sd_path (source e != x) e
    ++ sd_lift (if source e == x then target e else source e) w.
  by move: h => /=; case: ifP.
by rewrite mem_cat => /orP[/hp ->|/IH ->]; rewrite ?eqxx ?orbT.
Qed.

Lemma sd_bridgeless : bridgeless G -> bridgeless sdG.
Proof.
(* A bridge [(e, k)] of [sdG] makes [e] a bridge of [G]: a walk of [G] from
   [source e] to [target e] avoiding [e] lifts, with the other two edges of
   [e], to a walk between the ends of [(e, k)] avoiding it. *)
move=> hbl [e k] hbr; apply: (hbl e) => w hw.
case: (boolP (e \in w)) => [ew|new]; first by exists e; rewrite ?inE.
exfalso.
have hl := sd_lift_uwalk hw.
have hnot : forall j, ((e, j) : edge sdG) \notin sd_lift (source e) w.
  by move=> j; apply/negP => /sd_lift_mem /=; apply/negP.
case: k hbr => [[]|] hbr.
- have hw' : uwalk (source ((e, Some true) : edge sdG))
      (target ((e, Some true) : edge sdG))
      ([:: (e, None); (e, Some false)] ++ sd_lift (source e) w).
    do 2 (apply: uwalk_cons_rev; first by []).
    exact: hl.
  have [g /set1P -> hg] := hbr _ hw'.
  move: hg; rewrite mem_cat (negbTE (hnot _)) !inE.
  by rewrite !xpair_eqE eqxx.
- have hw' : uwalk (source ((e, Some false) : edge sdG))
      (target ((e, Some false) : edge sdG))
      (sd_lift (source e) w ++ [:: (e, Some true); (e, None)]).
    apply: uwalk_cat hl _.
    do 2 (apply: uwalk_cons_rev; first by []).
    by rewrite /= eqxx.
  have [g /set1P -> hg] := hbr _ hw'.
  move: hg; rewrite mem_cat (negbTE (hnot _)) !inE.
  by rewrite !xpair_eqE eqxx.
- have hw' : uwalk (source ((e, None) : edge sdG))
      (target ((e, None) : edge sdG))
      ((e, Some false) :: sd_lift (source e) w ++ [:: (e, Some true)]).
    apply: uwalk_cons_rev; first by [].
    apply: uwalk_cat hl _.
    apply: uwalk_cons_rev; first by [].
    by rewrite /= eqxx.
  have [g /set1P -> hg] := hbr _ hw'.
  move: hg; rewrite in_cons mem_cat (negbTE (hnot _)) !inE.
  by rewrite !xpair_eqE eqxx.
Qed.

Lemma sd_proj_uwalk (x y : sdG) (w : seq (edge sdG)) :
  uwalk x y w -> uwalk (sd_pi x) (sd_pi y) (sd_proj w).
Proof.
(* An outer edge [(e, Some c)] has both ends above [endpoint c e]; a middle
   edge [(e, None)] lies above [e]. *)
elim: w x => [x /eqP -> /=|[e [c|]] w IH x h]; first by rewrite eqxx.
  have hpi : sd_pi (source ((e, Some c) : edge sdG))
           = sd_pi (target ((e, Some c) : edge sdG)) by clear h; case: c.
  rewrite /sd_proj /=; case/orP: h => /andP[/eqP hx hw].
  - by rewrite -hx hpi; exact: IH hw.
  - by rewrite -hx -hpi; exact: IH hw.
rewrite /sd_proj /=; case/orP: h => /andP[/eqP hx hw].
- by apply: uwalk_cons; [rewrite -hx | exact: IH hw].
- by apply: uwalk_cons_rev; [rewrite -hx | exact: IH hw].
Qed.

(** In a [{0,2}]-regular edge set of [sdG], the three edges of [e] are all in
    or all out. *)
Lemma sd_reg (C : {set edge sdG}) (e : edge G) :
  subgraph_kregular C 2 ->
  ((e, Some false) \in C) = ((e, None) \in C) /\
  ((e, Some true) \in C) = ((e, None) \in C).
Proof.
(* The new vertex [inr (e, c)] has exactly two arc ends, so its degree in [C]
   counts two of the three edges of [e]. *)
move=> hreg.
have card1 : forall (P : pred (edge sdG)) f0,
    (forall f, P f = (f == f0)) -> #|[set f in C | P f]| = (f0 \in C).
  move=> P f0 hP; case: (boolP (f0 \in C)) => h0.
    rewrite (_ : [set f in C | P f] = [set f0]) ?cards1 //.
    apply/setP => f; rewrite !inE hP.
    by case: (f =P f0) => [->|]; rewrite ?h0 ?andbF.
  rewrite (_ : [set f in C | P f] = set0) ?cards0 //.
  apply/setP => f; rewrite !inE hP.
  by case: (f =P f0) => [->|]; rewrite ?(negbTE h0) ?andbF.
have es : forall c (f : edge sdG), (endpoint false f == (inr (e, c) : sdG))
    = (f == (e, if c then Some true else None)).
  move=> [] [g [[]|]]; rewrite /= /sd_end /= ?xpair_eqE /= ?andbT ?andbF;
    by [apply/eqP/eqP => [[->]|->] | apply/eqP => -[]].
have et : forall c (f : edge sdG), (endpoint true f == (inr (e, c) : sdG))
    = (f == (e, if c then None else Some false)).
  move=> [] [g [[]|]]; rewrite /= /sd_end /= ?xpair_eqE /= ?andbT ?andbF;
    by [apply/eqP/eqP => [[->]|->] | apply/eqP => -[]].
have hd : forall c, subdeg C (inr (e, c))
    = ((e, if c then Some true else None) \in C)
      + ((e, if c then None else Some false) \in C).
  by move=> c; rewrite /subdeg /ends_at (card1 _ _ (es c)) (card1 _ _ (et c)).
have h2 : forall a b : bool, (a + b = 0 \/ a + b = 2)%N -> a = b.
  by move=> [] [] //= [].
split.
- by apply/esym/h2; rewrite -(hd false); exact: hreg.
- by apply/h2; rewrite -(hd true); exact: hreg.
Qed.

Lemma sd_subdeg (C : {set edge sdG}) (v : G) :
  subgraph_kregular C 2 -> subdeg (sd_back C) v = subdeg C (inl v).
Proof.
(* The [b]-ends of [C] at [inl v] are the outer edges [(g, Some b)] of the
   edges [g] of [sd_back C] whose [b]-end is [v]. *)
move=> hreg.
have hr : forall g c, (((g, Some c) : edge sdG) \in C) = ((g, None) \in C).
  by move=> g []; case: (sd_reg g hreg).
have hb : forall b, ends_at C b (inl v)
    = [set ((g, Some b) : edge sdG) | g in ends_at (sd_back C) b v].
  move=> b; apply/setP => f; apply/idP/idP.
    case: f => g [c|]; rewrite inE /= /sd_end /=.
    - case: (b =P c) => [<-|_] /andP[hC] /eqP // [hv].
      by apply/imsetP; exists g => //; rewrite !inE -(hr g b) hC hv eqxx.
    - by case/andP => _ /eqP.
  case/imsetP => g; rewrite !inE => /andP[hC /eqP hv] ->.
  by rewrite hr hC /= /sd_end /= eqxx hv.
have inj : forall b, injective (fun g : edge G => ((g, Some b) : edge sdG)).
  by move=> b g1 g2 [].
by rewrite /subdeg !hb !card_imset.
Qed.

Lemma sd_circuit (C : {set edge sdG}) : is_circuit C -> is_circuit (sd_back C).
Proof.
case=> hne hreg hconn.
have hr : forall g c, (((g, Some c) : edge sdG) \in C) = ((g, None) \in C).
  by move=> g []; case: (sd_reg g hreg).
split.
- case/set0Pn: hne => -[g k] hf; apply/set0Pn; exists g; rewrite inE.
  by case: k hf => [c|] hf //; rewrite -(hr g c).
- by move=> v; rewrite sd_subdeg //; exact: hreg.
have lift_inc : forall z, H_inc (sd_back C) z -> H_inc C (inl z).
  move=> z /existsP[e /andP[he /existsP[b /eqP hb]]].
  apply/existsP; exists (e, Some b); rewrite hr; move: he; rewrite inE => -> /=.
  by apply/existsP; exists b; rewrite /= /sd_end /= eqxx hb.
move=> x y hx hy.
have [w /andP[hu ha]] := hconn _ _ (lift_inc _ hx) (lift_inc _ hy).
exists (sd_proj w); apply/andP; split; first exact: (sd_proj_uwalk hu).
apply/allP => e /mapP[[g k]]; rewrite mem_filter /= => /andP[/eqP hk hf] ->.
by rewrite inE -hk (allP ha _ hf).
Qed.

Lemma sd_cdc (L : seq {set edge sdG}) : cdc L -> cdc (map sd_back L).
Proof.
case=> hc hcnt; split.
  by move=> C' /mapP[C hC ->]; exact: sd_circuit (hc C hC).
move=> e; rewrite count_map -(hcnt (e, None)).
by apply: eq_count => C /=; rewrite inE.
Qed.

End Subdivide.

(** The reduction of the CDC to simple graphs (Jaeger 1985, Section 2), at
    the form stated by the external. *)
Theorem cdc_simple_reduction : external_cdc_simple_reduction_statement.
Proof.
move=> Hs G Hn _ Hbl.
have Hn' : (0 < #|sdG G|)%N.
  by case/card_gt0P: Hn => v _; apply/card_gt0P; exists (inl v).
have [L hL] := Hs (sdG G) Hn' (sd_simple G) (sd_bridgeless Hbl).
by exists (map (@sd_back G) L); exact: sd_cdc.
Qed.

(*@EDGE from=small_cycle_double_cover_statement to=cycle_double_cover_statement kind=implies status=verified proof=unconditional_small_cycle_double_cover_implies_cycle_double_cover cite="gc:e209" note="bm-013 gives, for every SIMPLE bridgeless multigraph, a cycle double cover with at most #|G|-1 members; forgetting the size bound gives the simple case of Row 11, and the simple-to-general step is proved as cdc_simple_reduction: subdividing every edge twice gives a simple bridgeless multigraph, and the middle edges of its cycle double cover form one of the original graph" *)
Theorem unconditional_small_cycle_double_cover_implies_cycle_double_cover :
  small_cycle_double_cover_statement -> cycle_double_cover_statement.
Proof.
exact: small_cycle_double_cover_implies_cycle_double_cover cdc_simple_reduction.
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
rewrite /padj /GTBase.petersen.kneser52_adj => hab hbc hac.
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
  exact: (hdeg v).
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


(** (Until 2026-10-25 the edge gc:e090, [status=conditional]; its annotation now
    sits on [unconditional_petersen_coloring_implies_m_n_cycle_covers] below,
    after [five_even_cover_cubic_reduction].) *)
Theorem petersen_coloring_implies_m_n_cycle_covers :
  external_five_even_cover_cubic_reduction_statement ->
  petersen_coloring_statement -> m_n_cycle_covers_statement.
Proof.
move=> Hred Hp; apply: Hred => G Hn He Hc Hbl.
have [f hf] := Hp G Hn (conj Hc Hbl).
exact: petersen_pullback_cover Hc hf.
Qed.

(** (Until 2026-10-25 the edge gc:e091, [status=conditional]; its annotation now
    sits on [unconditional_petersen_coloring_implies_cycle_double_cover] below.) *)
Theorem petersen_coloring_implies_cycle_double_cover :
  external_five_even_cover_cubic_reduction_statement ->
  petersen_coloring_statement -> cycle_double_cover_statement.
Proof.
move=> Hred Hp; apply: m_n_cycle_covers_implies_cycle_double_cover.
exact: petersen_coloring_implies_m_n_cycle_covers Hred Hp.
Qed.

(** ================================================================= *)
(** ** gc:e085 / e086 / e090 / e091: the cubic reduction of five-even-subgraph
       double covers (classical-lemmas TODO 2)

    Jaeger's and Zhang's reduction for "cycle" (= even subgraph) double covers
    needs no vertex splitting: inflate every vertex into a cycle.  [infG G] has
    the arc ends [(e, b)] of [G] as vertices; the copy [inl e] joins the two
    ends of [e], and the cycle edge [inr a] joins [a] to the next end at the
    same vertex ([inf_nxt], MathComp's [next] on the list [inf_ends]).
    - [infG G] is 3-regular ([inf_subdeg]), and loopless when no vertex of [G]
      has degree one ([inf_loopless]), which bridgelessness gives
      ([inf_mdeg1]); so it is cubic ([inf_cubic]).
    - It is bridgeless ([inf_bridgeless]): a cycle edge lies on its vertex's
      cycle ([inf_cycle_not_bridge]), and a walk of [G] avoiding [e] lifts to
      one avoiding [inl e] ([inf_lift]).
    - Contracting the cycles ([inf_contract]) keeps even subgraphs even: the
      degree of the contraction at [v] is the sum of the degrees at the ends of
      [v] minus twice the cycle edges of [v] ([inf_contract_even]), so a double
      cover of [infG G] by five even subgraphs maps to one of [G]
      ([inf_cover]). *)

(** Members of [C] picked out by one or two named elements. *)
Lemma inf_card1 (T : finType) (C : {set T}) (P : pred T) (x : T) :
  (forall f, P f = (f == x)) -> #|[set f in C | P f]| = (x \in C).
Proof.
move=> hP; case: (boolP (x \in C)) => hx.
  rewrite (_ : [set f in C | P f] = [set x]) ?cards1 //.
  by apply/setP => f; rewrite !inE hP; case: (f =P x) => [->|]; rewrite ?hx ?andbF.
rewrite (_ : [set f in C | P f] = set0) ?cards0 //.
by apply/setP => f; rewrite !inE hP; case: (f =P x) => [->|]; rewrite ?(negbTE hx) ?andbF.
Qed.

Lemma inf_card2 (T : finType) (C : {set T}) (P : pred T) (x y : T) :
  x != y -> (forall f, P f = (f == x) || (f == y)) ->
  #|[set f in C | P f]| = (x \in C) + (y \in C).
Proof.
move=> hxy hP.
rewrite (_ : [set f in C | P f] = [set f in C | f == x] :|: [set f in C | f == y]).
  rewrite cardsU (inf_card1 _ (fun f => erefl)) (inf_card1 _ (fun f => erefl)).
  rewrite (_ : _ :&: _ = set0) ?cards0 ?subn0 //.
  apply/setP => f; rewrite !inE; apply/negP => /andP[/andP[_ /eqP ->] /andP[_ hy]].
  by move: hxy; rewrite hy.
by apply/setP => f; rewrite !inE hP andb_orr.
Qed.

(** [next] on a duplicate-free cycle advances the index by one, cyclically. *)
Lemma inf_index_next (T : eqType) (s : seq T) (x : T) :
  uniq s -> x \in s -> index (next s x) s = (index x s).+1 %% size s.
Proof.
move=> us xs; rewrite next_nth xs.
case: s us xs => [//|y s'] us xs.
have hi : (index x (y :: s') < (size s').+1)%N.
  by rewrite -[(size s').+1]/(size (y :: s')) index_mem.
set i := index x (y :: s') in hi *.
case: (ltnP i (size s')) => hlt.
  rewrite (_ : nth y s' i = nth y (y :: s') i.+1) // index_uniq //= ?modn_small //;
    by rewrite ltnS.
have -> : i = size s' by apply/eqP; rewrite eqn_leq hlt -ltnS hi.
by rewrite nth_default //= eqxx modnn.
Qed.

Lemma inf_index_iter (T : eqType) (s : seq T) (x : T) (n : nat) :
  uniq s -> x \in s ->
  iter n (next s) x \in s /\ index (iter n (next s) x) s = (index x s + n) %% size s.
Proof.
move=> us xs; elim: n => [|n [hin hidx]] /=.
  by rewrite addn0 modn_small // index_mem.
split; first by rewrite mem_next.
by rewrite inf_index_next // hidx addnS -addn1 modnDml addn1.
Qed.

Section Inflate.
Variable G : mgraph.

(** The arc ends of [G] at the vertex [v], in a fixed order. *)
Definition inf_end (a : edge G * bool) : G := endpoint a.2 a.1.
Definition inf_ends (v : G) : seq (edge G * bool) :=
  enum [set a : edge G * bool | inf_end a == v].
Definition inf_nxt (a : edge G * bool) : edge G * bool := next (inf_ends (inf_end a)) a.
Definition inf_prv (a : edge G * bool) : edge G * bool := path.prev (inf_ends (inf_end a)) a.

(** The inflation: the copy [inl e] of [e] joins its two ends; the cycle edge
    [inr a] joins [a] to the next end at the same vertex. *)
Definition inf_endpoint (b : bool) (f : edge G + (edge G * bool)) : edge G * bool :=
  match f with
  | inl e => (e, b)
  | inr a => if b then inf_nxt a else a
  end.

Definition infG : mgraph :=
  @Graph unit unit (edge G * bool)%type (edge G + (edge G * bool))%type
    inf_endpoint (fun _ => tt) (fun _ => tt).

Lemma inf_ends_uniq (v : G) : uniq (inf_ends v).
Proof. exact: enum_uniq. Qed.

Lemma mem_inf_ends (v : G) (a : edge G * bool) : (a \in inf_ends v) = (inf_end a == v).
Proof. by rewrite mem_enum inE. Qed.

Lemma inf_end_nxt (a : edge G * bool) : inf_end (inf_nxt a) = inf_end a.
Proof.
by apply/eqP; rewrite -mem_inf_ends /inf_nxt mem_next mem_inf_ends.
Qed.

Lemma inf_end_prv (a : edge G * bool) : inf_end (inf_prv a) = inf_end a.
Proof.
by apply/eqP; rewrite -mem_inf_ends /inf_prv path.mem_prev mem_inf_ends.
Qed.

Lemma inf_prv_nxt (a : edge G * bool) : inf_prv (inf_nxt a) = a.
Proof. by rewrite /inf_prv inf_end_nxt path.prev_next // inf_ends_uniq. Qed.

Lemma inf_nxt_prv (a : edge G * bool) : inf_nxt (inf_prv a) = a.
Proof. by rewrite /inf_nxt inf_end_prv path.next_prev // inf_ends_uniq. Qed.

(** Every end has three arc ends in [infG]: its copy, its own cycle edge and
    the cycle edge of the previous end. *)
Lemma inf_subdeg (C : {set edge infG}) (a : infG) :
  subdeg C a = (((inl a.1 : edge infG) \in C) + ((inr a : edge infG) \in C)
               + ((inr (inf_prv a) : edge infG) \in C))%N.
Proof.
case: a => e b.
have hsrc : forall f : edge infG, (endpoint false f == ((e, b) : infG))
    = if b then f == inr (e, b) else (f == inl e) || (f == inr (e, b)).
  case: b => -[g|c]; rewrite /= ?xpair_eqE /= ?andbT ?andbF ?orbF;
    by [| apply/eqP/eqP => [->|[]] | apply/eqP/eqP => [[->]|[]->]
        | apply/eqP/eqP; congruence].
have hnp : forall c : edge G * bool, (inf_nxt c == (e, b)) = (c == inf_prv (e, b)).
  by move=> c; apply/eqP/eqP => [<-|->]; [rewrite inf_prv_nxt | rewrite inf_nxt_prv].
have htgt : forall f : edge infG, (endpoint true f == ((e, b) : infG))
    = if b then (f == inl e) || (f == inr (inf_prv (e, b)))
      else f == inr (inf_prv (e, b)).
  move=> -[g|c].
    case: b {hsrc hnp}; rewrite /= ?xpair_eqE /= ?andbT ?andbF ?orbF;
      by [| apply/eqP/eqP => [->|[]] | apply/eqP/eqP => [[->]|[]->]
          | apply/eqP/eqP; congruence].
  by rewrite /= hnp; case: b {hsrc hnp} => /=; apply/eqP/eqP => [->|[]->].
rewrite /subdeg /ends_at.
case: b hsrc htgt hnp => /= hsrc htgt _.
  by rewrite (inf_card1 _ hsrc) (inf_card2 _ _ htgt) // addnCA addnA.
by rewrite (inf_card2 _ _ hsrc) // (inf_card1 _ htgt).
Qed.

(** The ends at [v] count its degree (a loop twice). *)
Lemma inf_card_ends_in (X : {set edge G}) (v : G) :
  #|[set a : edge G * bool | (inf_end a == v) && (a.1 \in X)]| = subdeg X v.
Proof.
set A := [set a : edge G * bool | (inf_end a == v) && (a.1 \in X)].
have hb : forall b : bool, A :&: [set a | a.2 == b] = [set (e, b) | e in ends_at X b v].
  move=> b; apply/setP => -[e c]; rewrite !inE.
  apply/idP/idP => [/andP[/andP[he hX] /eqP hc]|/imsetP[f]].
    by apply/imsetP; exists e; [rewrite !inE hX -hc | rewrite -hc].
  by rewrite !inE => /andP[hf hv] [-> ->]; rewrite hf hv eqxx.
rewrite -(cardsID [set a | a.2 == true] A) hb.
rewrite (_ : A :\: [set a | a.2 == true] = A :&: [set a | a.2 == false]); last first.
  by apply/setP => -[e c]; rewrite !inE; case: c; rewrite ?andbT ?andbF.
rewrite hb !card_imset; try by move=> x y [->].
by rewrite /subdeg addnC.
Qed.

Lemma inf_card_ends (v : G) : #|[set a : edge G * bool | inf_end a == v]| = mdeg v.
Proof.
by rewrite /mdeg -inf_card_ends_in; apply: eq_card => a; rewrite !inE andbT.
Qed.

Lemma inf_size_ends (v : G) : size (inf_ends v) = mdeg v.
Proof. by rewrite -cardE inf_card_ends. Qed.

(** In a bridgeless multigraph no vertex has degree one: the only edge at such
    a vertex would be a bridge. *)
Lemma inf_mdeg1 : bridgeless G -> forall v : G, mdeg v != 1%N.
Proof.
move=> hbl v; apply/negP => /eqP h1.
have hcard : #|[set a : edge G * bool | inf_end a == v]| = 1%N.
  by rewrite inf_card_ends.
have [[e b] he] : exists a, a \in [set a : edge G * bool | inf_end a == v].
  by apply/card_gt0P; rewrite hcard.
rewrite inE in he; move/eqP: he => he.
have huniq : forall a', inf_end a' = v -> a' = (e, b).
  move=> a' ha'; apply: (card_le1_eqP (eq_leq hcard)); by rewrite inE ?ha' ?he.
have hother : endpoint (~~ b) e != v.
  apply/eqP => ho; have := huniq (e, ~~ b) ho.
  by case: b {he ho huniq}.
(* The edge [e] is then a bridge: a walk between its ends leaves [v], whose
   only arc end is the [b]-end of [e]. *)
apply: (hbl e) => w hw.
have [w' [hw' hmem]] : exists w',
    uwalk (endpoint b e) (endpoint (~~ b) e) w' /\ (e \in w' -> e \in w).
  case: b {huniq he hother} => /=; last by exists w.
  by exists (rev w); split; [exact: uwalk_rev | rewrite mem_rev].
case: w' hw' hmem => [/eqP hxy|f w'' hw' hmem].
  by move: hother; rewrite -hxy -he /inf_end eqxx.
have hf : f = e.
  case/orP: hw' => /andP[/eqP hs _].
    by have := huniq (f, false) (etrans hs he); case.
  by have := huniq (f, true) (etrans hs he); case.
exists e; first by rewrite inE.
by apply: hmem; rewrite hf mem_head.
Qed.

Lemma inf_loopless : bridgeless G -> loopless infG.
Proof.
(* A cycle edge is a loop only on a vertex with a single end. *)
move=> hbl [e|a]; first by rewrite /source /target /= xpair_eqE eqxx.
rewrite /source /target /=; apply/eqP => h.
set s := inf_ends (inf_end a) in h.
have has : a \in s by rewrite mem_inf_ends.
have hidx := inf_index_next (inf_ends_uniq (inf_end a)) has.
rewrite -/s -/(inf_nxt a) -h in hidx.
have hsz : size s != 1%N by rewrite inf_size_ends inf_mdeg1.
have hlt : (index a s < size s)%N by rewrite index_mem.
case: (ltnP (index a s).+1 (size s)) => h2.
  by move: hidx; rewrite modn_small // => /eqP; rewrite eqn_leq ltnn andbF.
have he : (index a s).+1 = size s by apply/eqP; rewrite eqn_leq hlt h2.
move: hidx; rewrite he modnn => h0.
by move: he hsz; rewrite h0 => <-.
Qed.

Lemma inf_cubic : bridgeless G -> cubic infG.
Proof.
move=> hbl; have hll := inf_loopless hbl; split => // a.
by rewrite -(mdeg_loopless _ hll) /mdeg inf_subdeg !in_setT.
Qed.

(** Walks around the cycle of a vertex. *)
Lemma inf_iter_end (a : edge G * bool) (n : nat) : inf_end (iter n inf_nxt a) = inf_end a.
Proof. by elim: n => //= n IH; rewrite inf_end_nxt. Qed.

Lemma inf_iter_next (a : edge G * bool) (n : nat) :
  iter n inf_nxt a = iter n (next (inf_ends (inf_end a))) a.
Proof. by elim: n => //= n IH; rewrite -IH /inf_nxt inf_iter_end. Qed.

Lemma inf_walk_iter (a : infG) (m n : nat) :
  @uwalk infG (iter m inf_nxt a) (iter (m + n) inf_nxt a)
        [seq (inr (iter i inf_nxt a) : edge infG) | i <- iota m n].
Proof.
elim: n m => [|n IH] m /=; first by rewrite addn0 eqxx.
by rewrite eqxx addnS -addSn (IH m.+1).
Qed.

(** Any two ends at the same vertex are joined around its cycle. *)
Lemma inf_reach (a b : edge G * bool) :
  inf_end b = inf_end a -> exists n, iter n inf_nxt a = b.
Proof.
move=> hb; set s := inf_ends (inf_end a).
have us : uniq s := inf_ends_uniq (inf_end a).
have has : a \in s by rewrite mem_inf_ends.
have hbs : b \in s by rewrite mem_inf_ends hb.
have hia : (index a s < size s)%N by rewrite index_mem.
have hib : (index b s < size s)%N by rewrite index_mem.
exists ((index b s + size s - index a s) %% size s).
rewrite inf_iter_next -/s.
have [hin hidx] := inf_index_iter ((index b s + size s - index a s) %% size s) us has.
rewrite -(nth_index a hin) hidx modnDmr subnKC ?modnDr ?modn_small ?nth_index //.
exact: leq_trans (ltnW hia) (leq_addl _ _).
Qed.

(** A cycle edge is not a bridge: go round the rest of the cycle. *)
Lemma inf_cycle_not_bridge (a : infG) : ~ is_bridge (inr a : edge infG).
Proof.
move=> hbr; set s := inf_ends (inf_end a).
have us : uniq s := inf_ends_uniq (inf_end a).
have has : a \in s by rewrite mem_inf_ends.
have hia : (index a s < size s)%N by rewrite index_mem.
have hd : (0 < size s)%N by apply: leq_ltn_trans hia.
have hiter : forall i, index (iter i inf_nxt a) s = (index a s + i) %% size s.
  by move=> i; rewrite inf_iter_next -/s; case: (inf_index_iter i us has).
have hin : forall i, iter i inf_nxt a \in s.
  by move=> i; rewrite inf_iter_next -/s; case: (inf_index_iter i us has).
have hfull : iter (size s) inf_nxt a = a.
  by rewrite -(nth_index a (hin _)) hiter modnDr modn_small // nth_index.
(* From [inf_nxt a] round to [a] through the other [size s - 1] cycle edges. *)
have hW := inf_walk_iter a 1 (size s).-1.
rewrite add1n prednK // hfull in hW.
have [g /set1P hg] := hbr _ (uwalk_rev hW).
rewrite hg mem_rev => /mapP[i].
rewrite mem_iota add1n prednK // => /andP[hi1 hi2] [hai].
have := hiter i; rewrite -hai => h.
have : (index a s + i == index a s + 0 %[mod size s]).
  by rewrite addn0 -h modn_small.
rewrite eqn_modDl mod0n modn_small // => /eqP hi0.
by rewrite hi0 in hi1.
Qed.

(** Walks of [G] lift to [infG], through copies of their own edges only. *)
Lemma inf_lift (x y : G) (w : seq (edge G)) (a0 b1 : infG) :
  uwalk x y w -> inf_end a0 = x -> inf_end b1 = y ->
  exists W : seq (edge infG),
    uwalk a0 b1 W /\ (forall g, (inl g : edge infG) \in W -> g \in w).
Proof.
have hcyc : forall a b : infG, inf_end b = inf_end a ->
    exists W : seq (edge infG),
      uwalk a b W /\ (forall g, (inl g : edge infG) \in W = false).
  move=> a b hab; have [n hn] := inf_reach hab.
  exists [seq (inr (iter i inf_nxt a) : edge infG) | i <- iota 0 n]; split.
    by have := inf_walk_iter a 0 n; rewrite add0n hn.
  by move=> g; apply/negP => /mapP[i _].
(* Each step through [g] goes round the cycle to the matching end of [g],
   then along its copy. *)
elim: w x a0 => [|g w IH] x a0 /=.
  move=> /eqP <- ha0 hb1.
  have [W [hW hW']] := hcyc a0 b1 (etrans hb1 (esym ha0)).
  by exists W; split => // h; rewrite hW'.
case/orP => /andP[/eqP hs hw] ha0 hb1.
  have [W1 [hW1 hW1']] := hcyc a0 (g, false) (etrans hs (esym ha0)).
  have [W2 [hW2 hW2']] := IH (target g) (g, true) hw erefl hb1.
  exists (W1 ++ inl g :: W2); split.
    by apply: uwalk_cat hW1 _; apply: uwalk_cons; [by [] | exact: hW2].
  move=> h; rewrite mem_cat hW1' /= in_cons => /orP[/eqP [->]|/hW2' hh].
    by rewrite mem_head.
  by rewrite in_cons hh orbT.
have [W1 [hW1 hW1']] := hcyc a0 (g, true) (etrans hs (esym ha0)).
have [W2 [hW2 hW2']] := IH (source g) (g, false) hw erefl hb1.
exists (W1 ++ inl g :: W2); split.
  by apply: uwalk_cat hW1 _; apply: uwalk_cons_rev; [by [] | exact: hW2].
move=> h; rewrite mem_cat hW1' /= in_cons => /orP[/eqP [->]|/hW2' hh].
  by rewrite mem_head.
by rewrite in_cons hh orbT.
Qed.

Lemma inf_bridgeless : bridgeless G -> bridgeless infG.
Proof.
(* A bridge [inl e] of [infG] would make [e] a bridge of [G]: a walk of [G]
   avoiding [e] lifts to one of [infG] avoiding [inl e]. *)
move=> hbl [e|a]; last exact: inf_cycle_not_bridge.
move=> hbr; apply: (hbl e) => w hw.
case: (boolP (e \in w)) => [ew|new]; first by exists e; rewrite ?inE.
exfalso.
have [W [hW hW']] := inf_lift (a0 := (e, false)) (b1 := (e, true)) hw erefl erefl.
have [g /set1P hg hgW] := hbr W hW.
rewrite hg in hgW.
by move: new; rewrite (hW' e hgW).
Qed.

(** Contraction: the edges of [G] whose copy lies in [C]. *)
Definition inf_contract (C : {set edge infG}) : {set edge G} :=
  [set e | (inl e : edge infG) \in C].

Lemma inf_contract_even (C : {set edge infG}) :
  even_subgraph C -> even_subgraph (inf_contract C).
Proof.
(* Summing the degrees of [C] over the ends at [v] counts the copies there
   once and the cycle edges of [v] twice. *)
move=> hC v.
have hA : subdeg (inf_contract C) v
        = (\sum_(a | inf_end a == v) (((inl a.1 : edge infG) \in C) : nat))%N.
  rewrite -inf_card_ends_in -sum1dep_card big_mkcondr /=.
  by apply: eq_bigr => a _; rewrite inE; case: (_ \in C).
have hB : (\sum_(a | inf_end a == v) (((inr (inf_prv a) : edge infG) \in C) : nat)
         = \sum_(a | inf_end a == v) (((inr a : edge infG) \in C) : nat))%N.
  rewrite [RHS](reindex_inj (can_inj inf_nxt_prv)) /=.
  by apply: eq_bigl => a; rewrite inf_end_prv.
have hsum : (\sum_(a | inf_end a == v) subdeg C a
            = subdeg (inf_contract C) v
              + 2 * \sum_(a | inf_end a == v) (((inr a : edge infG) \in C) : nat))%N.
  rewrite (eq_bigr _ (fun a _ => inf_subdeg C a)) !big_split /= hB -hA.
  by rewrite mul2n -addnn addnA.
have heven : ~~ odd (\sum_(a | inf_end a == v) subdeg C a).
  apply: (big_ind (fun n => ~~ odd n)); first by [].
    by move=> x y hx hy; rewrite oddD (negbTE hx) (negbTE hy).
  by move=> a _; exact: hC.
by move: heven; rewrite hsum oddD oddM addbF.
Qed.

Lemma inf_cover : u6_five_even_cover infG -> u6_five_even_cover G.
Proof.
case=> L [hs he hc]; exists (map inf_contract L); split.
- by rewrite size_map.
- by move=> C' /mapP[C hC ->]; exact: inf_contract_even (he C hC).
- move=> e; rewrite count_map -(hc (inl e)); apply: eq_count => C.
  by rewrite /= inE.
Qed.

End Inflate.

(** The reduction of five-even-subgraph double covers to cubic graphs. *)
Theorem five_even_cover_cubic_reduction : external_five_even_cover_cubic_reduction_statement.
Proof.
move=> Hcub G Hn He Hbl.
have [e0 _] := card_gt0P He.
apply: inf_cover; apply: Hcub.
- by apply/card_gt0P; exists ((e0, false) : infG G).
- by apply/card_gt0P; exists (inl e0 : edge (infG G)).
- exact: inf_cubic.
- exact: inf_bridgeless.
Qed.


(*@EDGE from=strong_5_cycle_double_cover_statement to=m_n_cycle_covers_statement kind=implies status=verified proof=unconditional_strong_5_cycle_double_cover_implies_m_n_cycle_covers cite="gc:e085" note="Row 10 is cubic-only and needs a circuit to start from: cubic_has_circuit supplies one (cycle_space.has_circuit on the full edge set, every degree being 3, hence never 1), and dropping Row 10's extra 'some member contains C' clause leaves exactly a (5,2)-cover of every cubic bridgeless graph; the cubic-to-general step is proved as five_even_cover_cubic_reduction: inflate every vertex into a cycle through its arc ends (a cubic bridgeless graph) and contract the cycles back, which keeps even subgraphs even" *)
Theorem unconditional_strong_5_cycle_double_cover_implies_m_n_cycle_covers :
  strong_5_cycle_double_cover_statement -> m_n_cycle_covers_statement.
Proof.
exact: strong_5_cycle_double_cover_implies_m_n_cycle_covers
  five_even_cover_cubic_reduction.
Qed.

(*@EDGE from=strong_5_cycle_double_cover_statement to=cycle_double_cover_statement kind=implies status=verified proof=unconditional_strong_5_cycle_double_cover_implies_cycle_double_cover cite="gc:e086" note="Composition of gc:e085 (Row 10 => Row 7, with the cubic reduction proved as five_even_cover_cubic_reduction) with the unconditional gc:e084 (Row 7 => Row 11, the even-subgraph-to-circuits refinement F14)" *)
Theorem unconditional_strong_5_cycle_double_cover_implies_cycle_double_cover :
  strong_5_cycle_double_cover_statement -> cycle_double_cover_statement.
Proof.
exact: strong_5_cycle_double_cover_implies_cycle_double_cover
  five_even_cover_cubic_reduction.
Qed.

(*@EDGE from=petersen_coloring_statement to=m_n_cycle_covers_statement kind=implies status=verified proof=unconditional_petersen_coloring_implies_m_n_cycle_covers cite="gc:e090" note="Pull back the Petersen graph's double cover by five even subgraphs along the Petersen colouring: the three edges at a vertex of a cubic graph go to a claw of the (triangle-free) Petersen graph (petersen_claw), every member meets every claw evenly (plab_claw_even) and every Petersen edge lies in exactly two members (plab_card), so petersen_pullback_cover gives a (5,2)-cover of every cubic bridgeless graph; the finite Petersen facts are proved by closed compute checks on 5-bit codes. The cubic-to-general step (Jaeger 1985 / Zhang) is proved as five_even_cover_cubic_reduction, as for gc:e085." *)
Theorem unconditional_petersen_coloring_implies_m_n_cycle_covers :
  petersen_coloring_statement -> m_n_cycle_covers_statement.
Proof.
exact: petersen_coloring_implies_m_n_cycle_covers five_even_cover_cubic_reduction.
Qed.

(*@EDGE from=petersen_coloring_statement to=cycle_double_cover_statement kind=implies status=verified proof=unconditional_petersen_coloring_implies_cycle_double_cover cite="gc:e091" note="Composition of gc:e090 (Petersen colouring => (5,2)-cover, with the cubic reduction proved as five_even_cover_cubic_reduction) with the unconditional gc:e084 (split the five even subgraphs into circuits, cycle_space.even_circuit_decomposition)." *)
Theorem unconditional_petersen_coloring_implies_cycle_double_cover :
  petersen_coloring_statement -> cycle_double_cover_statement.
Proof.
exact: petersen_coloring_implies_cycle_double_cover five_even_cover_cubic_reduction.
Qed.

(** Axiom audit (gc:e085, e086, e090, e091). *)
Print Assumptions five_even_cover_cubic_reduction.
Print Assumptions unconditional_strong_5_cycle_double_cover_implies_m_n_cycle_covers.
Print Assumptions unconditional_strong_5_cycle_double_cover_implies_cycle_double_cover.
Print Assumptions unconditional_petersen_coloring_implies_m_n_cycle_covers.
Print Assumptions unconditional_petersen_coloring_implies_cycle_double_cover.

(** ** The six perfect matchings of the Petersen graph (classical-lemmas TODO 8)

    The Petersen graph's own Berge–Fulkerson cover, used by implications_U10.v,
    where [petersen_BF_cover] proves [external_petersen_BF_cover_statement] from
    [petersen_BF_cover_body] below (the same Prop, stated here because that file
    imports this one).  [pmt a b] (for [a < b] the codes of two adjacent Petersen
    vertices) is a 6-bit code whose bit [k] is set iff that Petersen edge lies in
    the [k]-th perfect matching.  The matchings are the six complementary
    pentagon / pentagram pairs of K5: for a cyclic order (a0 a1 a2 a3 a4) of
    ['I_5], the edges {a_i, a_(i+1)} -- {a_(i+2), a_(i+4)}.  Two closed checks on
    small numbers ([pm_count_check], [pm_claw_check]) give the two properties; a
    claw is reduced to the three edges at a vertex by [petersen_claw].  A member
    [pmS k] contains BOTH orientations of each of its edges, as [Pedge] is the
    ordered-pair type. *)
Definition pmt (a b : nat) : nat :=
  match a, b with
  | 3, 12 => 10 | 3, 20 => 33 | 3, 24 => 20 | 5, 10 => 36 | 5, 18 => 24
  | 5, 24 => 3 | 6, 9 => 17 | 6, 17 => 6 | 6, 24 => 40 | 9, 18 => 34
  | 9, 20 => 12 | 10, 17 => 9 | 10, 20 => 18 | 12, 17 => 48 | 12, 18 => 5
  | _, _ => 0
  end.

Definition pml (a b : nat) : nat := pmt (minn a b) (maxn a b).

(** Every Petersen edge lies in exactly two of the six matchings. *)
Lemma pm_count_check :
  all (fun c => all (fun d => count (fun k => pbit k (pml c d)) (iota 0 6) == 2)
    (pnbr c)) pC2.
Proof. by compute. Qed.

(** At every Petersen vertex, each matching contains exactly one of the three
    edges. *)
Lemma pm_claw_check :
  all (fun c => all (fun d1 => all (fun d2 => all (fun d3 =>
      [&& d1 != d2, d2 != d3 & d1 != d3] ==>
      all (fun k => (pbit k (pml c d1) + pbit k (pml c d2)
                     + pbit k (pml c d3) == 1)%N) (iota 0 6))
    (pnbr c)) (pnbr c)) (pnbr c)) pC2.
Proof. by compute. Qed.

Definition pmX (X Y : {set 'I_5}) (k : nat) : bool := pbit k (pml (pcode X) (pcode Y)).

Definition pmS (k : nat) : {set Pedge} :=
  [set q : Pedge | pmX (val (val q).1) (val (val q).2) k].

Definition pmL : seq {set Pedge} := map pmS (iota 0 6).

Lemma pmXC (X Y : {set 'I_5}) k : pmX X Y k = pmX Y X k.
Proof. by rewrite /pmX /pml minnC maxnC. Qed.

Lemma pmS_supp (q : Pedge) (p y : petersenV) (k : nat) :
  psupp q = [set p; y] -> (q \in pmS k) = pmX (val p) (val y) k.
Proof.
move=> e.
have a : padj (val q).1 (val q).2 := valP q.
have n : (val q).1 != (val q).2 := padj_neq a.
have h1 : (val q).1 \in [set p; y] by rewrite -e /psupp set21.
have h2 : (val q).2 \in [set p; y] by rewrite -e /psupp set22.
rewrite inE; move: h1 h2 n; rewrite !inE => /orP[] /eqP -> /orP[] /eqP ->;
  rewrite ?eqxx // => _.
exact: pmXC.
Qed.

(** The Prop of [external_petersen_BF_cover_statement] (implications_U10.v),
    verbatim. *)
Lemma petersen_BF_cover_body :
  exists LP : seq {set Pedge},
    [/\ size LP = 6,
        (forall (S : {set Pedge}) (q1 q2 q3 : Pedge),
           S \in LP -> mut_adj3 Padj q1 q2 q3 ->
           ((q1 \in S) + (q2 \in S) + (q3 \in S))%N = 1)
      & (forall q : Pedge, count (fun S : {set Pedge} => q \in S) LP = 2)].
Proof.
exists pmL; split.
- by rewrite size_map size_iota.
- move=> S q1 q2 q3 /mapP[k hk ->] /petersen_claw
    [p [y1 [y2 [y3 [e1 e2 e3 [a1 a2 a3] [d12 d23 d13]]]]]].
  rewrite (pmS_supp _ e1) (pmS_supp _ e2) (pmS_supp _ e3) /pmX.
  have hd : forall y y' : petersenV, y != y' -> pcode (val y) != pcode (val y').
    by move=> y y'; apply: contraNneq => /pcode_inj/val_inj ->.
  move/allP: pm_claw_check => /(_ _ (pcode_V p)) /= /allP /(_ _ (pcode_nbr a1))
    /= /allP /(_ _ (pcode_nbr a2)) /= /allP /(_ _ (pcode_nbr a3)).
  rewrite (hd _ _ d12) (hd _ _ d23) (hd _ _ d13) => /implyP /(_ isT).
  move=> /andP[h0 /andP[h1 /andP[h2 /andP[h3 /andP[h4 /andP[h5 _]]]]]].
  move: hk; rewrite mem_iota add0n => /andP[_].
  by case: k => [|[|[|[|[|[|k]]]]]] // _; apply/eqP.
- move=> q; rewrite count_map.
  have a : padj (val q).1 (val q).2 := valP q.
  rewrite (eq_count (a2 := fun k => pmX (val (val q).1) (val (val q).2) k)); last first.
    by move=> k /=; rewrite inE.
  move/allP: pm_count_check => /(_ _ (pcode_V (val q).1)) /allP
    /(_ _ (pcode_nbr a)) /eqP.
  by rewrite /pmX.
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

(** (Until 2026-10-25 the edge gc:e098, [status=conditional]; its annotation now
    sits on [unconditional_cycle_double_covers_containing_predefined_2_regular_implies_cycle_double_cover]
    below, after [cdc_cubic_2connected_reduction].) *)
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

(** ================================================================= *)
(** ** gc:e098: the reduction of cycle double covers to cubic 2-connected
       multigraphs (classical-lemmas TODO 4)

    [cdc_cubic_2connected_reduction] proves
    [external_cdc_cubic_2connected_reduction_statement] without block
    decompositions.  Given a bridgeless [G] with at least two edges:
    - collapse its components onto one vertex ([comp_reduce.Hc]: connected,
      bridgeless, same edges, and the same even subgraphs, [cdc2c_Hc_even]);
    - inflate every vertex into a cycle ([infG], gc:e085's construction): a
      cubic, bridgeless and, by [inf_lift], connected multigraph
      ([cdc2c_inf_mconnected]) with at least four vertices;
    - such a multigraph is 2-connected ([cdc2c_cubic_two_connected]): a cut
      vertex [z] leaves two sides whose cuts consist of edges at [z], disjoint
      and nonempty, and [z] has three edges, so one cut is a single edge, a
      bridge ([cdc2c_cut1_bridge]);
    - a cycle double cover of the inflation contracts ([inf_contract]) to a
      double cover of [G] by even subgraphs, which split into circuits
      ([cycle_space.even_list_circuit_decomposition]).
    With a single edge, the edge is a loop and covers itself twice
    ([cdc2c_one_edge]). *)

(** A circuit is an even subgraph. *)
Lemma cdc2c_circuit_even (G : mgraph) (C : {set edge G}) :
  is_circuit C -> forall v : G, ~~ odd (subdeg C v).
Proof. by case=> _ hreg _ v; case: (hreg v) => ->. Qed.

(** Even subgraphs of the collapsed graph [Hc r0] are even subgraphs of [G]
    (the tail of comp_reduce.five_even_cover_connected_reduce, for one set). *)
Lemma cdc2c_Hc_even (G : mgraph) (r0 : G) (C : {set edge G}) :
  mroot r0 = r0 -> (forall v : Hc r0, ~~ odd (@subdeg (Hc r0) C v)) ->
  forall v : G, ~~ odd (subdeg C v).
Proof.
move=> hr0 hC v.
have keyends : forall (v : G) (h : vpred r0 v) (b : bool),
    mroot v != v -> #|@ends_at (Hc r0) C b (Sub v h)| = #|ends_at C b v|.
  move=> w h b hw; apply: eq_card => f; rewrite !inE.
  by rewrite -val_eqE val_prj SubK (pr_eqE _ hr0 hw).
have keydeg : forall (v : G) (h : vpred r0 v),
    mroot v != v -> @subdeg (Hc r0) C (Sub v h) = subdeg C v.
  move=> w h hw.
  by rewrite /subdeg (keyends w h false hw) (keyends w h true hw).
case: (boolP (mroot v == v)) => [/eqP hvr|hnr]; last first.
  have hv : vpred r0 v by rewrite /vpred hnr.
  by rewrite -(keydeg v hv hnr); exact: (hC (Sub v hv)).
have hsum : ~~ odd (\sum_(y in mcomp v) subdeg C y).
  by rewrite sum_subdeg_cut (cut_mcomp v) setI0 cards0 addn0 oddM /=.
have hrest : ~~ odd (\sum_(y in mcomp v | y != v) subdeg C y).
  apply: odd_sum_even_P => y /andP[hy hyv].
  have hnr : mroot y != y.
    apply/negP => /eqP hyy.
    by move: hyv; rewrite (mroot_unique hvr hy hyy) eqxx.
  have hv : vpred r0 y by rewrite /vpred hnr.
  by rewrite -(keydeg y hv hnr); exact: (hC (Sub y hv)).
by move: hsum; rewrite (bigD1 v (mcomp_id v)) /= oddD (negbTE hrest) addbF.
Qed.

(** The inflation of a connected multigraph is connected. *)
Lemma cdc2c_inf_mconnected (G : mgraph) : mconnected G -> mconnected (infG G).
Proof.
move=> hc a b.
have [w hw] := hc (inf_end a) (inf_end b).
have [W [hW _]] := inf_lift hw erefl erefl.
by exists W.
Qed.

(** An edge alone in a cut is a bridge. *)
Lemma cdc2c_cut1_bridge (H : mgraph) (A : {set H}) (f : edge H) :
  cut A = [set f] -> is_bridge f.
Proof.
move=> hA; apply/is_bridgeP => w hw.
have hf : f \in cut A by rewrite hA set11.
have hne : (source f \in A) != (target f \in A).
  by move: hf; rewrite inE; case: (source f \in A); case: (target f \in A).
have [g hgw] := uwalk_crosses hw hne.
by rewrite hA => /set1P hg; rewrite -hg.
Qed.

(** Adjacency avoiding the vertex [z]. *)
Definition cdc2c_radj (H : mgraph) (z : H) : rel H :=
  fun u v => [&& u != z, v != z & mrel u v].

Lemma cdc2c_reach_ne (H : mgraph) (z a u : H) :
  a != z -> connect (cdc2c_radj z) a u -> u != z.
Proof.
move=> ha /connectP [p hp ->]; elim: p a ha hp => //= c p IH a ha /andP[hac hp].
by apply: IH hp; case/and3P: hac.
Qed.

Lemma cdc2c_reach_walk (H : mgraph) (z x y : H) :
  connect (cdc2c_radj z) x y -> x != z ->
  exists w, uwalk x y w /\
    all (fun e => (source e \notin [set z]) && (target e \notin [set z])) w.
Proof.
case/connectP => p; elim: p x => [x _ hl _|c p IH x /= /andP[hxc hp] hl hx].
  have hxy : x = y by move: hl.
  by exists [::]; rewrite /= hxy eqxx.
case/and3P: hxc => _ hc /existsP[e he].
have [w [hw hall]] := IH c hp hl hc.
exists (e :: w); split.
  case/orP: he => /andP[/eqP hs /eqP ht].
  - by apply: uwalk_cons; [exact: hs | rewrite ht].
  - by apply: uwalk_cons_rev; [exact: ht | rewrite hs].
rewrite /= hall andbT !inE.
by case/orP: he => /andP[/eqP -> /eqP ->]; rewrite hx hc.
Qed.

(** A connected, bridgeless, loopless cubic multigraph with at least three vertices
    is 2-connected: a cut vertex [z] separates two sides whose cuts consist of edges
    at [z]; they are disjoint and nonempty, and [z] has three edges, so one cut is a
    single edge, a bridge. *)
Lemma cdc2c_cubic_two_connected (H : mgraph) :
  cubic H -> mconnected H -> bridgeless H -> (3 <= #|H|)%N -> two_connected H.
Proof.
move=> [hll hreg] hcon hbl h3; split => // z x y hx hy.
rewrite !inE in hx hy.
case: (boolP (connect (cdc2c_radj z) x y)) => cxy; first exact: cdc2c_reach_walk cxy hx.
exfalso.
have hsym : symmetric (cdc2c_radj z).
  by move=> p q; rewrite /cdc2c_radj mrel_sym; case: (p != z); case: (q != z).
have cS : forall a u v : H, a != z -> connect (cdc2c_radj z) a u -> v != z -> mrel u v ->
    connect (cdc2c_radj z) a v.
  move=> a u v ha hu hv huv; have hu' := cdc2c_reach_ne ha hu.
  apply: (connect_trans hu); apply: connect1.
  by rewrite /cdc2c_radj hv huv hu'.
have hmrel : forall f : edge H, mrel (source f) (target f).
  by move=> f; apply/existsP; exists f; rewrite !eqxx.
pose S := [set u | connect (cdc2c_radj z) x u].
pose T := [set u | connect (cdc2c_radj z) y u].
have hcutz : forall a : H, a != z -> forall f, f \in cut [set u | connect (cdc2c_radj z) a u] ->
    (source f == z) || (target f == z).
  move=> a ha f; rewrite !inE.
  case hs: (connect _ a (source f)); case ht: (connect _ a (target f)) => //= _.
  - apply/orP; right; apply/negPn/negP => htz.
    by move: ht; rewrite (cS a (source f) (target f) ha hs htz (hmrel f)).
  - apply/orP; left; apply/negPn/negP => hsz.
    by move: hs; rewrite (cS a (target f) (source f) ha ht hsz) // mrel_sym.
have hzout : forall a : H, a != z -> z \notin [set u | connect (cdc2c_radj z) a u].
  by move=> a ha; rewrite inE; apply/negP => /(cdc2c_reach_ne ha); rewrite eqxx.
have hne : forall a : H, a != z -> exists f, f \in cut [set u | connect (cdc2c_radj z) a u].
  move=> a ha; have [w hw] := hcon a z.
  have hsep : (a \in [set u | connect (cdc2c_radj z) a u]) != (z \in [set u | connect (cdc2c_radj z) a u]).
    by rewrite (negbTE (hzout a ha)) inE connect0.
  by have [f _ hf] := uwalk_crosses hw hsep; exists f.
have hST : forall u, u \in S -> u \in T -> False.
  move=> u; rewrite !inE => hxu hyu; move: cxy.
  have csym := sym_connect_sym hsym.
  by rewrite (connect_trans hxu) // csym.
have hdisj : [disjoint cut S & cut T].
  apply/pred0P => f /=; apply/negP => /andP[hfS hfT].
  have hcS : (source f \in S) (+) (target f \in S) by move: hfS; rewrite inE.
  have hcT : (source f \in T) (+) (target f \in T) by move: hfT; rewrite inE.
  case/orP: (hcutz x hx f hfS) => /eqP hz.
  - have hzS : (source f \in S) = false by rewrite hz; apply/negbTE/hzout.
    have hzT : (source f \in T) = false by rewrite hz; apply/negbTE/hzout.
    by move: hcS hcT; rewrite hzS hzT /= => htS htT; exact: (hST (target f)).
  - have hzS : (target f \in S) = false by rewrite hz; apply/negbTE/hzout.
    have hzT : (target f \in T) = false by rewrite hz; apply/negbTE/hzout.
    by move: hcS hcT; rewrite hzS hzT !addbF => hsS hsT; exact: (hST (source f)).
have hsub : cut S :|: cut T \subset edges_at z.
  apply/subsetP => f; rewrite inE => /orP[] hf; rewrite inE /incident.
  - by case/orP: (hcutz x hx f hf) => hz; apply/existsP; [exists false | exists true].
  - by case/orP: (hcutz y hy f hf) => hz; apply/existsP; [exists false | exists true].
have hcard : (#|cut S| + #|cut T| <= 3)%N.
  rewrite -cardsUI (disjoint_setI0 hdisj) cards0 addn0 -(hreg z).
  exact: subset_leq_card hsub.
have [f1 hf1] := hne x hx; have [f2 hf2] := hne y hy.
have h1 : (0 < #|cut S|)%N by apply/card_gt0P; exists f1.
have h2 : (0 < #|cut T|)%N by apply/card_gt0P; exists f2.
case: (leqP #|cut S| 1) => hS.
  have /cards1P [f hf] : #|cut S| == 1 by rewrite eqn_leq hS h1.
  exact: hbl f (cdc2c_cut1_bridge hf).
have hT : (#|cut T| <= 1)%N.
  by rewrite -(leq_add2l 2); apply: leq_trans hcard; rewrite leq_add2r.
have /cards1P [f hf] : #|cut T| == 1 by rewrite eqn_leq hT h2.
exact: hbl f (cdc2c_cut1_bridge hf).
Qed.

(** A bridgeless multigraph with exactly one edge: the edge is a loop, which covered
    twice by itself is a cycle double cover. *)
Lemma cdc2c_one_edge (G : mgraph) :
  bridgeless G -> #|edge G| = 1 -> exists L : seq {set edge G}, cdc L.
Proof.
move=> hbl h1.
have /cards1P [e he] : #|[set: edge G]| == 1 by rewrite cardsT h1.
have hall : forall f : edge G, f = e by move=> f; apply/set1P; rewrite -he in_setT.
have hloop : source e = target e.
  apply/eqP; apply/negPn/negP => hne; apply: (hbl e); apply/is_bridgeP => w.
  case: w => [/= /eqP hst|g w _]; first by move: hne; rewrite hst eqxx.
  by rewrite (hall g) mem_head.
have hcirc : is_circuit [set e].
  split.
  - by apply/set0Pn; exists e; rewrite set11.
  - move=> v; case: (eqVneq v (source e)) => [->|hv]; first by right; exact: subdeg_loop.
    left; rewrite /subdeg.
    have h0 : forall b, ends_at [set e] b v = set0.
      move=> b; apply/setP => f; rewrite !inE (hall f) eqxx /=.
      by apply/negbTE; case: b => /=; rewrite eq_sym // -hloop.
    by rewrite !h0 cards0.
  - move=> x y /existsP[f /andP[_ /existsP[b /eqP hx]]] /existsP[g /andP[_ /existsP[c /eqP hy]]].
    exists [::]; rewrite /walk_in /= andbT.
    move: hx hy; rewrite (hall f) (hall g).
    by case: b; case: c => /= <- <-; rewrite ?hloop.
exists [:: [set e]; [set e]]; split.
  by move=> C; rewrite !inE => /orP[] /eqP ->.
by move=> f; rewrite (hall f) /= set11.
Qed.

(** The reduction: cycle double covers of cubic 2-connected multigraphs give cycle
    double covers of all bridgeless multigraphs. *)
Theorem cdc_cubic_2connected_reduction : external_cdc_cubic_2connected_reduction_statement.
Proof.
move=> Hcub G Hn He Hbl.
case: (ltnP 1 #|edge G|) => hE; last first.
  have h1 : #|edge G| = 1 by apply/eqP; rewrite eqn_leq hE He.
  exact: cdc2c_one_edge Hbl h1.
have /card_gt0P[x0 _] : (0 < #|[set: G]|)%N by rewrite cardsT.
pose r0 := mroot x0.
have hr0 : mroot r0 = r0 := mroot_root x0.
have hKc : mconnected (Hc r0) := Hc_mconnected hr0.
have hKb : bridgeless (Hc r0) := @Hc_bridgeless G r0 Hbl.
have hHcub : cubic (infG (Hc r0)) := inf_cubic hKb.
have hHb : bridgeless (infG (Hc r0)) := inf_bridgeless hKb.
have hHc : mconnected (infG (Hc r0)) := cdc2c_inf_mconnected hKc.
have hHcard : (3 <= #|infG (Hc r0)|)%N.
  have -> : #|infG (Hc r0)| = (#|edge G| * 2)%N by rewrite card_prod card_bool.
  by apply: leq_trans (leq_mul hE (leqnn 2)).
have hpos : (0 < #|infG (Hc r0)|)%N by apply: leq_trans hHcard.
have [L [hLc hLn]] := Hcub (infG (Hc r0)) hpos hHcub
  (cdc2c_cubic_two_connected hHcub hHc hHb hHcard).
pose M := map (@inf_contract (Hc r0)) L.
have hMev : forall X : {set edge G}, X \in M -> forall v : G, ~~ odd (subdeg X v).
  move=> X /mapP[C hC ->]; apply: (cdc2c_Hc_even hr0).
  exact: inf_contract_even (cdc2c_circuit_even (hLc C hC)).
have hMn : forall e : edge G, count (fun X : {set edge G} => e \in X) M = 2.
  move=> e; rewrite count_map -(hLn (inl e)); apply: eq_count => C.
  by rewrite /= inE.
have [D [hDc hDn]] := even_list_circuit_decomposition hMev.
by exists D; split => // e; rewrite hDn hMn.
Qed.

(*@EDGE from=cycle_double_covers_containing_predefined_2_regular_statement to=cycle_double_cover_statement kind=implies status=verified proof=unconditional_cycle_double_covers_containing_predefined_2_regular_implies_cycle_double_cover cite="gc:e098" note="Instantiate the source at S = set0: it is 2-regular (degree 0 everywhere, subdeg0), G - E(set0) = G is connected since a 2-connected multigraph is connected (two_connected_del_set0), and the empty circuit decomposition [::] of set0 is trivially contained in L; so the source yields a CDC of every cubic 2-connected multigraph. The cubic 2-connected-to-general step is proved as cdc_cubic_2connected_reduction: collapse the components (comp_reduce.Hc), inflate every vertex into a cycle (infG, a connected cubic bridgeless multigraph, 2-connected since a cut vertex of a cubic graph forces a bridge), contract a cycle double cover back to even subgraphs and split them into circuits; a single edge is a loop covered twice." *)
Theorem unconditional_cycle_double_covers_containing_predefined_2_regular_implies_cycle_double_cover :
  cycle_double_covers_containing_predefined_2_regular_statement ->
  cycle_double_cover_statement.
Proof.
exact: cycle_double_covers_containing_predefined_2_regular_implies_cycle_double_cover
  cdc_cubic_2connected_reduction.
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

(** ** Axiom audit (gc:e209) *)

Print Assumptions cdc_simple_reduction.
Print Assumptions unconditional_small_cycle_double_cover_implies_cycle_double_cover.

(** ** Axiom audit (gc:e098) *)

Print Assumptions cdc_cubic_2connected_reduction.
Print Assumptions unconditional_cycle_double_covers_containing_predefined_2_regular_implies_cycle_double_cover.

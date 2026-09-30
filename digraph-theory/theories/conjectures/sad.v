(** * Digraph.conjectures.sad — P3 "arc-connectivity + Strong Arc Decompositions"

    Statement-only formalization (no axioms) of the Bang-Jensen–Yeo Strong Arc
    Decomposition (SAD) cluster, plus the working conjecture WC3 (the K = 3 form)
    and the bilateral controlled-lifting lemma CL1 as a Theorem-target.
    See docs/CONJECTURES_FORMALIZATION_PLAN.md §4 (P3), §5, §7, and the problem
    folder problems/arc_disjoint_strong_spanning_subdigraphs (ledger entries
    P2-CL1, WC3, central question).

    A subdigraph is represented by its arc set [A : {set (D * D)}] (a set of
    ordered vertex pairs that are genuine arcs of [D]); the carrier vertex set is
    always the FULL [V(D)] (we only ever talk about SPANNING subdigraphs), so a
    subdigraph is exactly an arc subset of [arcset D].  Reachability inside such a
    subdigraph is fingraph's [connect] over the relation "the pair is in [A]".

    New primitives (general digraph level):
      - [arcset D]          : the arc set of [D], as [{set (D * D)}].
      - [outcut X]          : the out-cut δ⁺(X) = arcs from [X] to its complement.
      - [arc_strong D k]    : [D] is k-arc-strong — every nonempty proper vertex
                              set [X] has out-cut of size ≥ k (≡ λ(D) ≥ k).
      - [lambda D]          : arc-strong connectivity λ(D), the minimum out-cut
                              size over nonempty proper [X] (guarded; see note).
      - [in_arcset A]       : [A] uses only genuine arcs of [D].
      - [subrel_of A]       : the boolean arc relation of the subdigraph [(V,A)].
      - [spanning_strong A] : [(V,A)] is a spanning strongly connected subdigraph.
      - [SAD D]             : [D] has a Strong Arc Decomposition — its arc set
                              partitions into two spanning-strong arc sets.

    Nodes (Definitions of type Prop):
      - [bang_jensen_yeo_SAD_statement] : ∃K, every K-arc-strong digraph has a SAD.
      - [WC3_statement]                 : the K = 3 form (working conjecture).
      - [CL1_statement]                 : the bilateral controlled-lifting lemma,
                                          as a Theorem-target (relative claim).

    Edges (Qed-closed relative theorems):
      - [WC3_implies_SAD]   : WC3  ⟹  Bang-Jensen–Yeo SAD (instantiate K = 3).
      - [arc_strong_mono]   : k-arc-strong ⟹ j-arc-strong for j ≤ k (sanity edge). *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented dipath strong.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Arc sets, out-cuts, and arc-strong connectivity *)

Section ArcConnectivity.
Variable D : diGraphType.
Implicit Types (X : {set D}) (A : {set (D * D)}).

(** The arc set of [D]: all ordered pairs [(u,v)] that are genuine arcs. *)
Definition arcset : {set (D * D)} := [set p | p.1 --> p.2].

Lemma in_arcsetE (u v : D) : ((u, v) \in arcset) = (u --> v).
Proof. by rewrite inE. Qed.

(** The out-cut δ⁺(X): arcs whose tail is in [X] and whose head is outside. *)
Definition outcut X : {set (D * D)} :=
  [set p in arcset | (p.1 \in X) && (p.2 \notin X)].

Lemma in_outcutE X (u v : D) :
  ((u, v) \in outcut X) = [&& u --> v, u \in X & v \notin X].
Proof. by rewrite inE in_arcsetE /= andbA. Qed.

(** [D] is k-arc-strong: every nonempty proper vertex subset has out-cut of size
    at least [k].  This is exactly λ(D) ≥ k (Menger: equivalently every ordered
    pair is joined by k arc-disjoint dipaths), the standard "k-arc-connected"
    hypothesis of the conjecture.  The guards [X != set0], [X != setT] exclude
    the two trivial cuts (empty out-cut), so the predicate is not vacuous. *)
Definition arc_strong (k : nat) : Prop :=
  forall X : {set D}, X != set0 -> X != [set: D] -> (k <= #|outcut X|)%N.

(** Arc-strong connectivity λ(D) as the actual minimum out-cut size over
    nonempty proper [X].  We fold with [minn] over those [X], using the default
    (empty-fold identity) [#|D| * #|D|] — an upper bound on any cut size — so that
    on degenerate digraphs with no nonempty proper subset (|D| ≤ 1) the value is
    harmless; for the conjectures themselves we use the cleaner predicate
    [arc_strong]. *)
Definition lambda : nat :=
  \big[minn/(#|D| * #|D|)%N]_(X : {set D} | (X != set0) && (X != [set: D]))
     #|outcut X|.

(** Any out-cut has size at most [#|D| * #|D|] (it is a set of vertex pairs). *)
Lemma outcut_le_sq X : (#|outcut X| <= #|D| * #|D|)%N.
Proof.
apply: (@leq_trans #|[set: D * D]|); first exact/subset_leq_card/subsetT.
by rewrite cardsT card_prod.
Qed.

(** Faithfulness bridge: [arc_strong k] is exactly "k ≤ every proper out-cut",
    which gives "k ≤ λ(D)" whenever a proper cut exists (|D| ≥ 2). *)
Lemma arc_strong_lambda (k : nat) :
  (exists X : {set D}, (X != set0) && (X != [set: D])) ->
  arc_strong k -> (k <= lambda)%N.
Proof.
move=> [X0 /andP[h01 h02]] hk; rewrite /lambda.
elim/big_ind: _ => [|m n hm hn|X /andP[h1 h2]].
- by apply: leq_trans (hk X0 h01 h02) (outcut_le_sq X0).
- by rewrite leq_min hm hn.
- exact: hk.
Qed.

End ArcConnectivity.

Arguments arcset D : clear implicits.
Arguments lambda D : clear implicits.

(** Monotonicity sanity edge: k-arc-strong implies j-arc-strong for j ≤ k. *)
Lemma arc_strong_mono (D : diGraphType) (j k : nat) :
  (j <= k)%N -> arc_strong D k -> arc_strong D j.
Proof. by move=> jk hk X h1 h2; exact: leq_trans jk (hk X h1 h2). Qed.

(** ** Spanning strong subdigraphs (by arc set) *)

Section SpanningStrong.
Variable D : diGraphType.
Implicit Types (A : {set (D * D)}).

(** [A] uses only genuine arcs of [D]. *)
Definition in_arcset A : Prop := A \subset arcset D.

(** The boolean arc relation of the subdigraph [(V, A)]: [u] beats [v] iff the
    pair [(u,v)] is in [A]. *)
Definition subrel_of A : rel D := fun u v => (u, v) \in A.

(** [(V, A)] is a spanning strongly connected subdigraph: [A] consists of genuine
    arcs and every ordered pair of vertices is joined by a directed path that uses
    only arcs of [A] ([connect] over [subrel_of A]).  "Spanning" is automatic: the
    vertex set is the full [V(D)]. *)
Definition spanning_strong A : Prop :=
  in_arcset A /\ forall u v : D, connect (subrel_of A) u v.

(** A spanning-strong subdigraph is strong in the host's sense too: any [A]-path
    is in particular an [arc]-path, so [strongb D] follows.  (Sanity lemma; the
    converse direction needed for the conjectures is the hard content.) *)
Lemma spanning_strong_host A : spanning_strong A -> strongb D.
Proof.
move=> [Asub Aconn]; apply/strongP=> x y.
apply: connect_sub (Aconn x y) => u v; rewrite /subrel_of => uvA.
by apply: connect1; have := subsetP Asub _ uvA; rewrite in_arcsetE.
Qed.

End SpanningStrong.

Arguments in_arcset {D} A.
Arguments subrel_of {D} A.
Arguments spanning_strong {D} A.

(** ** Strong Arc Decomposition (SAD) *)

(** [D] has a Strong Arc Decomposition: its arc set partitions into two arc sets
    [A1], [A2] (disjoint, covering all of [arcset D]) that are each a spanning
    strongly connected subdigraph.  Equivalently, a 2-colouring of the arcs in
    which each colour class spans and is strongly connected. *)
Definition SAD (D : diGraphType) : Prop :=
  exists A1 A2 : {set (D * D)},
    [/\ [disjoint A1 & A2],
        A1 :|: A2 = arcset D,
        spanning_strong A1
      & spanning_strong A2 ].

(** A 2-colouring formulation: a single colouring [c : D*D -> bool] of the arcs
    whose two classes are both spanning-strong.  Equivalent to [SAD] (the two
    presentations are interderivable; we record both and the bridge). *)
Definition SAD_colouring (D : diGraphType) : Prop :=
  exists c : (D * D) -> bool,
    spanning_strong [set p in arcset D | c p] /\
    spanning_strong [set p in arcset D | ~~ c p].

Lemma SAD_colouring_SAD (D : diGraphType) : SAD_colouring D -> SAD D.
Proof.
move=> [c [h1 h2]]; exists [set p in arcset D | c p], [set p in arcset D | ~~ c p].
split=> //.
- rewrite -setI_eq0; apply/eqP/setP=> p; rewrite !inE.
  by case: (p.1 --> p.2); case: (c p).
- apply/setP=> p; rewrite !inE.
  by case: (p.1 --> p.2); case: (c p).
Qed.

(** ** Bang-Jensen–Yeo SAD existence conjecture *)

(** Corpus row: opg:arc_disjoint_strongly_connected_spanning_subdigraphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/arc_disjoint_strongly_connected_spanning_subdigraphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/arc_disjoint_strongly_connected_spanning_subdigraphs.json
    English statement: (Open Problem Garden, Arc-disjoint strongly connected spanning subdigraphs (Bang-Jensen and Yeo 2004))
      There is an integer K such that every nonempty finite K-arc-strong digraph has a strong
      arc decomposition: its arc set splits into two disjoint parts, each of which, taken with
      the full vertex set, is a strongly connected spanning subdigraph. K-arc-strong means that
      every nonempty proper vertex set has at least K arcs leaving it.
    Definitions: [arcset D] - the set of ordered pairs that are arcs (this file); [outcut X] -
      the arcs from X to its complement (this file); [arc_strong D k] - every nonempty proper
      vertex set has out-cut of size at least k, that is arc-connectivity at least k (this
      file); [spanning_strong A] - A uses only real arcs and every ordered pair of vertices is
      joined by a path using only arcs of A (this file); [SAD D] - the arc set partitions into
      two spanning-strong parts (this file).
    Notes: A subdigraph is represented by its arc set, the vertex set always being the whole of
      V(D), so spanning is automatic. The two parts being arc-disjoint AND covering the arc set
      is a partition, which is the decomposition reading; K = 2 is known to be false. *)
Definition bang_jensen_yeo_SAD_statement : Prop :=
  exists K : nat,
    forall D : diGraphType, (0 < #|D|)%N -> arc_strong D K -> SAD D.

(** ** WC3 — the working conjecture (K = 3 form) *)

(** Corpus row: derived:drv_sad_wc3
    Site: none
    Review: none
    English statement: (corpus derived row WC3, the K = 3 working instance of the Bang-Jensen-Yeo conjecture)
      Every nonempty finite 3-arc-strong digraph (every nonempty proper vertex set has at least
      3 arcs leaving it) has a strong arc decomposition: its arc set splits into two disjoint
      parts each inducing, on the full vertex set, a strongly connected spanning subdigraph.
    Definitions: [arc_strong D 3] and [SAD D] and [spanning_strong] and [outcut] (this file).
    Notes: All known obstructions to a strong arc decomposition are exactly 2-arc-strong, which
      is why 3 is conjectured to suffice; the edge [WC3_implies_SAD] in this file derives the
      Bang-Jensen-Yeo statement with K = 3. *)
Definition WC3_statement : Prop :=
  forall D : diGraphType, (0 < #|D|)%N -> arc_strong D 3 -> SAD D.

(** Edge: WC3 ⟹ Bang-Jensen–Yeo SAD (take K = 3). *)
Theorem WC3_implies_SAD :
  WC3_statement -> bang_jensen_yeo_SAD_statement.
Proof. by move=> H; exists 3 => D n0 h3; exact: H. Qed.

(** ** CL1 — bilateral controlled-lifting lemma (Theorem-target) *)

(** No corpus row: the bilateral controlled-lifting lemma P2-CL1 of
    problems/arc_disjoint_strong_spanning_subdigraphs: if the vertex set splits into two parts
    of size at least 2, each induced subdigraph has a strong arc decomposition, and each of the
    two bridge cuts splits into two nonempty parts, then the whole digraph has a strong arc
    decomposition. It is a relative theorem-target of the SAD attack, provable without resolving
    WC3, and has no corpus row. *)
Definition CL1_statement : Prop :=
  forall (D : diGraphType) (V1 : {set D}),
    let V2 := ~: V1 in
    (2 <= #|V1|)%N -> (2 <= #|V2|)%N ->
    SAD (induced_digraph V1) -> SAD (induced_digraph V2) ->
    (exists B1 B2 : {set (D * D)},
       [/\ [disjoint B1 & B2], B1 :|: B2 = outcut V1, B1 != set0 & B2 != set0]) ->
    (exists C1 C2 : {set (D * D)},
       [/\ [disjoint C1 & C2], C1 :|: C2 = outcut V2, C1 != set0 & C2 != set0]) ->
    SAD D.

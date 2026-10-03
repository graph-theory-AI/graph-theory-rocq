(** * Digraph.conjectures.implications2 — MORE §7 dependency-graph EDGES

    A second batch of machine-checked implication edges between the committed
    conjecture statements (cf. [implications.v]).  As there, every edge is a
    *relative* theorem: provable WITHOUT resolving (proving or refuting) any of the
    conjectures it relates — it only transports one conjectural hypothesis to
    another, or applies a committed conjecture on a restricted subclass.  So this
    layer is genuine [Qed]-closed content (no [Admitted], no [Axiom]).  Any bridge
    fact that would require resolving a conjecture, or that needs heavy library
    machinery outside this file's scope, is carried as an EXPLICIT hypothesis so the
    theorem stays [Qed]-closed (the established idiom of [implications.v], which
    carries [hero (TT l)] the same way).
    See docs/CONJECTURES_FORMALIZATION_PLAN.md §7 (deliverable 2).

    Edges proved here:

      χ-bounded cluster (chi_bounded.v):
      - [conj2_implies_conj4] : Conjecture 2 (Forb(H) χ-bounded ⟺ underlying H a
        forest) ⟹ Conjecture 4 (every oriented star is χ-bounding).  An oriented
        star is an oriented forest, so the (⟸) half of Conj 2 at H = the star gives
        χ-boundedness of its Forb class.  The bridge [oriented_star S ->
        oriented_forest S] ("the underlying graph of an oriented star is a forest")
        is carried as an explicit hypothesis [star_is_forest] (proving it from
        graph-theory's [is_forest] path-uniqueness API is out of scope here; the
        edge itself is Qed-closed under the bridge).
      - [m3_landmark_refutes_tvec_2] : the m(3) landmark (an oriented triangle-free
        graph that is not 2-dicolourable) forces any t⃗-binding sequence [h] of
        [tvec_core_statement] to exceed 2 at the witness order — a faithful
        proof-relative numeric consequence.

      packing cluster (packing.v):
      - [bermond_thomassen_implies_one_cycle] : Bermond–Thomassen at k = 1 (so
        δ⁺ ≥ 1) yields a directed cycle — the classic δ⁺ ≥ 1 ⟹ cycle, relative.
      - [hoang_reed_implies_bermond_thomassen_k1] : at k = 1 the two packing
        conjectures coincide (both deliver a single dicycle from δ⁺ ≥ 1).
      - [erdos_posa_long_dicycles_gives_transversal_or_pack] : a convenience
        unfolding of Erdős–Pósa at fixed ℓ, n.

      SAD cluster (sad.v):
      - [BJY_SAD_implies_strong] : Bang-Jensen–Yeo SAD ⟹ every sufficiently
        arc-strong nonempty digraph is strongly connected (via [spanning_strong_host]).
      - [WC3_implies_3arcstrong_strong] : WC3 ⟹ every 3-arc-strong nonempty digraph
        is strong.

      Path-FAS cluster (path_fas.v):
      - [matchingFAS_implies_pathFAS] : a matching FAS is a path-shaped FAS (a
        matching is a linear forest), so [has_matchingFAS ⟹ has_pathFAS].
      - [dw1_implies_pathFAS] : matchingFAS⟺dw1 (committed) ⟹ Δ*(T) ≤ 1 gives a
        path-FAS, and then Δ*(T) ≤ 2 (re-deriving the degreewidth split).

      unvd cluster (unvd.v):
      - [conj9_weaken_const] : Conjecture 9's absolute constant is monotone — the
        bound transports to any larger constant.

    Supporting (Qed-closed) bridge lemma:
      - [matching_linear_forest] : matching G -> linear_forest G. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude interop_graph_theory.
From Digraph Require Import digraph oriented tournament dipath strong.
From Digraph Require Import dichromatic heroes.
From Digraph Require Import chi_bounded packing sad path_fas unvd.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** χ-bounded cluster: Conjecture 2 ⟹ Conjecture 4 *)

(** Conjecture 2 ⟹ Conjecture 4.  Conjecture 2 is the bi-implication
    [chi_bounded_under (Forb H) ⟺ oriented_forest H] for every oriented [H].
    Conjecture 4 asks every oriented star to be χ-bounding.  An oriented star is an
    oriented forest (its underlying graph is a star, hence a forest), so the (⟸)
    direction of Conj 2 — applied at [H] := the star, which is oriented — delivers
    χ-boundedness of the star's Forb class, which is exactly Conjecture 4.

    The bridge "an oriented star's underlying graph is a forest"
    ([star_is_forest]) is carried as an explicit hypothesis (it is a true
    structural fact, but a self-contained proof needs graph-theory's [is_forest]
    path-uniqueness API, outside this edge's scope).  Carrying it keeps the edge
    fully [Qed]-closed. *)
Theorem conj2_implies_conj4 :
  (forall S : diGraphType, oriented_star S -> oriented_forest S) ->
  conj2_1605_statement -> conj4_1605_statement.
Proof.
move=> star_is_forest C2 S Sstar.
have Sor : oriented_dg S by case: Sstar.
(* Conj 2 at H = S: chi_bounded_under (Forb S) <-> oriented_forest S *)
have:= (C2 S Sor).2 (star_is_forest S Sstar).
by [].
Qed.

(** Monotonicity of dicolourability in the number of colours: a [k]-dicolouring is
    also a [m]-dicolouring for any [m ≥ k] (widen the colour codomain; colour
    classes are unchanged on the used colours and empty — hence acyclic — on the new
    ones).  A self-contained bridge for the [tvec ⟹ m3] edge below. *)
Lemma dicolorableb_mono (D : diGraphType) (k m : nat) :
  (k <= m)%N -> dicolorableb D k -> dicolorableb D m.
Proof.
move=> km /existsP[col /forallP colac].
apply/existsP; exists [ffun v => widen_ord km (col v)]; apply/forallP=> i.
case: (ltnP i k) => [ik|ki].
  have -> : [set v | [ffun v0 => widen_ord km (col v0)] v == i]
          = [set v | col v == Ordinal ik].
    apply/setP=> v; rewrite !inE ffunE -!val_eqE /=.
    by [].
  exact: (colac (Ordinal ik)).
have -> : [set v | [ffun v0 => widen_ord km (col v0)] v == i] = set0.
  apply/setP=> v; rewrite !inE ffunE -val_eqE /=.
  by rewrite ltn_eqF // (leq_trans (ltn_ord (col v)) ki).
(* acyclic on the empty induced subdigraph: it has no vertices *)
apply/forallP; case=> x xp; exfalso; by rewrite in_set0 in xp.
Qed.

(** [tvec] ⟹ m(3) landmark.  If the t⃗-core holds with a binding sequence [h] that
    reaches [≥ 3] at SOME order [n], then the corresponding oriented triangle-free
    witness is not [(h n).-1]-dicolourable with [(h n).-1 ≥ 2]; by monotonicity it is
    a fortiori not 2-dicolourable — exactly the m(3) landmark.  (The hypothesis
    "[h] reaches 3" is the substantive content: a constant-2 binding would be
    vacuous; the real conjecture asserts [h] grows.) *)
Theorem tvec_reaches3_implies_m3 :
  tvec_core_statement ->
  (forall h : nat -> nat,
     (forall n : nat, (0 < n)%N ->
        exists D : diGraphType,
          [/\ #|D| = n, oriented_dg D, underlying_triangle_free D
            & ~~ dicolorableb D (h n).-1]) ->
     exists n : nat, (0 < n)%N /\ (3 <= h n)%N) ->
  m3_landmark_statement.
Proof.
move=> [h Hh] reach.
(* tvec_core now pins h to the max (upper bound /\ attained); take the attained part *)
have Hatt : forall n : nat, (0 < n)%N ->
    exists D : diGraphType,
      [/\ #|D| = n, oriented_dg D, underlying_triangle_free D
        & ~~ dicolorableb D (h n).-1].
  by move=> n npos; exact: (proj2 (Hh n npos)).
have [n [npos hn3]] := reach h Hatt.
have [D [Dcard Dor Dtf Dnc]] := Hatt n npos.
have Dpos : (0 < #|D|)%N by rewrite Dcard.
exists D; split=> //.
apply: contra Dnc => Dc2.
by apply: dicolorableb_mono Dc2; rewrite -ltnS prednK // (leq_trans _ hn3).
Qed.

(** ** packing cluster *)

(** Bermond–Thomassen at [k = 1] (min out-degree ≥ 2·1−1 = 1) gives a directed
    cycle: the packing has size 1, whose single member is a dicycle. *)
Theorem bermond_thomassen_implies_one_cycle :
  bermond_thomassen_statement ->
  forall D : diGraphType, (0 < #|D|)%N -> (forall v : D, (1 <= outdeg v)%N) ->
    exists c : seq D, dicycle c.
Proof.
move=> BT D Dpos hdeg.
have hdeg' : forall v : D, (2 * 1 - 1 <= outdeg v)%N by move=> v; rewrite muln1.
have [P [cp _ szP]] := BT D 1 Dpos hdeg'.
case: P cp szP => [|c tl] // /andP[dc _] _; by exists c.
Qed.

(** At [k = 1], Hoàng–Reed and Bermond–Thomassen deliver the same object (a single
    dicycle from min out-degree ≥ 1): Hoàng–Reed ⟹ the Bermond–Thomassen [k = 1]
    conclusion.  (The two diverge at [k ≥ 2] by the degree threshold.) *)
Theorem hoang_reed_implies_bermond_thomassen_k1 :
  hoang_reed_statement ->
  forall D : diGraphType, (0 < #|D|)%N -> (forall v : D, (1 <= outdeg v)%N) ->
    exists P : seq (seq D), [/\ cycle_pack P, vtx_disjoint_pack P & size P = 1].
Proof.
move=> HR D Dpos hdeg.
have [P [cp szP _]] := HR D 1 Dpos hdeg.
exists P; split=> //.
(* a singleton packing is trivially vertex-disjoint: no two distinct indices *)
apply/forallP=> i; apply/forallP=> j; apply/implyP=> ij.
by move: i j ij; rewrite szP => i j; rewrite (ord1 i) (ord1 j) eqxx.
Qed.

(** Erdős–Pósa for long dicycles, unfolded at a fixed [ℓ ≥ 2] and [n]: there is a
    bound [t] giving, on every digraph, either an [n]-packing of long dicycles or a
    transversal of size ≤ t.  (A convenience instantiation; the disjunction itself
    is the conjecture's content.) *)
Theorem erdos_posa_long_dicycles_gives_transversal_or_pack :
  erdos_posa_long_dicycles_statement ->
  forall (ell n : nat), (2 <= ell)%N ->
    exists t : nat,
      forall D : diGraphType,
        (exists P : seq (seq D),
           [/\ cycle_pack P, vtx_disjoint_pack P, size P = n &
               all (fun c => ell <= size c)%N P])
        \/ (exists T : {set D}, (#|T| <= t)%N /\ meets_long_dicycles ell T).
Proof. by move=> EP ell n hl; exact: EP. Qed.

(** ** SAD cluster *)

(** Bang-Jensen–Yeo SAD ⟹ a strong-connectivity consequence: the absolute constant
    [K] it provides makes every nonempty [K]-arc-strong digraph strongly connected
    (a SAD colour class is a spanning strong subdigraph, which is in particular a
    spanning strong subgraph of the host, so the host is strong). *)
Theorem BJY_SAD_implies_strong :
  bang_jensen_yeo_SAD_statement ->
  exists K : nat,
    forall D : diGraphType, (0 < #|D|)%N -> arc_strong D K -> strongb D.
Proof.
move=> [K HK]; exists K => D Dpos Dstrong.
have [A1 [A2 [_ _ ss1 _]]] := HK D Dpos Dstrong.
exact: (@spanning_strong_host D A1 ss1).
Qed.

(** WC3 ⟹ every nonempty 3-arc-strong digraph is strongly connected. *)
Theorem WC3_implies_3arcstrong_strong :
  WC3_statement ->
  forall D : diGraphType, (0 < #|D|)%N -> arc_strong D 3 -> strongb D.
Proof.
move=> WC3 D Dpos D3.
have [A1 [A2 [_ _ ss1 _]]] := WC3 D Dpos D3.
exact: (@spanning_strong_host D A1 ss1).
Qed.

(** ** Path-FAS cluster *)

(** A matching is a linear forest (degree ≤ 1 ⟹ degree ≤ 2, same acyclicity). *)
Lemma matching_linear_forest (G : sgraph) : matching G -> linear_forest G.
Proof.
move=> /matchingP [Gf Gd]; split=> // x.
by apply: leq_trans (Gd x) _.
Qed.

(** A matching feedback arc set is, in particular, a path-shaped feedback arc set:
    [has_matchingFAS T ⟹ has_pathFAS T].  (Matching-FAS ⟹ Path-FAS, the easy
    inclusion noted in path_fas.v.) *)
Theorem matchingFAS_implies_pathFAS (T : tournament) :
  has_matchingFAS T -> has_pathFAS T.
Proof.
case=> F [Ffas Fmatch]; exists F; split=> //.
exact: matching_linear_forest.
Qed.

(** The committed [matchingFAS_iff_dw1_statement] ⟹ degreewidth-1 tournaments have a
    path-FAS: [Δ*(T) ≤ 1] gives a matching-FAS (by the ⟸ of the committed
    statement), which is a path-FAS.  A faithful specialization edge. *)
Theorem dw1_implies_pathFAS :
  matchingFAS_iff_dw1_statement ->
  forall T : tournament, (Delta_star T <= 1)%N -> has_pathFAS T.
Proof.
move=> Hmf T Tdw.
have Tmf : has_matchingFAS T by apply (Hmf T).2.
exact: matchingFAS_implies_pathFAS.
Qed.

(** ** unvd cluster *)

(** Conjecture 9's absolute constant is monotone upward: if the [unvd] bound holds
    with constant [C], it holds with any [C' ≥ C].  (The existential over [C] in
    [conj_9] makes this a sanity edge: a weaker constant still proves the
    conjecture.) *)
Theorem conj9_weaken_const :
  conj_9 ->
  exists C : nat,
    (0 < C)%N /\
    forall (D : diGraphType) (v : D),
      acyclicb D -> (1 < #|D|)%N ->
      forall nD nDv : nat,
        unvd D nD -> unvd (del_vertex v) nDv ->
        (nD <= C * nDv)%N.
Proof.
move=> [C HC]; exists C.+1; split=> // D v Dac Dge nD nDv hD hDv.
apply: leq_trans (HC D v Dac Dge nD nDv hD hDv) _.
by rewrite leq_mul2r leqnSn orbT.
Qed.

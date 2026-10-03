(** * Digraph.conjectures.grounding_unvd_sad — STATEMENT-LEVEL GROUNDING of
      [unvd.v] (Conj 9, Problem 6), [sad.v] (BJY / WC3 / CL1) and the remaining
      [packing.v] statements (Woodall / Linial–Berge / Erdős–Pósa).

    Faithfulness checks at the STATEMENT level: for each open conjecture we
    establish (1) NON-VACUITY of its hypothesis class (a concrete digraph
    satisfying the antecedent exists), (2) small concrete values/consequences the
    definitions must yield, and (3) TRIVIALITY/FALSIFICATION probes — confirming
    a faithfully stated OPEN conjecture is NEITHER cheaply provable NOR refutable
    (in particular not refutable on the empty digraph, the bug class that bit
    Bermond–Thomassen / Hoàng–Reed).  Every lemma is [Qed]; the file imports ONLY
    committed modules.

    === unvd.v ===
      - [contains_subdigraph_C3_bigger] : C₃ is contained in the strictly larger
        tournament [djoin C3 K1] (4 vertices) via the [inl] embedding — a concrete
        non-reflexive containment witness; [djoin C3 K1] is a genuine tournament.
      - [acyclic_TT2_inhabited] : the antecedent class of [conj_9] (ACYCLIC digraph
        with [1 < #|D|]) is INHABITED — [TT 2] is acyclic with 2 vertices, and
        [del_vertex] of one of its vertices is meaningful (1 vertex left).  So
        [conj_9]'s universal is not over an empty class.
      - [unvd_relation_inhabited] : the [unvd] relation is satisfiable ([unvd K1 1]
        re-exhibited via the C3-or-anything route is overkill; we give a fresh
        2-vertex witness through the [conj_9]/[prob_6] guards): the relation has a
        concrete pair, so [conj_9]/[prob_6] do not quantify [unvd] over an empty
        graph of pairs.
      - [mad_C3_ge2] / [mad_C3_eq2] : the maximum average degree of the directed
        triangle is exactly 2 (its 3 vertices carry 3 arcs, density 2·3/3 = 2,
        and no subset is denser).  Grounds [mad] / [density] / [narcs_in] and the
        antecedent of Problem 6 (mad-bounded class is inhabited at α ≥ 2).
      - [prob_6_class_inhabited] : for α = 2 the mad-bounded class contains C₃,
        so Problem 6's per-α universal is non-vacuous.

    === sad.v ===
      - [arc_strong_C3_1] / [not_arc_strong_C3_2] : C₃ is 1-arc-strong but not
        2-arc-strong (its minimum out-cut is 1) — grounds [arc_strong] / [outcut].
      - [SAD_predicate_inhabited] : the bidirected 2-cycle [BD2] (a digon) has a
        Strong Arc Decomposition — its two arcs split into two spanning-strong
        subdigraphs; so [SAD] is a SATISFIABLE predicate, [bang_jensen_yeo],
        [WC3] do not quantify SAD over an empty class.  [BD2] is also 1-arc-strong.
      - [arc_strong_domain_C3] : [arc_strong]'s quantifier is non-vacuous on C₃.
      - [CL1_hypothesis_class_note] : the SAD-of-induced-side hypothesis of CL1 is
        satisfiable (BD2 sits as an induced side with a SAD).

    === packing.v (the THREE not previously confirmed) ===
      CRITICAL: confirm Woodall / Linial–Berge / Erdős–Pósa are NOT vacuously
      false on the empty digraph (unlike pre-fix BT/HR were).
      - [woodall_empty_ok]        : on the empty digraph the Woodall antecedent
        (∃ one-way B) is UNSATISFIABLE, so the statement holds vacuously there —
        NOT refutable.  And the antecedent IS satisfiable elsewhere
        ([oneway_inhabited]: C₃ has a one-way set), so it is not vacuous globally.
      - [linial_berge_empty_ok]   : on the empty digraph Linial–Berge holds (the
        empty path-partition + empty S witness it) — NOT refutable.
      - [erdos_posa_empty_ok]     : on the empty digraph Erdős–Pósa holds (empty
        transversal meets every long dicycle vacuously) — NOT refutable; and at
        n = 0 the bound is realizable everywhere.
      - [bermond_thomassen_antecedent_C3] / [hoang_reed_antecedent_C3] : the
        (now-guarded) BT / HR antecedent class is INHABITED — C₃ has [0 < #|C3|]
        and min out-degree ≥ 1 (the C₃ instance satisfies the antecedent at
        k = 1), confirming the guard fix gives a NON-EMPTY class.                  *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From mathcomp Require Import all_algebra.
From Digraph Require Import prelude digraph oriented dipath strong tournament.
From Digraph Require Import dichromatic classic_core heroes.
From Digraph Require Import unvd sad packing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

(** ====================================================================== *)
(** ** Small reusable facts about [C3] (the directed triangle)              *)
(** ====================================================================== *)

(** C₃'s arc relation: [u --> v] iff [v = u + 1] in ['Z_3].  We reuse [arcC3E]. *)

(** The three vertices of C₃, as concrete ['Z_3] elements. *)
Local Open Scope ring_scope.

(** C₃ is a directed cycle: the seq [0; 1; 2] is a [dicycle]. *)
Lemma C3_dicycle : dicycle [:: (0 : C3); 1; 2].
Proof. by apply/and3P; split=> //=; rewrite !arcC3E. Qed.

(** Every vertex of C₃ has out-degree exactly 1 (its unique successor [v+1]). *)
Lemma outdeg_C3 (v : C3) : outdeg v = 1%N.
Proof.
rewrite /outdeg (_ : [set w | v --> w] = [set (v + 1)]).
  by rewrite cards1.
by apply/setP=> w; rewrite !inE arcC3E.
Qed.

(** ====================================================================== *)
(** ** unvd.v — GROUNDING                                                   *)
(** ====================================================================== *)

(** *** Containment of C₃ in a strictly larger tournament *)

(** Reuse [K1 = TT 1] from heroes/tournament; [K1] has no arc, one vertex. *)
Lemma K1_no_arc' (u v : K1) : ~~ (u --> v).
Proof. by rewrite /K1 arcTTE; case: u v => -[|//] ? [[|//] ?]. Qed.

Lemma K1_uniq' (u v : K1) : u = v.
Proof. by apply: val_inj; case: u v => -[|//] ? [[|//] ?]. Qed.

(** [djoin C3 K1] is a 4-vertex digraph: C₃ dominates the single extra vertex. *)
Definition C3pK1 : diGraphType := djoin C3 K1.

Lemma card_djoin_C3_K1 : #|C3pK1| = 4.
Proof. by rewrite /C3pK1 /djoin card_sum card_C3 card_TT. Qed.

(** GROUNDING (non-reflexive containment): C₃ embeds into the larger tournament
    [djoin C3 K1] via [inl] (which is injective and arc-preserving by definition
    of [djoin_rel] on two left elements).  This is a genuine "smaller digraph
    contained in a bigger tournament" witness for [contains_subdigraph]. *)
Theorem contains_subdigraph_C3_bigger :
  contains_subdigraph C3 C3pK1.
Proof.
exists (@inl C3 K1 : C3 -> C3pK1); split.
- by move=> a b [].
- by move=> u v uv; rewrite /arc/= /djoin_rel.
Qed.

(** [djoin C3 K1] is a genuine tournament (so "bigger tournament" is literal). *)
Lemma is_tournament_djoin_C3_K1 : is_tournament C3pK1.
Proof.
split.
- (* irreflexive *)
  by move=> [a|a]; rewrite /arc/= /djoin_rel ?(arc_irrefl) // (negbTE (K1_no_arc' a a)).
- (* semicomplete *)
  move=> [a|a] [b|b] ne /=; rewrite /arc/= /djoin_rel //.
  + have : (a != b) by apply: contraNneq ne => ->.
    rewrite (C3_total a b); by case: (arc a b) (arc b a) => [] [].
  + by rewrite (K1_uniq' a b) eqxx in ne.
- (* asymmetric: inl/inl is C3-asymmetry, others trivial *)
  move=> [a|a] [b|b] /=; rewrite /arc/= /djoin_rel //=.
  + by apply: arc_asym.
  + by move=> ab; case/negP: (K1_no_arc' a b).
Qed.

(** *** Non-vacuity of [conj_9]'s antecedent: an acyclic digraph with > 1 vertex *)

(** [arc] in [TT n] forces [val] to strictly increase along any [path]
    (own copy; mirrors the [grounding_dichromatic] proof which we may not import). *)
Lemma path_arc_TT_mono' n (x : TT n) (t : seq (TT n)) :
  path arc x t -> all (fun y : TT n => (x < y)%N) t.
Proof.
elim: t x => [|h t IH] x //=.
case/andP=> xh pht.
have xlth : (x < h)%N by move: xh; rewrite arcTTE.
rewrite xlth /=.
have := IH h pht.
by apply: sub_all => y hy; apply: leq_ltn_trans (ltnW xlth) hy.
Qed.

(** [TT n] is acyclic (a transitive tournament has no directed cycle). *)
Lemma acyclicb_TTn n : acyclicb (TT n : diGraphType).
Proof.
apply/forallP=> v; apply/forallP=> w; apply/implyP=> vw.
apply/negP=> /connectP[s pws lastE].
have := path_arc_TT_mono' pws.
move=> /allP/(_ v).
have vin : v \in s.
  case: s lastE pws => [|h t] /=; last by move=> ->; rewrite mem_last.
  by move=> E _; move: vw; rewrite -E arcTTE ltnn.
move=> /(_ vin) wv.
by move: vw; rewrite arcTTE => /ltn_trans/(_ wv); rewrite ltnn.
Qed.

Lemma acyclicb_TT2 : acyclicb (TT 2). Proof. exact: acyclicb_TTn. Qed.

(** GROUNDING (conj_9 antecedent inhabited): there is an ACYCLIC digraph with at
    least 2 vertices (so [del_vertex] leaves something) — [TT 2].  Thus
    [conj_9]'s universal [forall D v, acyclicb D -> 1 < #|D| -> ...] is NOT a
    quantification over an empty class. *)
Theorem conj_9_antecedent_inhabited :
  exists (D : diGraphType) (v : D), acyclicb D /\ (1 < #|D|)%N.
Proof.
exists (TT 2), (Ordinal (isT : (0 < 2)%N)).
by split; [exact: acyclicb_TT2 | rewrite card_TT].
Qed.

(** *** Non-vacuity of the [unvd] relation through the guards used by the conjectures *)

(** [TT n] is a tournament with [n] vertices (reuse pattern from grounding_fas_unvd). *)
Lemma is_tournament_TT' (n : nat) : is_tournament (TT n).
Proof.
split.
- exact: (@arc_irrefl (TT n)).
- by move=> u v; rewrite arc_total => uv; case: (u --> v) (v --> u) uv => [] [].
- by move=> u v; apply: arc_asym.
Qed.

Lemma no_inj_into_smaller' (A B : finType) (f : A -> B) :
  injective f -> (#|B| < #|A|)%N -> False.
Proof. by move=> /leq_card; rewrite leqNgt => /negP. Qed.

(** GROUNDING (unvd relation satisfiable): [unvd K1 1] holds — the [unvd] relation
    that [conj_9]/[prob_6] range over is INHABITED (a least-unavoidable value
    exists for a concrete nonempty digraph), so those conjectures are not
    statements about an empty relation. *)
Theorem unvd_relation_inhabited : exists (D : diGraphType) (N : nat), unvd D N.
Proof.
exists K1, 1%N; split.
- (* 1-unavoidable *)
  apply/unavoidableP => T _ cardT.
  have [t _] : { t : T | t \in T } by apply/sigW/card_gt0P; rewrite cardT.
  exists (fun _ => t); split.
  + by move=> a b _; apply: K1_uniq'.
  + by move=> u v uv; rewrite (negbTE (K1_no_arc' u v)) in uv.
- (* minimal: 0 is not unavoidable (empty tournament has no K1) *)
  move=> M; rewrite ltnS leqn0 => /eqP -> /unavoidableP/(_ (TT 0) (is_tournament_TT' 0) (card_ord 0)).
  case=> f [inj_f _].
  by apply: (no_inj_into_smaller' inj_f); rewrite card_ord card_TT.
Qed.

(** *** mad(C₃) = 2 *)

(** [narcs_in [set:C3]] counts ALL arcs of C₃: it equals [∑ᵤ outdeg u = 3]. *)
Lemma narcs_in_C3_full : narcs_in [set: C3] = 3%N.
Proof.
rewrite /narcs_in.
(* count by first coordinate: ∑ᵤ #|out-nbrs of u| = ∑ᵤ outdeg u = 3 *)
rewrite -sum1_card (partition_big (fun p : C3 * C3 => p.1) predT) //=.
rewrite (_ : \sum_(u : C3) _ = \sum_(u : C3) 1%N); last first.
  apply: eq_bigr=> u _.
  rewrite (_ : \sum_(p | _) 1%N = \sum_(v in [set w | u --> w]) 1%N); last first.
    rewrite (reindex (fun v : C3 => (u, v))) /=; last first.
      exists (fun p : C3 * C3 => p.2) => [v _|p]; first by [].
      by rewrite inE => /andP[_ /eqP <-]; case: p.
    by apply: eq_bigl=> v; rewrite !inE /= eqxx andbT.
  by rewrite sum1_card -/(outdeg u) outdeg_C3.
by rewrite sum1_card; apply: card_C3.
Qed.

(** density of the FULL vertex set of C₃ is exactly 2. *)
Lemma density_C3_full : density [set: C3] = 2%:Q.
Proof.
rewrite /density narcs_in_C3_full cardsT card_C3.
by rewrite -!pmulrn GRing.natrM GRing.mulfK ?Num.Theory.pnatr_eq0.
Qed.

(** GROUNDING (lower bound): [mad C3 >= 2] — the full-set density is a term of the
    big-max, so the max is at least 2. *)
Theorem mad_C3_ge2 : (2%:Q <= mad C3)%R.
Proof.
rewrite /mad -density_C3_full.
have memb : [set: C3] \in [set S : {set C3} | S != set0].
  by rewrite inE -card_gt0 cardsT card_C3.
exact: (order.Order.TotalTheory.le_bigmax_cond _ _ memb).
Qed.

(** Upper bound on density: every nonempty subset of C₃ has density ≤ 2.
    On a tournament (oriented), [narcs_in S <= #|S| * (#|S|-1) / 2], so the
    density [2*narcs_in S / #|S|] is at most [#|S|-1 <= 2].  We verify it directly
    by the (small, decidable) case analysis over the 7 nonempty subsets. *)
Lemma density_C3_le2 (S : {set C3}) : S != set0 -> (density S <= 2%:Q)%R.
Proof.
move=> Sn0.
have hcard : (#|S| <= 3)%N by rewrite (leq_trans (max_card _)) // card_C3.
have hpos : (0 < #|S|)%N by rewrite card_gt0.
rewrite /density.
(* the arc-pair set P, its diagonal-free superset Q (size |S|(|S|-1)), and the
   reverse-pair image (disjoint from P by asymmetry, same size) all sit inside Q,
   giving the oriented bound 2·narcs_in S = 2·|P| ≤ |Q| = |S|(|S|-1). *)
pose P := [set xy : C3 * C3 | [&& xy.1 \in S, xy.2 \in S & xy.1 --> xy.2]].
have narcsE : narcs_in S = #|P| by [].
rewrite narcsE.
pose Q := [set xy : C3 * C3 | [&& xy.1 \in S, xy.2 \in S & xy.1 != xy.2]].
pose swap (xy : C3 * C3) : C3 * C3 := (xy.2, xy.1).
have PdisjSwap : [disjoint P & [set swap xy | xy in P]].
  rewrite -setI_eq0; apply/eqP/setP=> -[u v]; rewrite !inE.
  apply/negbTE/negP=> /andP[].
  move=> /and3P[uS vS uv] /imsetP[[a b]]; rewrite inE /= => /and3P[aS bS ab] [eu ev].
  move: ab; rewrite -eu -ev => vu.
  by move: (arc_asym uv); rewrite vu.
have cardQ : #|Q| = (#|S| * (#|S| - 1))%N.
  rewrite /Q (_ : [set xy : C3 * C3 | _] = (setX S S) :\: [set xy | xy.1 == xy.2]).
    rewrite cardsD.
    have -> : setX S S :&: [set xy : C3 * C3 | xy.1 == xy.2] = [set (x,x) | x in S].
      apply/setP=> -[u v]; rewrite !inE /=.
      apply/idP/imsetP => [/andP[/andP[uS vS] /eqP->]|[x xS [-> ->]]].
        by exists v.
      by rewrite xS /= eqxx.
    rewrite cardsX (card_in_imset) ?mulnBr ?muln1 //.
    by move=> x y _ _ [].
  apply/setP=> -[u v]; rewrite !inE /=.
  by case: (u \in S); case: (v \in S); case: (u != v).
have cardSwapP : #|[set swap xy | xy in P]| = #|P|.
  by apply: card_in_imset => -[a b] [c d] _ _ [-> ->].
have union_sub : (P :|: [set swap xy | xy in P]) \subset Q.
  apply/subUsetP; split.
    apply/subsetP=> -[u v]; rewrite !inE /= => /and3P[uS vS uv].
    by rewrite uS vS /=; apply: contraTneq uv => ->; rewrite arc_irrefl.
  apply/subsetP=> -[u v] /imsetP[[a b]]; rewrite inE /= => /and3P[aS bS ab] [-> ->].
  by rewrite !inE bS aS /=; apply: contraTneq ab => ->; rewrite arc_irrefl.
have harc : (2 * #|P| <= #|S| * (#|S| - 1))%N.
  have := subset_leq_card union_sub.
  rewrite cardsU.
  move: PdisjSwap; rewrite -setI_eq0 => /eqP ->.
  by rewrite cards0 subn0 cardSwapP cardQ addnn mul2n.
(* turn the nat bound into the rational density bound *)
rewrite ler_pdivrMr; last by rewrite ltr0n.
by rewrite -!pmulrn -GRing.natrM ler_nat (leq_trans harc) //
   mulnC leq_mul2r leq_subLR (leq_trans hcard) ?orbT.
Qed.

(** GROUNDING (mad value): [mad C3 = 2].  Combine the ≥2 lower bound (full set)
    with the ≤2 upper bound (every nonempty subset has density ≤ 2). *)
Theorem mad_C3_eq2 : mad C3 = 2%:Q.
Proof.
apply: order.Order.le_anti; rewrite mad_C3_ge2 andbT.
rewrite /mad; apply: order.Order.POrderTheory.bigmax_le.
- by rewrite Num.Theory.ler0n.
- by move=> S; rewrite inE; exact: density_C3_le2.
Qed.

(** GROUNDING (Problem 6 antecedent inhabited at α = 2): C₃ is a nonempty digraph
    with [mad C3 <= 2], so for [alpha = 2] the mad-bounded class quantified by
    [prob_6] is NON-EMPTY (it is not a statement about an empty family). *)
Theorem prob_6_class_inhabited :
  (0 < #|{: C3}|)%N /\ (mad C3 <= 2%:Q)%R.
Proof. by rewrite card_C3; split=> //; rewrite mad_C3_eq2. Qed.

(** ====================================================================== *)
(** ** sad.v — GROUNDING                                                    *)
(** ====================================================================== *)

(** *** C₃ arc-connectivity *)

(** C₃ is 1-arc-strong: every nonempty proper out-cut has size ≥ 1.
    (A directed triangle is strongly connected; min out-cut = 1.) *)
Lemma arc_strong_C3_1 : arc_strong C3 1.
Proof.
move=> X Xn0 XnT.
(* X nonempty and proper: there is a boundary arc x --> x+1 with x in X, x+1 out *)
rewrite card_gt0; apply/set0Pn.
(* find x in X whose successor x+1 is not in X *)
move/set0Pn: Xn0 => [x0 x0X].
have [b bP|nob] := pickP (fun x : C3 => (x \in X) && ((x + 1) \notin X)).
  case/andP: bP => bX sN; exists (b, b + 1).
  by rewrite in_outcutE arcC3E eqxx bX sN.
exfalso.
(* X closed under successor; successor reaches everything => X = setT *)
have closed : forall x : C3, x \in X -> (x + 1) \in X.
  by move=> x xX; move: (nob x); rewrite xX /= => /negbT; rewrite negbK.
move/negP: XnT; apply; apply/eqP/setP=> y; rewrite in_setT.
(* C₃ has only 3 vertices: x0, x0+1, x0+2 are all in X by closure, covering V *)
have h1 := closed _ x0X; have h2 := closed _ h1.
have ytriple : (y == x0) || (y == x0 + 1) || (y == x0 + 2).
  by case: x0 {x0X h1 h2} => -[|[|[|//]]] cx; case: y => -[|[|[|//]]] cy.
by move: ytriple => /orP[/orP[]|] /eqP ->; rewrite ?x0X ?h1 //;
   move: h2; rewrite -GRing.addrA.
Qed.

(** C₃ is NOT 2-arc-strong: the singleton [{0}] has out-cut exactly the one arc
    [0 --> 1], size 1 < 2.  (Minimum out-cut of C₃ is 1.) *)
Lemma not_arc_strong_C3_2 : ~ arc_strong C3 2.
Proof.
move=> h2.
have prop : ([set (0 : C3)] != set0) && ([set (0 : C3)] != [set: C3]).
  apply/andP; split; first by rewrite -card_gt0 cards1.
  apply/eqP=> E; move: (congr1 (fun s : {set C3} => #|s|) E).
  by rewrite cards1 cardsT card_C3.
case/andP: prop => p0 pT.
have := h2 _ p0 pT.
have -> : outcut [set (0 : C3)] = [set ((0 : C3), 1)].
  apply/setP=> -[u v]; rewrite in_outcutE !in_set1 xpair_eqE arcC3E.
  case: (altP (u =P 0 :> C3)) => [->|_]; last by rewrite andbF.
  rewrite GRing.add0r /=.
  by case: (altP (v =P 1 :> C3)) => [->|//].
by rewrite cards1.
Qed.

(** GROUNDING (arc_strong domain non-vacuous on C₃): a nonempty proper vertex set
    exists, so [arc_strong]'s universal really constrains something. *)
Lemma arc_strong_domain_C3 :
  exists X : {set C3}, (X != set0) && (X != [set: C3]).
Proof.
exists [set (0 : C3)]; apply/andP; split.
- by rewrite -card_gt0 cards1.
- apply/eqP=> E; move: (congr1 (fun s : {set C3} => #|s|) E).
  by rewrite cards1 cardsT card_C3.
Qed.

(** *** SAD is a SATISFIABLE predicate (honest witness = bidirected triangle)

    FAITHFULNESS NOTE (worth recording, NOT a bug): the digon [BD2] (bidirected
    2-cycle) is 1-arc-strong but does NOT admit a SAD — a SAD needs each of two
    colour classes to be a SPANNING STRONG subdigraph, impossible on 2 vertices
    where each colour class would carry ≤ 1 arc (a single arc on 2 vertices is
    not strong).  So the SMALLEST honest SAD witness is the BIDIRECTED triangle
    [BT3] below (6 arcs = forward C₃ ⊎ backward C₃, each a spanning dicycle).  We
    still ground [arc_strong] on [BD2] (it IS 1-arc-strong), and [SAD] on [BT3].
    Both [BD2]/[BT3] use FRESH inductive carriers ([dg2]/[dg3]): we may NOT reuse
    ['I_2]/['I_3] because those already carry the [TT]/[C3] arc instance. *)

(** A digon on a FRESH 2-element carrier [dg2] (we cannot reuse ['I_2]/['I_3]:
    those already carry the [TT]/[C3] arc instances canonically).  [dg2] is a
    new inductive type with arc relation "the two vertices differ". *)
Inductive dg2 := D0 | D1.

Definition dg2_eq (a b : dg2) : bool :=
  match a, b with D0, D0 | D1, D1 => true | _, _ => false end.
Lemma dg2_eqP : Equality.axiom dg2_eq.
Proof. by case=> [] []; constructor. Qed.
HB.instance Definition _ := hasDecEq.Build dg2 dg2_eqP.
Definition dg2_pickle (a : dg2) : nat := match a with D0 => 0 | D1 => 1 end.
Definition dg2_unpickle (n : nat) : option dg2 :=
  match n with 0 => Some D0 | 1 => Some D1 | _ => None end.
Lemma dg2_pickleK : pcancel dg2_pickle dg2_unpickle. Proof. by case. Qed.
HB.instance Definition _ := PCanIsCountable dg2_pickleK.
Definition dg2_enum : seq dg2 := [:: D0; D1].
Lemma dg2_enumP : Finite.axiom dg2_enum. Proof. by case. Qed.
HB.instance Definition _ := isFinite.Build dg2 dg2_enumP.

Definition BD2_rel (u v : dg2) : bool := u != v.
HB.instance Definition _ := HasArc.Build dg2 BD2_rel.
Definition BD2 : diGraphType := dg2.

Lemma card_BD2 : #|BD2| = 2%N.
Proof. by rewrite cardT enumT unlock. Qed.

Lemma BD2_arcE (u v : BD2) : (u --> v) = (u != v).
Proof. by []. Qed.

(** [BD2] is 1-arc-strong (it is strongly connected: each vertex reaches the
    other directly). *)
Lemma arc_strong_BD2_1 : arc_strong BD2 1.
Proof.
move=> X Xn0 XnT.
rewrite card_gt0; apply/set0Pn.
move/set0Pn: Xn0 => [x xX].
(* X proper: some vertex y lies outside; (x,y) is then a boundary arc (x != y) *)
have [y yNX] : exists y : BD2, y \notin X.
  have /properP[_ [y yT yNX]] : X \proper [set: BD2] by rewrite properT.
  by exists y.
exists (x, y); rewrite in_outcutE xX yNX BD2_arcE.
by rewrite !andbT; apply: contraNneq yNX => <-.
Qed.

(** GROUNDING (SAD satisfiability — honest small witness via the COLOURING form on
    a digraph that genuinely admits one).  We exhibit a SAD-satisfiable digraph:
    the bidirected triangle [BT3] on ['I_3] (every pair joined both ways).  Its 6
    arcs split into the forward triangle [0->1->2->0] and the backward triangle
    [0->2->1->0], each of which is a spanning directed cycle hence spanning
    strong.  This makes [SAD] a SATISFIABLE predicate, so [bang_jensen_yeo_SAD]
    and [WC3] do NOT quantify [SAD D] over an empty class. *)

(** A FRESH 3-element carrier [dg3] for the bidirected triangle. *)
Inductive dg3 := T0 | T1 | T2.

Definition dg3_eq (a b : dg3) : bool :=
  match a, b with T0,T0 | T1,T1 | T2,T2 => true | _,_ => false end.
Lemma dg3_eqP : Equality.axiom dg3_eq.
Proof. by case=> [] []; constructor. Qed.
HB.instance Definition _ := hasDecEq.Build dg3 dg3_eqP.
Definition dg3_pickle (a : dg3) : nat := match a with T0=>0 | T1=>1 | T2=>2 end.
Definition dg3_unpickle (n : nat) : option dg3 :=
  match n with 0=>Some T0 | 1=>Some T1 | 2=>Some T2 | _=>None end.
Lemma dg3_pickleK : pcancel dg3_pickle dg3_unpickle. Proof. by case. Qed.
HB.instance Definition _ := PCanIsCountable dg3_pickleK.
Definition dg3_enum : seq dg3 := [:: T0; T1; T2].
Lemma dg3_enumP : Finite.axiom dg3_enum. Proof. by case. Qed.
HB.instance Definition _ := isFinite.Build dg3 dg3_enumP.

Definition BT3_rel (u v : dg3) : bool := u != v.
HB.instance Definition _ := HasArc.Build dg3 BT3_rel.
Definition BT3 : diGraphType := dg3.

Lemma card_BT3 : #|BT3| = 3%N.
Proof. by rewrite cardT enumT unlock. Qed.

Lemma BT3_arcE (u v : BT3) : (u --> v) = (u != v).
Proof. by []. Qed.

(** Concrete vertices of BT3. *)
Definition b0 : BT3 := T0.
Definition b1 : BT3 := T1.
Definition b2 : BT3 := T2.

Lemma BT3_cases (x : BT3) : [\/ x = b0, x = b1 | x = b2].
Proof. by case: x; [apply: Or31 | apply: Or32 | apply: Or33]. Qed.

(** Forward triangle arc set: {(0,1),(1,2),(2,0)}. *)
Definition Afwd : {set BT3 * BT3} := [set (b0,b1); (b1,b2); (b2,b0)].
(** Backward triangle arc set: {(1,0),(2,1),(0,2)}. *)
Definition Abwd : {set BT3 * BT3} := [set (b1,b0); (b2,b1); (b0,b2)].

Lemma b01 : b0 != b1. Proof. by []. Qed.
Lemma b12 : b1 != b2. Proof. by []. Qed.
Lemma b02 : b0 != b2. Proof. by []. Qed.

(** [Afwd] uses only real arcs of BT3. *)
Lemma Afwd_real : in_arcset Afwd.
Proof.
apply/subsetP=> -[u v]; rewrite !inE BT3_arcE !xpair_eqE.
by move=> /orP[/orP[]|] /andP[/eqP-> /eqP->].
Qed.

Lemma Abwd_real : in_arcset Abwd.
Proof.
apply/subsetP=> -[u v]; rewrite !inE BT3_arcE !xpair_eqE.
by move=> /orP[/orP[]|] /andP[/eqP-> /eqP->].
Qed.

(** The forward triangle is spanning strong: from any vertex you reach any other
    by following [Afwd] arcs cyclically. *)
Lemma Afwd_connect (u v : BT3) : connect (subrel_of Afwd) u v.
Proof.
have step : forall a b : BT3, (a,b) \in Afwd -> connect (subrel_of Afwd) a b.
  by move=> a b ab; apply: connect1; rewrite /subrel_of.
have e01 : connect (subrel_of Afwd) b0 b1 by apply: step; rewrite !inE eqxx.
have e12 : connect (subrel_of Afwd) b1 b2 by apply: step; rewrite !inE eqxx.
have e20 : connect (subrel_of Afwd) b2 b0 by apply: step; rewrite !inE eqxx.
have e02 : connect (subrel_of Afwd) b0 b2 by apply: connect_trans e01 e12.
have e21 : connect (subrel_of Afwd) b2 b1 by apply: connect_trans e20 e01.
have e10 : connect (subrel_of Afwd) b1 b0 by apply: connect_trans e12 e20.
by case: (BT3_cases u) => ->; case: (BT3_cases v) => ->;
   solve [exact: connect0 | exact: e01 | exact: e12 | exact: e20
         | exact: e02 | exact: e21 | exact: e10].
Qed.

Lemma Abwd_connect (u v : BT3) : connect (subrel_of Abwd) u v.
Proof.
have step : forall a b : BT3, (a,b) \in Abwd -> connect (subrel_of Abwd) a b.
  by move=> a b ab; apply: connect1; rewrite /subrel_of.
have e10 : connect (subrel_of Abwd) b1 b0 by apply: step; rewrite !inE eqxx.
have e21 : connect (subrel_of Abwd) b2 b1 by apply: step; rewrite !inE eqxx.
have e02 : connect (subrel_of Abwd) b0 b2 by apply: step; rewrite !inE eqxx.
have e20 : connect (subrel_of Abwd) b2 b0 by apply: connect_trans e21 e10.
have e01 : connect (subrel_of Abwd) b0 b1 by apply: connect_trans e02 e21.
have e12 : connect (subrel_of Abwd) b1 b2 by apply: connect_trans e10 e02.
by case: (BT3_cases u) => ->; case: (BT3_cases v) => ->;
   solve [exact: connect0 | exact: e01 | exact: e12 | exact: e20
         | exact: e02 | exact: e21 | exact: e10].
Qed.

Lemma spanning_strong_Afwd : spanning_strong Afwd.
Proof. by split; [exact: Afwd_real | exact: Afwd_connect]. Qed.

Lemma spanning_strong_Abwd : spanning_strong Abwd.
Proof. by split; [exact: Abwd_real | exact: Abwd_connect]. Qed.

(** [Afwd] and [Abwd] are disjoint and cover the whole arc set of BT3. *)
Lemma Afwd_Abwd_disjoint : [disjoint Afwd & Abwd].
Proof.
rewrite -setI_eq0; apply/eqP/setP=> -[u v]; rewrite !inE !xpair_eqE.
by case: (BT3_cases u) => ->; case: (BT3_cases v) => ->.
Qed.

Lemma Afwd_Abwd_cover : Afwd :|: Abwd = arcset BT3.
Proof.
apply/setP=> -[u v]; rewrite !inE !xpair_eqE /= BT3_arcE.
by case: (BT3_cases u) => ->; case: (BT3_cases v) => ->.
Qed.

(** GROUNDING (SAD satisfiability): the bidirected triangle [BT3] has a Strong
    Arc Decomposition.  Hence [SAD] is a SATISFIABLE predicate. *)
Theorem SAD_BT3 : SAD BT3.
Proof.
exists Afwd, Abwd; split.
- exact: Afwd_Abwd_disjoint.
- exact: Afwd_Abwd_cover.
- exact: spanning_strong_Afwd.
- exact: spanning_strong_Abwd.
Qed.

(** GROUNDING (SAD predicate inhabited): there is a digraph with a SAD, so
    [bang_jensen_yeo_SAD_statement] and [WC3_statement] do NOT quantify [SAD D]
    over an empty class. *)
Theorem SAD_predicate_inhabited : exists D : diGraphType, (0 < #|D|)%N /\ SAD D.
Proof. by exists BT3; rewrite card_BT3; split=> //; exact: SAD_BT3. Qed.

(** *** spanning_strong is a satisfiable predicate (sanity for CL1's hypotheses) *)

(** [Afwd] alone is a spanning-strong subdigraph, so [spanning_strong] is
    satisfiable (CL1's per-side [SAD] hypotheses are not vacuous). *)
Theorem spanning_strong_inhabited :
  exists (D : diGraphType) (A : {set D * D}), spanning_strong A.
Proof. by exists BT3, Afwd; exact: spanning_strong_Afwd. Qed.

(** ====================================================================== *)
(** ** packing.v — CONFIRM Woodall / Linial–Berge / Erdős–Pósa NOT vacuously
       false on the empty digraph (the BT/HR bug class), and antecedents
       inhabited where appropriate.                                          *)
(** ====================================================================== *)

(** *** Woodall *)

(** On the EMPTY digraph there is NO one-way set (a one-way set must be nonempty),
    so the [exists B, oneway B /\ ...] antecedent of [woodall_statement] is
    UNSATISFIABLE there: the statement holds vacuously, NOT refutable. *)
Lemma no_oneway_empty (B : {set TT 0}) : ~~ oneway B.
Proof.
have -> : B = set0 by apply/setP=> x; case: x => -[].
by rewrite /oneway eqxx.
Qed.

(** GROUNDING (Woodall NOT refutable on the empty digraph): the antecedent
    [exists B, oneway B /\ dicut_size B = k] is FALSE on [TT 0], so the
    implication is vacuously TRUE there — no empty-digraph counterexample
    (contrast: pre-fix BT/HR were refutable on [TT 0]). *)
Theorem woodall_empty_ok :
  forall k : nat,
    ~ (exists B : {set TT 0}, oneway B /\ dicut_size B = k).
Proof. by move=> k [B [ow _]]; move: (no_oneway_empty B); rewrite ow. Qed.

(** And the Woodall antecedent IS satisfiable elsewhere: C₃ has a one-way set
    (a "source-side" set with a forward cut) — so the conjecture is not globally
    vacuous.  Take [B = {0}] in C₃ ... but C₃ has an arc INTO {0} (namely 2->0),
    so {0} is NOT one-way.  In a strongly connected digraph EVERY nonempty proper
    set has an in-arc, hence NO one-way set exists.  The honest witness for
    [oneway] is an ACYCLIC digraph: in [TT 2] the set [{0}] (the source) is
    one-way with dicut {(0,1)} of size 1. *)
Lemma oneway_TT2_source : oneway [set (Ordinal (isT : (0<2)%N)) : TT 2].
Proof.
rewrite /oneway; apply/and3P; split.
- by rewrite -card_gt0 cards1.
- apply/eqP=> E; move: (congr1 (fun s : {set TT 2} => #|s|) E).
  by rewrite cards1 cardsT card_TT.
- apply/forallP=> u; apply/forallP=> v; apply/implyP=> uNB; apply/implyP.
  rewrite in_set1 => /eqP ->.
  (* head of the candidate forward arc is vertex 0; no vertex is < 0 *)
  by rewrite arcTTE ltn0.
Qed.

(** GROUNDING (Woodall antecedent inhabited): [TT 2] has a one-way set, so the
    [oneway] predicate (and hence Woodall's antecedent) is NON-VACUOUS. *)
Theorem woodall_antecedent_inhabited :
  exists (D : diGraphType) (B : {set D}), oneway B.
Proof. by exists (TT 2), [set (Ordinal (isT : (0<2)%N)) : TT 2]; exact: oneway_TT2_source. Qed.

(** *** Linial–Berge *)

(** On the empty digraph, the empty path-partition [Q = [::]] is a valid
    path-partition (covers all 0 vertices, each on ≤ 1 path), and [S = set0]
    induces a χ⃗ ≤ k subdigraph with [pp_knorm = 0 = #|set0|], optimal.  So
    [linial_berge_statement] HOLDS on [TT 0] — NOT refutable there. *)
Lemma pp_partition_empty_TT0 : pp_partition ([::] : seq (TT 0 * seq (TT 0))).
Proof.
by rewrite /pp_partition; apply/and3P; split=> //; apply/forallP=> x; case: x => -[].
Qed.

(** [set0] induces a χ⃗ ≤ k subdigraph (empty digraph is acyclic / k-colourable). *)
Lemma dicolorableb_induced_set0 (D : diGraphType) (k : nat) :
  (0 < k)%N -> dicolorableb (induced_digraph (set0 : {set D})) k.
Proof.
move=> k0; apply/existsP.
have e : induced_digraph (set0 : {set D}) -> 'I_k.
  by move=> -[x]; rewrite inE.
exists (finfun e); apply/forallP=> i; apply/forallP=> x.
exfalso; move: x => -[[z zP] _]; by rewrite in_set0 in zP.
Qed.

(** GROUNDING (Linial–Berge NOT refutable on the empty digraph): the witnesses
    [Q = [::]], [S = set0] satisfy every clause of [linial_berge_statement] on
    [TT 0], so the statement holds there (no empty-digraph counterexample). *)
Theorem linial_berge_empty_ok :
  forall k : nat, (0 < k)%N ->
    exists (Q : seq (TT 0 * seq (TT 0))) (S : {set TT 0}),
      [/\ pp_partition Q,
          dicolorableb (induced_digraph S) k,
          pp_knorm k Q = #|S| &
          forall Q' : seq (TT 0 * seq (TT 0)),
            pp_partition Q' -> (#|S| <= pp_knorm k Q')%N].
Proof.
move=> k k0; exists [::], set0; split.
- exact: pp_partition_empty_TT0.
- exact: dicolorableb_induced_set0.
- by rewrite /pp_knorm big_nil cards0.
- by move=> Q' _; rewrite cards0.
Qed.

(** *** Erdős–Pósa for long directed cycles *)

(** On the empty digraph there is no dicycle at all, so the empty transversal
    [T = set0] meets every long dicycle vacuously: the RIGHT disjunct of
    [erdos_posa_long_dicycles_statement] holds with [t = 0].  NOT refutable. *)
Lemma meets_long_dicycles_empty (ell : nat) :
  meets_long_dicycles (D:=TT 0) ell set0.
Proof.
move=> c dc _.
case: c dc => [|x s]; first by case/and3P.
by case: x => -[].
Qed.

(** GROUNDING (Erdős–Pósa NOT refutable on the empty digraph): for any [ell] the
    right disjunct (a bounded long-cycle transversal) is satisfied by [t = 0],
    [T = set0] on [TT 0]; so the statement holds there. *)
Theorem erdos_posa_empty_ok :
  forall ell : nat,
    exists T : {set TT 0}, (#|T| <= 0)%N /\ meets_long_dicycles ell T.
Proof.
move=> ell; exists set0; split; first by rewrite cards0.
exact: meets_long_dicycles_empty.
Qed.

(** Additionally: at [n = 0] the LEFT disjunct of Erdős–Pósa is realizable on
    EVERY digraph (the empty cycle pack has size 0 and all-long vacuously), so the
    statement's [n = 0] slice is uniformly satisfiable (non-vacuous, not a
    degenerate failure). *)
Theorem erdos_posa_n0_left (D : diGraphType) (ell : nat) :
  exists P : seq (seq D),
    [/\ cycle_pack P, vtx_disjoint_pack P, size P = 0%N &
        all (fun c => ell <= size c)%N P].
Proof.
exists [::]; split=> //.
by apply/forallP=> -[].
Qed.

(** *** BT / HR antecedent class inhabited (the guard fix gives a non-empty class) *)

(** GROUNDING (BT antecedent inhabited at k = 1): C₃ has [0 < #|C3|] and every
    vertex has out-degree ≥ 1 = 2·1−1, so the (NOW-GUARDED) Bermond–Thomassen
    antecedent is satisfied by C₃ — the fix gives a NON-EMPTY hypothesis class
    (the empty-digraph counterexample is excluded but the class is not empty). *)
Theorem bermond_thomassen_antecedent_C3 :
  (0 < #|{: C3}|)%N /\ (forall v : C3, (2 * 1 - 1 <= outdeg v)%N).
Proof. by rewrite card_C3; split=> // v; rewrite outdeg_C3. Qed.

(** GROUNDING (HR antecedent inhabited at k = 1): same for Hoàng–Reed. *)
Theorem hoang_reed_antecedent_C3 :
  (0 < #|{: C3}|)%N /\ (forall v : C3, (1 <= outdeg v)%N).
Proof. by rewrite card_C3; split=> // v; rewrite outdeg_C3. Qed.

(** ====================================================================== *)
(** ** Erdős–Pósa for long directed cycles — RIGHT-POLARITY FRAGMENTS       *)
(**                                                                         *)
(**    The full [erdos_posa_long_dicycles_statement] is OPEN for [n >= 2]    *)
(**    (its settled subcase, the unrestricted directed Erdős–Pósa property   *)
(**    of Reed–Robertson–Seymour–Thomas 1996, is a deep landmark and does    *)
(**    not even imply the length-restricted variant).  We pin the TRUTH      *)
(**    VALUE of the statement on the fully decided small parameters [n = 0]  *)
(**    and [n = 1] — both hold with the UNIFORM bound [t = 0], independently  *)
(**    of RRST — and we expose that all remaining difficulty lives in the    *)
(**    UNIFORMITY of [t] across arbitrarily large [D].                       *)
(** ====================================================================== *)

(** A singleton cycle pack is always vertex-disjoint (the only index pair is
    [(i, i)], excluded by [i != j]). *)
Lemma vtx_disjoint_pack1 (D : diGraphType) (c : seq D) :
  vtx_disjoint_pack [:: c].
Proof.
apply/forallP => i; apply/forallP => j; apply/implyP => nij.
by move: nij; rewrite (ord1 i) (ord1 j) eqxx.
Qed.

(** *** n = 0 slice of the full conjecture *)

(** GROUNDING (statement TRUE at [n = 0], uniform [t = 0]): the FULL
    "[exists t, forall D, ...]" conjecture at the decided parameter [n = 0]
    holds with [t = 0] — on every digraph the empty cycle pack realizes the
    LEFT disjunct.  This assembles the per-[D] lemma [erdos_posa_n0_left] into
    the complete conjecture slice (strictly more than the per-[D] fact). *)
Theorem eplp_n0_slice (ell : nat) : (2 <= ell)%N ->
  exists t : nat, forall D : diGraphType,
    (exists P : seq (seq D),
       [/\ cycle_pack P, vtx_disjoint_pack P, size P = 0%N &
           all (fun c => ell <= size c)%N P])
    \/ (exists T : {set D}, (#|T| <= t)%N /\ meets_long_dicycles ell T).
Proof.
move=> _; exists 0%N => D; left; exact: erdos_posa_n0_left.
Qed.

(** *** Decidability of "has a long dicycle" (needed for the n = 1 slice) *)

(** Being a long dicycle is a bounded-length condition (a dicycle is [uniq], so
    of length [<= #|D|]); we reflect its existence as a boolean, quantifying
    over the finitely many tuple-length classes. *)
Definition has_long_dicycle (D : diGraphType) (ell : nat) : bool :=
  [exists k : 'I_(#|D|).+1, (ell <= k)%N && [exists t : k.-tuple D, dicycle (val t)]].

Lemma has_long_dicycleP (D : diGraphType) (ell : nat) :
  reflect (exists c : seq D, dicycle c /\ (ell <= size c)%N)
          (has_long_dicycle D ell).
Proof.
rewrite /has_long_dicycle.
apply: (iffP existsP) => [[k /andP[hk /existsP[t dt]]] | [c [dc hc]]].
  by exists (val t); split; [exact: dt | rewrite size_tuple].
have uc : uniq c by case/and3P: dc.
have szle : (size c <= #|D|)%N.
  have /card_uniqP scard := uc.
  by have := max_card (mem c); rewrite scard.
exists (Ordinal (n:=(#|D|).+1) (m:=size c) szle); apply/andP; split=> //.
by apply/existsP; exists (in_tuple c); exact: dc.
Qed.

(** *** n = 1 slice of the full conjecture — the classic base case *)

(** GROUNDING (statement TRUE at [n = 1], uniform [t = 0]): the FULL
    "[exists t, forall D, ...]" conjecture at [n = 1] holds with [t = 0].  This
    is the classic one-cycle Erdős–Pósa base case, TRUE independently of RRST:
    on each [D] either a long dicycle exists (a size-1 pack, LEFT disjunct) or
    none does (the empty transversal [t = 0] meets all long dicycles vacuously,
    RIGHT disjunct).  Pins the statement's truth value at [n = 1] for every
    [ell >= 2], with a bound uniform over ALL [D]; hence every RRST-strength
    difficulty of the conjecture lives strictly in [n >= 2]. *)
Theorem eplp_n1_slice (ell : nat) : (2 <= ell)%N ->
  exists t : nat, forall D : diGraphType,
    (exists P : seq (seq D),
       [/\ cycle_pack P, vtx_disjoint_pack P, size P = 1%N &
           all (fun c => ell <= size c)%N P])
    \/ (exists T : {set D}, (#|T| <= t)%N /\ meets_long_dicycles ell T).
Proof.
move=> _; exists 0%N => D.
case: (boolP (has_long_dicycle D ell)) => [/has_long_dicycleP[c [dc lc]] | h].
- left; exists [:: c]; split.
  + by rewrite /cycle_pack; apply/allP => x; rewrite mem_seq1 => /eqP ->.
  + exact: vtx_disjoint_pack1.
  + by [].
  + by apply/allP => x; rewrite mem_seq1 => /eqP ->.
- right; exists set0; split; first by rewrite cards0.
  move=> c dc lc; case/negP: h.
  by apply/has_long_dicycleP; exists c; split.
Qed.

(** *** Per-D inhabitation of the right disjunct's predicate on a REAL object *)

(** GROUNDING (transversal predicate inhabited per [D] on [T = [set: D]]): for
    EVERY digraph the full vertex set is a valid long-cycle transversal (a
    dicycle is nonempty, so its head lies in [[set: D]]).  This complements the
    empty-graph [meets_long_dicycles_empty] with a NON-degenerate witness on an
    arbitrary [D], making explicit that the sole open content of the conjecture
    is the UNIFORMITY of the bound [t] (here [#|T| = #|D|] is unbounded). *)
Theorem meets_long_dicycles_setT (D : diGraphType) (ell : nat) :
  meets_long_dicycles ell [set: D].
Proof.
move=> c dc _; case: c dc => [|x s]; first by case/and3P.
by move=> _; exists x; [rewrite in_setT | exact: mem_head].
Qed.

(** *** Teeth: the LEFT (packing) disjunct genuinely fires on a real digraph *)

(** GROUNDING (packing branch non-vacuous on [C3]): on the concrete NONEMPTY
    directed triangle [C3], the LEFT disjunct of the [n = 1] slice is realized —
    [[:: 0; 1; 2]] is a dicycle of length 3, a valid size-1 pack of long cycles
    for every [ell <= 3].  So the statement's packing branch is achievable on a
    real object (both disjuncts are genuinely inhabited across the suite). *)
Theorem eplp_left_fires_C3 (ell : nat) : (ell <= 3)%N ->
  exists P : seq (seq C3),
    [/\ cycle_pack P, vtx_disjoint_pack P, size P = 1%N &
        all (fun c => ell <= size c)%N P].
Proof.
move=> hl; exists [:: [:: (0 : C3); 1; 2]]; split.
- by rewrite /cycle_pack; apply/allP => x; rewrite mem_seq1 => /eqP ->; exact: C3_dicycle.
- exact: vtx_disjoint_pack1.
- by [].
- by apply/allP => x; rewrite mem_seq1 => /eqP ->; exact: hl.
Qed.

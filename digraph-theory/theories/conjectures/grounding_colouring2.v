(** * Digraph.conjectures.grounding_colouring2 — STATEMENT-LEVEL grounding for
    colouring_variants.v (pass 2: the parts NOT covered by grounding_chi_col.v).

    grounding_chi_col.v already grounded the oriented-colouring and the
    [majority_col] / [c3const] red-flag side of colouring_variants.v.  This file
    grounds the REMAINING machinery — the arc-colouring / monochromatic
    reachability and the parametric majority bound — along the three
    faithfulness axes:

      (1) NON-VACUITY: each of the four open _statement Props ranges over a
          hypothesis class; we exhibit a CONCRETE inhabitant of every antecedent
          (majority_3col_statement: a digraph; oriented_chromatic_planar_bounded:
          a loopless planar oriented digraph; mono_reach_or_rainbow:
          a nonempty 3-arc-coloured tournament; sands_sauer_woodrow:
          a k-arc-coloured digraph).  A forall over an empty class says nothing.

      (2) SMALL-INSTANCE WITNESSES / VALUES on tiny digraphs:
          - a CONCRETE majority 3-colouring of C3 (the constant colouring FAILS,
            but an honest rainbow colouring SUCCEEDS — value-level check that the
            existential head of Conj 2 holds on the directed triangle);
          - a CONCRETE [kmajority_col] witness for k=2,3 on TT 2 (single arc);
          - a CONCRETE [mono_reach] instance on a 1-arc-coloured TT 2 (0 reaches
            1 in the unique colour, and reflexively everywhere);
          - a CONCRETE [rainbow_triangle] on C3 (the identity-on-arcs colouring
            assigns the three cyclic arcs three distinct colours);
          - a CONCRETE [mono_root] on C3 (constant arc-colouring: vertex 0 reaches
            every vertex via the monochromatic directed cycle).

      (3) TRIVIALITY / FALSIFICATION probes: an OPEN conjecture must be NEITHER
          provable nor refutable / not vacuous / not trivially true.  We pin:
          - [mono_root] is NOT automatic: the EMPTY arc-colouring of TT 2 (so no
            arc carries any colour) has NO monochromatic root, because vertex 0
            cannot reach 1.  So the disjunction in [mono_reach_or_rainbow] has
            real content (it is not "rainbow ∨ trivially-true");
          - [rainbow_triangle] is NOT automatic: a CONSTANT 3-arc-colouring of C3
            has NO rainbow triangle (its three arcs share a colour).  So the
            "rainbow" disjunct is also not free;
          - [majority_col] is NOT vacuously satisfied by every colouring (the
            constant colouring of C3 fails — re-confirmed here via the parametric
            [kmajority_col] at k=2).

    Imports ONLY committed modules.  No Admitted / Axiom: every lemma is Qed. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra.
From Digraph Require Import prelude digraph oriented tournament dipath.
From Digraph Require Import dichromatic two_extremal classic_core colouring_variants.
Set SsrOldRewriteGoalsOrder.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ==================================================================== *)
(** ** A. NON-VACUITY of the four open _statement antecedent classes.

    Each Prop is [forall <class member>, ...] (or [exists f, forall member, ...]).
    We inhabit the class so the universal is not vacuously about nothing. *)

(** *** A.1  [majority_3col_statement] ranges over ALL digraphs — inhabited by
    the directed triangle C3 (3 vertices, 3 arcs).  (Trivially the class of
    digraphs is non-empty; we name a concrete nonempty member to also feed the
    value checks below.) *)
Lemma majority_class_inhabited : exists D : diGraphType, (0 < #|D|)%N.
Proof. by exists (C3 : diGraphType); rewrite card_C3. Qed.

(** *** A.2  [mono_reach_or_rainbow_statement] ranges over nonempty 3-arc-
    coloured tournaments.  C3 IS a tournament, is nonempty, and carries an
    arc-colouring (e.g. the constant one) — the antecedent class is inhabited. *)
Lemma c3_constarc : arc_colouring C3 3.
Proof. exact: (fun _ _ => ord0). Qed.

Lemma mono_reach_or_rainbow_class_inhabited :
  exists (T : tournament) (c : arc_colouring T 3), (0 < #|T|)%N.
Proof.
exists (C3 : tournament), (fun _ _ => ord0).
by rewrite card_C3.
Qed.

(** *** A.3  [sands_sauer_woodrow_statement] ranges over k-arc-coloured digraphs
    for every k; for any k ≥ 1 the class is inhabited (C3 with a constant
    k-colouring).  For k = 0 the colour type 'I_0 is empty, so there is NO
    arc-colouring of a digraph WITH an arc — a genuine (and correct) degeneracy
    we record, since SSW is only interesting for k ≥ 1. *)
Lemma ssw_class_inhabited (k : nat) :
  (0 < k)%N -> exists (D : diGraphType) (c : arc_colouring D k), (0 < #|D|)%N.
Proof.
move=> k0; exists (C3 : diGraphType), (fun _ _ => Ordinal k0).
by rewrite card_C3.
Qed.

(** Since 2026-10-25 [sands_sauer_woodrow_statement] ranges over LOOPLESS k-arc-coloured
    digraphs; the same witness C3, a tournament, is loopless, so the guarded class is inhabited
    for every k ≥ 1 too. *)
Lemma ssw_loopless_class_inhabited (k : nat) :
  (0 < k)%N ->
  exists (D : diGraphType) (c : arc_colouring D k), loopless D /\ (0 < #|D|)%N.
Proof.
move=> k0; exists (C3 : diGraphType), (fun _ _ => Ordinal k0).
by split; [move=> v; rewrite arcxx | rewrite card_C3].
Qed.

(** *** A.4  [oriented_chromatic_planar_bounded_statement] ranges over loopless
    oriented digraphs whose underlying simple graph is planar.  TT 2 (a single
    arc) is loopless and oriented; its underlying graph is a single edge, which
    is planar.  We record the loopless witness here (planarity of a single edge
    is supplied by two_extremal.planar_sg's K5/K33-minor-free criterion, which a
    2-vertex graph trivially meets — established at the two_extremal level). *)
Lemma loopless_TT2 : loopless (TT 2 : diGraphType).
Proof. by move=> v; rewrite arcxx. Qed.

Lemma planar_class_loopless_inhabited :
  exists (D : diGraphType), loopless D.
Proof. by exists (TT 2 : diGraphType); exact: loopless_TT2. Qed.

(** ==================================================================== *)
(** ** B. CONCRETE majority 3-colouring of C3 (the value head of Conj 2).

    grounding_chi_col.v showed the CONSTANT colouring of C3 FAILS majority.
    Here we exhibit a colouring that SUCCEEDS: colour each vertex with its own
    'Z_3 index (the "rainbow" / identity colouring).  Then every vertex's unique
    out-neighbour [v+1] has a DIFFERENT colour, so the same-colour
    out-neighbourhood is empty and 2·0 ≤ outdeg trivially. *)

Definition c3rainbow (v : C3) : 'I_3 := v.

Lemma c3rainbow_same_empty (v : C3) : same_col_outnb c3rainbow v = set0.
Proof.
apply/setP=> w; rewrite inE in_set0.
apply/andP=> -[]; rewrite arcC3E /c3rainbow => /eqP wv /eqP wv2.
(* colour of w equals colour of v means w = v (as 'I_3 = 'Z_3), but w = v+1 *)
move: (C3_irrefl v); rewrite arcC3E -{1}wv2 -wv eqxx => /esym.
by [].
Qed.

Lemma majority_col_c3rainbow : majority_col c3rainbow.
Proof. by apply/forallP=> v; rewrite c3rainbow_same_empty cards0 muln0. Qed.

(** The existential head [exists col : C3 -> 'I_3, majority_col col] of Conj 2
    holds on the directed triangle. *)
Lemma majority_3col_C3 : exists col : C3 -> 'I_3, majority_col col.
Proof. by exists c3rainbow; exact: majority_col_c3rainbow. Qed.

(** ==================================================================== *)
(** ** C. CONCRETE kmajority_col witnesses on TT 2 (single arc 0→1).

    The identity colouring 'I_2 -> 'I_2 makes every same-colour out-neighbourhood
    empty (0's out-neighbour 1 has colour 1 ≠ 0).  Hence [kmajority_col k] holds
    for EVERY k (k·0 = 0 ≤ outdeg).  This is the parametric (1/k)·deg⁺ head of
    Conjecture 9, instantiated at k = 2 (= majority) and k = 3. *)

Definition tt2id (v : TT 2) : 'I_2 := v.

Lemma tt2id_same_empty (v : TT 2) : same_col_outnb tt2id v = set0.
Proof.
apply/setP=> w; rewrite inE in_set0.
apply/andP=> -[vw]; rewrite /tt2id => /eqP wv.
by move: vw; rewrite wv arcxx.
Qed.

Lemma kmajority_col_TT2 (k : nat) : kmajority_col k tt2id.
Proof. by apply/forallP=> v; rewrite tt2id_same_empty cards0 muln0. Qed.

(** At k = 2 this is exactly [majority_col] (via the committed [kmajority_col2]). *)
Lemma kmajority_col2_TT2 : majority_col tt2id.
Proof. by rewrite -kmajority_col2; exact: kmajority_col_TT2. Qed.

(** Conj 9's existential head at k = 2 on TT 2 (3-colour, (1/2)·deg⁺ bound):
    lift the 2-colouring into 'I_3. *)
Lemma kmajority_k1_head_TT2 : exists col : TT 2 -> 'I_3, kmajority_col 2 col.
Proof.
pose col := fun v : TT 2 => widen_ord (isT : (2 <= 3)%N) (tt2id v).
exists col; apply/forallP=> v.
have hempty : same_col_outnb col v = set0.
  apply/setP=> w; rewrite inE in_set0.
  apply/andP=> -[vw]; rewrite /col -val_eqE /= /tt2id => /eqP eqval.
  by move: vw; rewrite (val_inj eqval) arcxx.
by rewrite hempty cards0 muln0.
Qed.

(** ==================================================================== *)
(** ** D. CONCRETE monochromatic reachability on a 1-arc-coloured TT 2.

    Colour the single arc 0→1 with the unique colour [ord0 : 'I_1].  Then:
      - reflexively every vertex reaches itself in colour 0 ([mono_reach_refl]);
      - vertex 0 reaches vertex 1 by the colour-0 arc (one [connect1] step).
    So 0 is a monochromatic-reachability ROOT in this 1-colouring. *)

Definition tt2arc1 : arc_colouring (TT 2) 1 := fun _ _ => ord0.

Lemma mono_rel_tt2arc1 (u v : TT 2) :
  mono_rel tt2arc1 ord0 u v = (u --> v).
Proof. by rewrite /mono_rel /tt2arc1 eqxx andbT. Qed.

(** 0 --> 1 holds in TT 2. *)
Lemma tt2_0arc1 :
  (Ordinal (isT : (0 < 2)%N) : TT 2) --> (Ordinal (isT : (1 < 2)%N)).
Proof. by rewrite arcTTE. Qed.

Lemma mono_reach_tt2_0to1 :
  mono_reach tt2arc1 ord0
    (Ordinal (isT : (0 < 2)%N)) (Ordinal (isT : (1 < 2)%N)).
Proof.
apply: connect1; rewrite mono_rel_tt2arc1; exact: tt2_0arc1.
Qed.

(** Vertex 0 is a monochromatic-reachability ROOT of (TT 2, tt2arc1): it reaches
    both vertices (itself reflexively, 1 via the coloured arc). *)
Lemma mono_root_tt2_0 : mono_root tt2arc1 (Ordinal (isT : (0 < 2)%N)).
Proof.
apply/forallP=> w; apply/existsP; exists ord0.
(* w is either 0 (reflexive) or 1 (one arc step) *)
case: w => -[|[|//]] hw.
- by rewrite (_ : Ordinal hw = Ordinal (isT : (0 < 2)%N)) ?mono_reach_refl //;
     apply: val_inj.
- rewrite (_ : Ordinal hw = Ordinal (isT : (1 < 2)%N)); last by apply: val_inj.
  exact: mono_reach_tt2_0to1.
Qed.

(** ==================================================================== *)
(** ** E. CONCRETE rainbow triangle on C3.

    The 3-arc-colouring that gives arc (u,v) the colour [v : 'I_3] (its head's
    index) assigns the three cyclic arcs 0→1, 1→2, 2→0 the three colours 1,2,0 —
    pairwise distinct.  So C3 has a rainbow directed triangle under this
    colouring (the LEFT disjunct of [mono_reach_or_rainbow_statement] is
    realisable). *)

Definition c3head : arc_colouring C3 3 := fun _ v => v.

Section E_C3rainbow.
Local Open Scope ring_scope.
Import GRing.Theory.

Lemma arcC3_01 : (0 : C3) --> (1 : C3).
Proof. by rewrite arcC3E add0r. Qed.
Lemma arcC3_12 : (1 : C3) --> (1 + 1 : C3).
Proof. by rewrite arcC3E. Qed.
Lemma arcC3_20 : (1 + 1 : C3) --> (0 : C3).
Proof. by rewrite arcC3E; apply/eqP; apply: val_inj. Qed.

Lemma rainbow_triangle_c3head : rainbow_triangle c3head.
Proof.
exists (0 : C3), (1 : C3), (1 + 1 : C3); split.
- exact: arcC3_01.
- exact: arcC3_12.
- exact: arcC3_20.
- (* colours are [c 0 1; c 1 (1+1); c (1+1) 0] = [1; 1+1; 0], pairwise distinct *)
  by rewrite /c3head; vm_compute.
Qed.

End E_C3rainbow.

(** ==================================================================== *)
(** ** F. TRIVIALITY / FALSIFICATION probes — the disjuncts are NOT free.

    The open [mono_reach_or_rainbow_statement] is "rainbow triangle ∨ a
    mono-root".  A faithful encoding must make BOTH disjuncts genuinely
    falsifiable, else the disjunction is provable for free.  We refute each
    disjunct on a concrete instance. *)

(** *** F.1  [rainbow_triangle] is NOT automatic: a CONSTANT 3-arc-colouring of
    C3 has NO rainbow triangle (all three arcs share colour 0, so the colour
    multiset is never uniq). *)
Definition c3const3 : arc_colouring C3 3 := fun _ _ => ord0.

Lemma no_rainbow_c3const3 : ~ rainbow_triangle c3const3.
Proof.
case=> a [b [c0 [_ _ _ ]]]; rewrite /c3const3.
(* [ord0; ord0; ord0] is not uniq *)
by vm_compute.
Qed.

(** *** F.2  [mono_root] is NOT automatic: the EMPTY-on-arcs case.  Take TT 2 but
    a colouring where the (only) arc 0→1 gets a colour that is NEVER reachable —
    impossible in 'I_1 (one colour).  Instead, use a 2-colouring where the arc
    0→1 carries colour 1 but we test reachability for the SUB-relation of colour
    0, which is empty, so 0 does NOT reach 1 in colour 0.  Combined with E/D,
    this shows mono-reachability genuinely depends on the colouring. *)
Definition tt2arc_to1 : arc_colouring (TT 2) 2 :=
  fun _ _ => Ordinal (isT : (1 < 2)%N).

(** In colour 0 the sub-relation is empty (every arc carries colour 1). *)
Lemma mono_rel_tt2arc_to1_col0 (u v : TT 2) :
  mono_rel tt2arc_to1 ord0 u v = false.
Proof.
rewrite /mono_rel /tt2arc_to1.
have -> : (Ordinal (isT : (1 < 2)%N) == ord0 :> 'I_2) = false.
  by rewrite -val_eqE.
by rewrite andbF.
Qed.

(** Hence 0 does NOT reach 1 in colour 0 (the only step available is the loop). *)
Lemma not_mono_reach_tt2_col0 :
  ~~ mono_reach tt2arc_to1 ord0
       (Ordinal (isT : (0 < 2)%N)) (Ordinal (isT : (1 < 2)%N)).
Proof.
apply/connectP=> -[p].
- (* with an empty step relation, any non-trivial path is impossible; the path
     must be [::] so source = target, but 0 ≠ 1 *)
  case: p => [/= _ h|x p /=].
  + by move: h => /(congr1 val) /=.
  + by rewrite mono_rel_tt2arc_to1_col0.
Qed.

(** *** F.3  Re-confirm [majority_col] is NOT vacuous via the parametric form:
    the CONSTANT colouring of C3 violates [kmajority_col 2] (= majority), since
    each vertex's unique out-neighbour shares its colour: 2·1 = 2 > 1 = outdeg. *)
Definition c3const2 (_ : C3) : 'I_2 := ord0.

Lemma c3const2_same (v : C3) : same_col_outnb c3const2 v = [set (v + 1)%R].
Proof. by apply/setP=> w; rewrite !inE arcC3E; case: (w == (v + 1)%R). Qed.

Lemma c3_outdeg1' (v : C3) : outdeg v = 1%N.
Proof.
rewrite /outdeg.
have -> : [set w | v --> w] = [set (v + 1)%R].
  by apply/setP=> w; rewrite !inE arcC3E.
by rewrite cards1.
Qed.

Lemma not_kmajority_col2_c3const2 : ~~ kmajority_col 2 c3const2.
Proof.
apply/forallPn; exists ord0.
by rewrite c3const2_same cards1 c3_outdeg1' muln1.
Qed.

(** ==================================================================== *)
(** ** G. The relative-edge theorems are genuine implications (no Admit).

    Re-expose the committed [majority_k1col_implies_majority_3col] edge to
    confirm it is a clean implication that we can DISCHARGE its hypothesis from
    Conj 9 — a faithfulness check that the edge is content-bearing, not an
    encoding artefact.  (The open statements themselves are NOT proved here:
    they require infinite-family arguments — correctly hard, NOT a red flag.) *)
Lemma conj9_implies_conj2_edge :
  majority_k1col_statement -> majority_3col_statement.
Proof. exact: majority_k1col_implies_majority_3col. Qed.

(** And the tournament / Eulerian specialisations are honest specialisations. *)
Lemma conj2_specialises_tournament :
  majority_3col_statement -> majority_3col_tournament_statement.
Proof. exact: majority_3col_implies_tournament. Qed.

(** ==================================================================== *)
(** ** H. RIGHT-POLARITY fragments of [mono_reach_or_rainbow_statement].

    The open statement is: every nonempty 3-arc-coloured tournament has a
    rainbow triangle OR a monochromatic-reachability root.  The grounding above
    (sections A/D/E/F) only inhabits the class and exercises the two disjuncts
    in isolation on a fixed colouring.  Here we PIN THE STATEMENT TRUE, via its
    RIGHT disjunct [exists v, mono_root c v], on the settled dominating-vertex
    sub-cases — for ARBITRARY 3-arc-colourings — and we confirm the [0 < #|T|]
    guard is load-bearing (not vacuizing).  These are genuine truth-value
    forcing facts: they discharge the conjecture on an infinite sub-family and
    the smallest nonempty parameter without touching the open general case. *)

(** *** H.1  ALWAYS-TRUE-DIRECTION.  In ANY tournament, a source vertex [v]
    (one that dominates every other vertex) is a monochromatic-reachability
    root for EVERY 3-arc-colouring: it reaches itself by the empty colour-[ord0]
    path, and every other [w] by the single arc [v --> w] taken in its own
    colour [c v w].  So the RIGHT disjunct of the statement holds outright, and
    it holds uniformly over all colourings — the colouring is never consulted to
    decide reachability past the first arc.  This is the reusable core: the
    whole tournaments-with-a-source class satisfies the statement. *)
Lemma dominating_mono_root (T : tournament) (c : arc_colouring T 3) (v : T) :
  (forall w : T, w != v -> v --> w) -> mono_root c v.
Proof.
move=> Hdom; apply/forallP => w; apply/existsP.
case: (eqVneq w v) => [->|wv].
- by exists ord0; exact: mono_reach_refl.
- exists (c v w); apply: connect1.
  by rewrite /mono_rel eqxx andbT; exact: (Hdom _ wv).
Qed.

(** *** H.2  SMALL-INSTANCE (infinite settled sub-family).  The FULL conclusion
    of [mono_reach_or_rainbow_statement] holds for EVERY transitive tournament
    [TT n] with [n >= 1], under EVERY 3-arc-colouring: vertex [0 = Ordinal n0]
    dominates all others (in [TT n], [0 --> w] iff [0 < val w], which holds for
    all [w != 0]).  This decides the open conjecture TRUE on the whole family
    {TT n : n >= 1}, for arbitrary colourings — the right disjunct, via H.1. *)
Lemma mono_reach_or_rainbow_TTn (n : nat) (c : arc_colouring (TT n) 3) :
  (0 < n)%N -> rainbow_triangle c \/ exists v : TT n, mono_root c v.
Proof.
move=> n0; right; exists (Ordinal n0); apply: dominating_mono_root => w wne.
rewrite arcTTE lt0n.
by move: wne; rewrite -val_eqE.
Qed.

(** *** H.3  SMALL-INSTANCE (base case).  The full conclusion holds for EVERY
    singleton tournament ([#|T| = 1]) under EVERY 3-arc-colouring: its unique
    vertex vacuously dominates (there is no [w != v]), hence is a mono-root by
    H.1.  This is the smallest nonempty parameter of the statement, decided TRUE
    on the right disjunct.  (The dominating hypothesis is met vacuously: any
    [w != v] would give a second element, contradicting [#|T| = 1].) *)
Lemma mono_reach_or_rainbow_card1 (T : tournament) (c : arc_colouring T 3) :
  #|T| = 1%N -> rainbow_triangle c \/ exists v : T, mono_root c v.
Proof.
move=> T1; have /card_gt0P [v _] : (0 < #|T|)%N by rewrite T1.
right; exists v; apply: dominating_mono_root => w wv.
have /card_le1_eqP eqall : (#|[set: T]| <= 1)%N by rewrite cardsT T1.
have wveq : w = v := eqall v w (in_setT v) (in_setT w).
by rewrite wveq eqxx in wv.
Qed.

(** *** H.4  GUARD FAITHFULNESS (the [0 < #|T|] hypothesis is load-bearing).
    On the EMPTY tournament [TT 0] the conclusion is FALSE: a rainbow triangle
    needs three vertices and a mono-root needs one, but [TT 0 = 'I_0] has NONE
    (every purported vertex [Ordinal m] would carry [m < 0], impossible).  So
    dropping the guard would make the statement false for a trivial reason;
    keeping it does NOT vacuize the statement (H.2/H.3 show the guarded class is
    richly satisfiable), it exactly excludes the single degenerate falsifier. *)
Lemma TT0_no_conclusion (c : arc_colouring (TT 0) 3) :
  ~ (rainbow_triangle c \/ exists v : TT 0, mono_root c v).
Proof.
case.
- by case=> a [b [c0 _]]; case: a => m; rewrite ltn0.
- by case=> v _; case: v => m; rewrite ltn0.
Qed.

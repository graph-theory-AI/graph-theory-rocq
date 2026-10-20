(** * Digraph.conjectures.grounding_sad_packing — GROUNDING of [sad.v] + [packing.v]

    Faithfulness checks: small, decidable, textbook-true facts that the NEW
    definitions of arc-connectivity ([sad.v]: [outcut], [arc_strong], [lambda],
    [SAD]) and packing ([packing.v]: [cycle_pack], [dicycle] base case) must
    satisfy if they are faithful to the literature.  Every lemma is [Qed]; the
    file imports ONLY committed modules.

    Grounded facts (each tied to a textbook statement):

      1. λ(directed cycle) = 1, in the cut-predicate form
         [arc_strong (Cyc n) 1] for every n ≥ 1, plus the matching upper bound
         [lambda (Cyc n) = 1] for n ≥ 2 (some single boundary out-arc, never
         more is forced).  Textbook: a directed cycle is 1-arc-strong and its
         minimum out-cut δ⁺ has size exactly 1 (Bang-Jensen & Gutin,
         *Digraphs*, ch. on arc-strong connectivity).

      2. [arc_strong_mono] re-exercised: k-arc-strong ⟹ j-arc-strong, j ≤ k
         (monotonicity of λ-thresholds — already in sad.v; we re-derive a fresh
         instance to confirm the definition supports it).

      3. PACKING base case (Bermond–Thomassen / Hoàng–Reed at k = 1, the classic
         "δ⁺ ≥ 1 ⟹ a directed cycle"): a finite digraph whose every vertex has
         out-degree ≥ 1 contains a [dicycle].  Proof = follow out-arcs until a
         vertex repeats (pigeonhole on a finite type), giving the orbit of a
         periodic vertex as the cycle.  This grounds [packing.hoang_reed_statement]
         at [k = 1] UNCONDITIONALLY (the file only had it relative to HR).

    RED-FLAG probes (reported, all benign here):
      - [arc_strong] is NOT vacuous: its quantifier ranges over nonempty proper
        [X], which exist as soon as 2 ≤ |D| (witnessed on [Cyc 2]).
      - [lambda]'s empty-fold default ([#|D|*#|D|]) DOES make degenerate small
        cases "lie": on a 1-vertex digraph there is no proper [X], so
        [lambda = 1] even though there is no cut at all.  Documented in sad.v and
        confirmed here ([lambda_singleton_default]); harmless because the
        conjectures use [arc_strong], not [lambda], and guard [0 < #|D|].          *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented dipath strong tournament.
From Digraph Require Import sad packing.
Set SsrOldRewriteGoalsOrder.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** A concrete directed cycle [Cyc n] (own copy; no team-file import) *)

(** A big-[minn] over a list is ≤ any of its terms whose guard holds (the
    upper-bound direction of a minimum-fold; [minn] is not an AC monoid in the
    library so we derive it by hand). *)
Lemma bigmin_leq_term (I : finType) (r : seq I) (P : pred I) (F : I -> nat)
    (d : nat) (j : I) :
  j \in r -> P j -> (\big[minn/d]_(i <- r | P i) F i <= F j)%N.
Proof.
elim: r => [|a r IH] //=; rewrite inE big_cons.
case: (eqVneq j a) => [->|/= ja].
  by move=> _ Pj; rewrite Pj geq_minl.
move=> /= jr Pj; case: ifP => _.
  by apply: leq_trans (geq_minr _ _) (IH jr Pj).
exact: IH jr Pj.
Qed.

(** Arithmetic: the mod-successor [k+1 mod n] never equals [k] (no loop), n ≥ 2. *)
Lemma succ_mod_neq (n k : nat) : (2 <= n)%N -> (k < n)%N -> (k.+1 %% n == k = false).
Proof.
move=> n2 kn; apply/negbTE/eqP => E; move: E.
case: (ltngtP k.+1 n) => [lt|gt|eqn].
- by rewrite (modn_small lt) => /esym /n_Sn.
- by move: gt; rewrite ltnS leqNgt kn.
- by rewrite -eqn modnn => k0; move: n2; rewrite -eqn -k0 ltnn.
Qed.

Section Cyc.
Variable n : nat.
Hypothesis n0 : (0 < n)%N.

Definition crel (x y : 'I_n) : bool := val y == (val x).+1 %% n.
HB.instance Definition _ := Finite.on ('I_n).
HB.instance Definition _ := HasArc.Build 'I_n crel.
Definition Cyc : diGraphType := 'I_n.

(** A concrete vertex (value 0) — [Cyc]'s carrier [n] is not syntactically a
    successor, so we name [ord0] explicitly via the [0 < n] guard. *)
Definition v0 : Cyc := Ordinal n0.

(** Successor on the cycle: [x ↦ (x+1) mod n]; always an arc. *)
Definition suc (x : Cyc) : Cyc := Ordinal (ltn_pmod (val x).+1 n0).

Lemma suc_arc (x : Cyc) : x --> suc x.
Proof. by rewrite /arc/= /crel /=. Qed.

Lemma suc_arcE (x y : Cyc) : (x --> y) = (y == suc x).
Proof.
rewrite /arc/= /crel; apply/idP/idP => [/eqP E|/eqP->].
- by apply/eqP/val_inj.
- by [].
Qed.

(** Iterating [suc] [k] times shifts the value by [k] (mod n). *)
Lemma val_iter_suc k (x : Cyc) : val (iter k suc x) = (val x + k) %% n.
Proof.
elim: k => [|k IH] /=; first by rewrite addn0 modn_small.
by rewrite IH /suc /= addnS -addn1 modnDml addn1.
Qed.

(** [suc] reaches every vertex from any starting point (the cycle is one orbit). *)
Lemma suc_reaches (x j : Cyc) : exists k, iter k suc x = j.
Proof.
exists ((val j + (n - val x)) %% n).
apply: val_inj; rewrite val_iter_suc modnDmr.
rewrite (addnCA (val x) (val j)) subnKC ?(ltnW (ltn_ord x)) //.
by rewrite modnDr modn_small // ltn_ord.
Qed.

(** Boundary vertex: any nonempty proper [X] has a vertex whose successor leaves
    [X].  (If not, [X] is closed under [suc], hence — since [suc] reaches every
    vertex — equal to all of [V], contradicting properness.) *)
Lemma cyc_boundary (X : {set Cyc}) :
  X != set0 -> X != setT -> exists x, x \in X /\ suc x \notin X.
Proof.
move=> /set0Pn[x0 x0X] XnT.
have [b /andP[bX sbN]|nob] := pickP (fun x => (x \in X) && (suc x \notin X)).
  by exists b.
have closed : forall x, x \in X -> suc x \in X.
  by move=> x xX; move: (nob x); rewrite xX /= => /negbT; rewrite negbK.
have iterIn : forall (y : Cyc) k, y \in X -> iter k suc y \in X.
  by move=> y k yX; elim: k => [//|k IH] /=; apply: closed.
exfalso; move/negP: XnT; apply; apply/eqP/setP=> j; rewrite in_setT.
have [k Ek] := suc_reaches x0 j.
by rewrite -Ek; apply: iterIn.
Qed.

(** GROUNDING 1a. λ(directed cycle) ≥ 1: [Cyc n] is 1-arc-strong.  Every
    nonempty proper vertex set has a boundary out-arc, so its out-cut is ≥ 1.
    Textbook: a directed cycle is (arc-)strongly connected. *)
Lemma cyc_arc_strong : arc_strong Cyc 1.
Proof.
move=> X Xn0 XnT.
have [x [xX sxNX]] := cyc_boundary Xn0 XnT.
rewrite card_gt0; apply/set0Pn; exists (x, suc x).
by rewrite in_outcutE suc_arc xX sxNX.
Qed.

(** The successor of a vertex is never the vertex itself (n ≥ 2): no loop. *)
Lemma sucNx (x : Cyc) : (2 <= n)%N -> suc x != x.
Proof.
move=> n2; apply/eqP => /(f_equal val) /= /eqP.
by rewrite succ_mod_neq // ltn_ord.
Qed.

(** Out-cut of a "prefix-by-one-vertex" set has size exactly 1 on the cycle:
    the singleton [[set x]] (a proper nonempty set once n ≥ 2) cuts off exactly
    the one arc [x --> suc x].  This pins the MINIMUM out-cut to 1. *)
Lemma outcut_singleton (x : Cyc) :
  (2 <= n)%N -> outcut [set x] = [set (x, suc x)].
Proof.
move=> n2; apply/setP=> -[u v]; rewrite in_outcutE in_set1 !inE xpair_eqE suc_arcE.
case: (altP (u =P x)) => [-> /=|_]; last by rewrite andbF.
case: (altP (v =P suc x)) => [-> /=|//].
by rewrite sucNx.
Qed.

(** GROUNDING 1b. λ(directed cycle) = 1 (the [lambda] big-min), for n ≥ 2.
    Combine the ≥ 1 bound ([arc_strong]) with the singleton cut of size 1. *)
Lemma lambda_Cyc : (2 <= n)%N -> lambda Cyc = 1.
Proof.
move=> n2.
(* the singleton [set v0] is a nonempty proper vertex set *)
have wit : ([set v0] != set0) && ([set v0] != [set: Cyc]).
  apply/andP; split; first by rewrite -card_gt0 cards1.
  apply: contraTneq (n2) => E; rewrite -ltnNge.
  have : #|[set v0]| = #|[set: Cyc]| by rewrite E.
  by rewrite cards1 cardsT card_ord => <-.
(* lower bound: 1 <= lambda, via arc_strong_lambda and the proper witness *)
have lb : (1 <= lambda Cyc)%N.
  by apply: (arc_strong_lambda (D:=Cyc)); [exists [set v0] | exact: cyc_arc_strong].
(* upper bound: lambda <= |outcut [set v0]| = 1 *)
have ub : (lambda Cyc <= 1)%N.
  rewrite -(_ : #|outcut [set v0]| = 1); last first.
    by rewrite outcut_singleton // cards1.
  rewrite /lambda; apply: bigmin_leq_term; [exact: mem_index_enum | exact: wit].
by apply/eqP; rewrite eqn_leq ub lb.
Qed.

End Cyc.

(** ** GROUNDING 2 — monotonicity of the arc-strong threshold (re-derived)

    [arc_strong_mono] is already in sad.v; we re-derive a concrete instance from
    the [arc_strong] definition itself (not calling the library lemma) to confirm
    the encoding supports the textbook fact "k-arc-strong ⟹ j-arc-strong, j ≤ k"
    (λ-thresholds are downward closed). *)
Lemma arc_strong_mono_reexercise (D : diGraphType) :
  arc_strong D 5 -> arc_strong D 2.
Proof. by move=> h5 X X0 XT; apply: leq_trans (h5 X X0 XT). Qed.

(** ** RED-FLAG probe: [arc_strong] is not vacuous; [lambda]'s default lies on
       a single vertex (documented, harmless) *)

(** Non-vacuity: for [Cyc 2] there IS a nonempty proper [X], so the quantifier
    in [arc_strong] / the big-min in [lambda] both range over a nonempty domain. *)
Lemma arc_strong_domain_nonempty :
  exists X : {set Cyc 2}, (X != set0) && (X != [set: _]).
Proof.
exists [set (ord0 : 'I_2)]; apply/andP; split.
- by rewrite -card_gt0 cards1.
- apply/eqP => E; move: (congr1 (fun s : {set Cyc 2} => #|s|) E).
  by rewrite cards1 cardsT card_ord.
Qed.

(** Confirmed quirk (NOT a bug, documented in sad.v): on a 1-vertex digraph the
    big-min over proper [X] is empty, so [lambda] returns its default
    [#|D|*#|D| = 1] — i.e. it "reports" λ = 1 although there is NO out-cut at
    all.  Harmless: the conjectures use [arc_strong] and guard [0 < #|D|]. *)
Lemma lambda_singleton_default : lambda (Cyc 1) = 1.
Proof.
rewrite /lambda big_pred0; first by rewrite card_ord.
move=> X; apply/negbTE; rewrite negb_and !negbK.
(* on 'I_1: X != set0 forces X = setT, so the proper-cut guard is always false *)
case: (eqVneq X set0) => [->|/= Xn0]; first by [].
apply/eqP/setP=> v; rewrite in_setT.
by move: Xn0 => /set0Pn[w wX]; rewrite [v]ord1; move: wX; rewrite [w]ord1 => ->.
Qed.

(** ** GROUNDING 3 — packing base case: δ⁺ ≥ 1 forces a directed cycle *)

(** Pigeonhole on a finite type: iterating any [f : T → T] from [x] eventually
    loops within the first [#|T|] iterates (the [#|T|+1] prefix cannot be uniq). *)
Lemma looping_card (T : finType) (f : T -> T) (x : T) : looping f x #|T|.
Proof.
apply: contraT; rewrite -looping_uniq => U.
have := max_card (mem (traject f x #|T|.+1)).
by rewrite (card_uniqP U) size_traject ltnNge => /negP.
Qed.

(** Hence there is a PERIODIC vertex: some [z] with [iter k.+1 f z = z]. *)
Lemma periodic_vtx (T : finType) (f : T -> T) (x : T) :
  exists z, exists k, iter k.+1 f z = z.
Proof.
have /loopingP/(_ #|T|) := looping_card f x.
case/trajectP => i ltiN Ei.
exists (iter i f x), (#|T| - i).-1.
have ge : i <= #|T| by apply: ltnW.
by rewrite prednK ?subn_gt0 // -iterD subnK // -Ei.
Qed.

(** THE BASE CASE.  A finite NONEMPTY digraph in which every vertex has
    out-degree ≥ 1 contains a directed cycle.  (Bermond–Thomassen / Hoàng–Reed
    at k = 1; the classic "min out-degree ≥ 1 ⟹ a dicycle".)  Choose any
    out-neighbour at each vertex to get a total successor map [f] with [v --> f v]
    (via [pick]); from a starting vertex, a periodic [z] for [f] has [orbit f z]
    an [f]-cycle, which is a genuine [dicycle].

    NOTE the explicit [0 < #|D|] guard: it is REQUIRED — on the empty digraph the
    hypothesis is vacuous yet a dicycle cannot exist, so the unguarded statement
    is FALSE (see [hoang_reed_false] / [bermond_thomassen_false] below). *)
Theorem min_outdeg_dicycle (D : diGraphType) :
  (0 < #|D|)%N -> (forall v : D, (1 <= outdeg v)%N) ->
  exists c : seq D, dicycle c.
Proof.
move=> Dpos hdeg.
(* total successor function: pick a real out-neighbour at each vertex *)
pose f := fun v : D => odflt v [pick w | v --> w].
have farc : forall v, v --> f v.
  move=> v; rewrite /f; case: pickP => [w /= //|no].
  move: (hdeg v); rewrite /outdeg (_ : [set w | v --> w] = set0) ?cards0 //.
  by apply/setP=> w; rewrite !inE; apply/negbTE/negP=> vw; move: (no w); rewrite /= vw.
(* a starting vertex exists since D is nonempty *)
have [x _] : exists x : D, x \in [set: D].
  by apply/set0Pn; rewrite -card_gt0 cardsT.
(* a periodic vertex of f, whose orbit is the directed cycle *)
have [z [k Ek]] := periodic_vtx f x.
exists (orbit f z).
have cyc : fcycle f (orbit f z).
  by have H := @orbitPcycle D f z; apply/(H 0 3); exists k.
apply/and3P; split.
- by rewrite /nilp size_orbit -lt0n order_gt0.
- by apply: (sub_cycle _ cyc) => u v /= /eqP <-; exact: farc.
- exact: orbit_uniq.
Qed.

(** Tie to the file's conjecture: [hoang_reed_statement] at [k = 1] over a
    NONEMPTY digraph is exactly "δ⁺ ≥ 1 ⟹ a packing of one dicycle", which
    [min_outdeg_dicycle] supplies UNCONDITIONALLY — so the [k=1] slice of
    Hoàng–Reed is a THEOREM (on nonempty digraphs), confirming the statement is
    correctly calibrated there (it must be TRUE at k = 1, and is). *)
Theorem hoang_reed_k1_holds (D : diGraphType) :
  (0 < #|D|)%N -> (forall v : D, (1 <= outdeg v)%N) ->
  exists P : seq (seq D), [/\ cycle_pack P, size P = 1 & all (@dicycle D) P].
Proof.
move=> Dpos hdeg; have [c dc] := min_outdeg_dicycle Dpos hdeg.
by exists [:: c]; rewrite /cycle_pack /= dc.
Qed.

(** ** RED FLAG (FOUND & FIXED) — the packing statements were FALSE on the empty digraph.

    Originally [hoang_reed_statement] and [bermond_thomassen_statement] quantified over
    EVERY digraph with NO [0 < #|D|] guard.  On the empty digraph [TT 0] (carrier ['I_0],
    no vertices) the min-out-degree hypothesis is VACUOUSLY satisfied yet the conclusion
    demands a size-[k=1] cycle packing (a nonempty dicycle) — impossible with no vertices —
    so BOTH statements were REFUTABLE.  An open conjecture must be neither provable nor
    refutable, so this was a definitional bug, caught by this grounding pass.  FIX:
    packing.v now carries the [(0 < #|D|)%N ->] guard on both statements, excluding the
    empty-digraph counterexample, so they are no longer refutable.  We ground the FIXED
    statements instead: the [k = 1] slice is a THEOREM on nonempty digraphs (correct
    calibration). *)

(** Bermond–Thomassen [k = 1] on a nonempty digraph of min out-degree ≥ 1: a directed
    cycle packing of size 1 — the [k=1] slice of the FIXED [bermond_thomassen_statement],
    proved unconditionally via [min_outdeg_dicycle].  (Companion to [hoang_reed_k1_holds].) *)
Theorem bermond_thomassen_k1_holds (D : diGraphType) :
  (0 < #|D|)%N -> (forall v : D, (1 <= outdeg v)%N) ->
  exists P : seq (seq D), [/\ cycle_pack P, vtx_disjoint_pack P & size P = 1].
Proof.
move=> Dpos hdeg; have [c dc] := min_outdeg_dicycle Dpos hdeg.
exists [:: c]; split.
- by rewrite /cycle_pack /= dc.
- by apply/forallP=> i; apply/forallP=> j; apply/implyP=> ij;
     move: ij; rewrite (ord1 i) (ord1 j) eqxx.
- by [].
Qed.

(** Sanity: the empty packing is a valid (vertex-disjoint) cycle packing of
    size 0 — the [k = 0] slice of the packing statements is non-vacuous but
    trivial (no degeneracy bug). *)
Lemma empty_pack_ok (D : diGraphType) :
  cycle_pack ([::] : seq (seq D)) /\ vtx_disjoint_pack ([::] : seq (seq D)).
Proof.
split; first by [].
by apply/forallP => -[].
Qed.

(** ** GROUNDING 4 — the Hoàng–Reed intersection-forest clause, right polarity

    We now ground the ACTUAL laminar / intersection-forest conclusion of
    [packing.hoang_reed_statement]
      [forall j, 0 < j -> #|C_j ∩ ⋃_{i<j} C_i| <= 1]
    (the third conjunct in the [exists P] witness), which the existing grounding
    only touched in the weaker "[all dicycle]" form ([hoang_reed_k1_holds]) or
    inlined inside [bermond_thomassen_implies_hoang_reed_weak].

    (4a)  ALWAYS-TRUE DIRECTION.  For ANY vertex-disjoint cycle pack, the laminar
          clause holds unconditionally at every index: each later cycle meets the
          union of the earlier ones in the EMPTY set (cardinality 0 ≤ 1).  This is
          the trivially-true half of the statement's conclusion, valid at every k
          — it decouples the post-processing from the hard cycle-production step.
          (Factors out the argument inlined in the edge theorem
          [bermond_thomassen_implies_hoang_reed_weak] into a reusable standalone.) *)
Lemma vtx_disjoint_pack_laminar (D : diGraphType) (P : seq (seq D)) :
  vtx_disjoint_pack P ->
  forall j : 'I_(size P), (0 < j)%N ->
    (#|[set v : D | (v \in nth [::] P j) &&
         [exists i : 'I_(size P), (i < j)%N && (v \in nth [::] P i)]]| <= 1)%N.
Proof.
move=> vdp j _.
have hE : [set v : D | (v \in nth [::] P j) &&
            [exists i : 'I_(size P), (i < j)%N && (v \in nth [::] P i)]] == set0.
  rewrite -subset0; apply/subsetP => v; rewrite inE.
  move=> /andP[vj /existsP[i /andP[ij vi]]].
  have iNj : i != j by rewrite -val_eqE (ltn_eqF ij).
  have vd : vtx_disjoint (nth [::] P i) (nth [::] P j).
    by move/forallP/(_ i)/forallP/(_ j)/implyP/(_ iNj): vdp.
  rewrite /vtx_disjoint in vd.
  move/hasPn/(_ v vi): vd => /negP nvj.
  by case: (nvj vj).
by rewrite (eqP hE) cards0.
Qed.

(** (4b)  SMALL-INSTANCE, EXACT FORM.  The FULL [hoang_reed_statement] predicate
          (with the real intersection-forest clause, not the weaker [all dicycle]
          conjunct of [hoang_reed_k1_holds]) is TRUE at [k = 1]: min out-degree ≥ 1
          forces one dicycle and the laminar clause is vacuous at size 1 (there is
          no valid index [j] with [0 < j] in ['I_1]).  This pins the settled
          [k = 1] case of Hoàng–Reed TRUE in the actual predicate form, reusing the
          already-proven [min_outdeg_dicycle] and [vtx_disjoint_pack_laminar]. *)
Lemma hoang_reed_k1_exact (D : diGraphType) :
  (0 < #|D|)%N -> (forall v : D, (1 <= outdeg v)%N) ->
  exists P : seq (seq D),
    [/\ cycle_pack P, size P = 1 &
        forall j : 'I_(size P), (0 < j)%N ->
          (#|[set v : D | (v \in nth [::] P j) &&
               [exists i : 'I_(size P), (i < j)%N && (v \in nth [::] P i)]]| <= 1)%N].
Proof.
move=> Dpos hdeg.
have [c dc] := min_outdeg_dicycle Dpos hdeg.
exists [:: c]; split.
- by rewrite /cycle_pack /= dc.
- by [].
- apply: (@vtx_disjoint_pack_laminar D [:: c]).
  by apply/forallP=> a; apply/forallP=> b; apply/implyP=> ab;
     move: ab; rewrite (ord1 a) (ord1 b) eqxx.
Qed.

(** (4c)  TEETH — the intersection-forest guard genuinely CONSTRAINS.

    A right-polarity fragment must be two-sided: the laminar clause is not
    vacuously satisfiable.  We exhibit a concrete cycle pack of TWO dicycles that
    share exactly two vertices, on which the clause is FALSE (cardinality 2 > 1).
    Hence the "settled TRUE" of Hoàng–Reed at [k ≥ 2] is nontrivial: it asks for
    cycles that a general pack need NOT provide.  Concretely, on the 4-vertex
    digraph with arcs 0→1, 1→2, 2→0, 1→3, 3→0, the two triangles
    [C1 = 0,1,2] and [C2 = 0,1,3] both share {0,1}. *)

Inductive V4 := A0 | A1 | A2 | A3.
Definition V4_eq (a b : V4) : bool :=
  match a, b with A0,A0 | A1,A1 | A2,A2 | A3,A3 => true | _,_ => false end.
Lemma V4_eqP : Equality.axiom V4_eq.
Proof. by case=> [] []; constructor. Qed.
HB.instance Definition _ := hasDecEq.Build V4 V4_eqP.
Definition V4_pickle (a : V4) : nat :=
  match a with A0=>0 | A1=>1 | A2=>2 | A3=>3 end.
Definition V4_unpickle (n : nat) : option V4 :=
  match n with 0=>Some A0 | 1=>Some A1 | 2=>Some A2 | 3=>Some A3 | _=>None end.
Lemma V4_pickleK : pcancel V4_pickle V4_unpickle. Proof. by case. Qed.
HB.instance Definition _ := PCanIsCountable V4_pickleK.
Definition V4_enum : seq V4 := [:: A0; A1; A2; A3].
Lemma V4_enumP : Finite.axiom V4_enum. Proof. by case. Qed.
HB.instance Definition _ := isFinite.Build V4 V4_enumP.

Definition arc4_rel (u v : V4) : bool :=
  match u, v with
  | A0, A1 => true
  | A1, A2 => true
  | A2, A0 => true
  | A1, A3 => true
  | A3, A0 => true
  | _, _ => false
  end.
HB.instance Definition _ := HasArc.Build V4 arc4_rel.
Definition D4 : diGraphType := V4.

Definition C1 : seq D4 := [:: A0; A1; A2].
Definition C2 : seq D4 := [:: A0; A1; A3].
Definition Pk : seq (seq D4) := [:: C1; C2].

(** Index 1 (the second cycle [C2]) and index 0 (the first cycle [C1]). *)
Definition jj : 'I_(size Pk) := @Ordinal (size Pk) 1 isT.
Definition ii : 'I_(size Pk) := @Ordinal (size Pk) 0 isT.

Lemma laminar_predicate_discriminating :
  exists (D : diGraphType) (P : seq (seq D)),
    cycle_pack P /\
    ~ (forall j : 'I_(size P), (0 < j)%N ->
        (#|[set v : D | (v \in nth [::] P j) &&
             [exists i : 'I_(size P), (i < j)%N && (v \in nth [::] P i)]]| <= 1)%N).
Proof.
exists D4, Pk; split; first by [].
move=> H.
have card2 : #|[set A0; A1] : {set D4}| = 2%N by rewrite cards2.
have Hge : (2 <= #|[set v : D4 | (v \in nth [::] Pk jj) &&
             [exists i : 'I_(size Pk), (i < jj)%N && (v \in nth [::] Pk i)]]|)%N.
  rewrite -card2; apply: subset_leq_card.
  apply/subsetP => v; rewrite !inE => /orP[/eqP->|/eqP->];
    (apply/andP; split; first by []);
    by apply/existsP; exists ii.
have Hle := H jj isT.
by move: (leq_trans Hge Hle).
Qed.

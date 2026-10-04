(** * Digraph.conjectures.glue_eul_subtype — DEGREE-UNIONING binary amalgam by
      a SUBTYPE / delete-b-redirect carrier, proved EULERIAN-PRESERVING, and the
      full recursive fold over a plane tree with ALL FOUR realises constraints
      (Conjecture 9.2, Aboulker–Aubian–Charbit arXiv:2304.04690 §9)

    This file CLOSES the EULERIAN residual that [glue_tree.v] (pass 4) had to
    carry as a hypothesis.  The committed binary amalgam [two_extremal_glue.vglue]
    lifts arcs through ONE canonical representative
    ([vglue_arc p q := sumarc (repr p) (repr q)]); at the merged class
    [{inl a, inr b}] the representative picks ONE side, so the merged vertex
    inherits only that side's incidences and DROPS the other's.  Hence [vglue] is
    NOT degree-preserving and [glue_tree] is not Eulerian (pass 4 proved loopless +
    digon-free + digon-graph-forest for the full fold but carried Eulerian as a
    hypothesis).

    THE FIX (encoding A — SUBTYPE delete-b-redirect, degree-union DEFINITIONAL).
    We build the degree-unioning amalgam [ueglue D1 D2 a b] on the EXPLICIT finite
    carrier [(D1 + {x : D2 | x != b})%type] — NO quotient.  Vertex [b] of [D2] is
    DELETED; the merged vertex is [inl a], and ALL of [b]'s incidences are
    REDIRECTED onto it.  Concretely [uearc] is:
      - [inl u --> inl v]  := [u --> v]                              (inside D1)
      - [inr w --> inr w'] := [val w --> val w']                     (inside D2 - b)
      - [inl u --> inr w'] := [(u == a) && (b --> val w')]   (merged vertex carries
                                                              b's D2 out-arcs)
      - [inr w --> inl v]  := [(v == a) && (val w --> b)]    (… and b's D2 in-arcs)
    so the merged vertex's incidences are exactly the UNION of [a]'s (in D1) and
    [b]'s (in D2): [outdeg (inl a) = outdeg_{D1} a + outdeg_{D2} b] and likewise for
    in-degrees ([ueglue_outdeg_merged] / [ueglue_indeg_merged]).  Because [D2] is
    loopless there is no arc [b --> b], so NO out/in-arc of [b] is lost in the
    redirection: every other vertex keeps its original degree
    ([ueglue_outdeg_inr] / [ueglue_indeg_inr] / [ueglue_*_inl_ne]).

    WHAT IS PROVED ([Qed], no [Admitted]/[Axiom]):

    - §0 — two generic finite-cardinality helpers: [card_set_sum] (split a set over
      a sum carrier into its [inl]/[inr] parts) and [card_sig_pred] (count a
      predicate over a subtype by lifting to the base, conjoined with the subtype
      predicate).

    - §1 — the concrete carrier [ueglue] (a genuine [diGraphType], no quotient), its
      arc-computation lemma [ueglue_arcE], and the two structural preservations
      [ueglue_loopless] / [ueglue_digonfree].

    - §2 — the per-vertex degree formulas and EULERIAN-PRESERVATION
      [ueglue_Eulerian]: if [D1] and [D2] are Eulerian (and [D2] loopless, which
      every realisation is) then [ueglue] is Eulerian.  This is THE key new content
      the committed [vglue] could not deliver.  (The two balance hypotheses
      [indeg_{D1} a = outdeg_{D1} a] and [indeg_{D2} b = outdeg_{D2} b] of the
      assignment are exactly what [Eulerian D1] / [Eulerian D2] supply at [a] / [b],
      so they are not separate hypotheses.)

    - §3 — the recursive fold [glue_tree_e : ptree -> eadigraph] over [ptree], built
      from the degree-unioning binary primitive [eglue_one], and the FOUR invariants
      proved by induction ([ptree_ind']): [glue_tree_e_loopless],
      [glue_tree_e_digonfree], [glue_tree_e_digonG_forest] (via the committed
      [two_extremal_glue.digonfree_forest]) and — the residual now closed —
      [glue_tree_e_Eulerian].  The base block is the committed rim [di_cycle 3]
      (loopless + digon-free + Eulerian).

    - §4 — a fully-concrete [realises] witness [realises_E] carrying all four side
      conditions, PROVED to satisfy the three faithful constraints
      [realises_loopless] / [realises_Eulerian] / [realises_digonG_forest] of
      [two_extremal_hajos], and the UNCONDITIONAL theorem [glue_tree_e_realises_E]:
      EVERY [glue_tree_e t] realises [t] — no Eulerian hypothesis carried.  Hence the
      tree-join generator is inhabited and [conj_9_2_concrete realises_E] is
      non-vacuous; the [conj_9_2] / Conjecture-P / 3-connected-wheel edges chain
      through the committed [two_extremal_hajos] machinery.

    Every theorem below is [Qed]-closed; nothing is [Admitted] or [Axiom]ed. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From mathcomp Require Import generic_quotient.
From Digraph Require Import prelude interop_graph_theory digraph oriented tournament.
From Digraph Require Import dipath strong dichromatic classic_core two_extremal.
From Digraph Require Import two_extremal_hajos two_extremal_glue glue_tree.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope quotient_scope.

(** ** §0 — generic finite-cardinality helpers *)

(** Split a set over a sum carrier into its [inl]-part and [inr]-part. *)
Lemma card_set_sum (A B : finType) (Q : pred (A + B)) :
  #|[set x | Q x]| = #|[set x : A | Q (inl x)]| + #|[set x : B | Q (inr x)]|.
Proof.
pose L : {set (A + B)%type} := [set x | if x is inl _ then true else false].
rewrite -(cardsID L [set x | Q x]).
congr (_ + _).
- rewrite -(card_imset _ (@inl_inj A B)); apply: eq_card => x.
  rewrite !inE; case: x => [u|u] /=; rewrite ?andbT ?andbF //;
    apply/idP/imsetP => [Qu|[v]]; rewrite ?inE.
  + by exists u; rewrite ?inE.
  + by move=> Qv [->].
  + by [].
  + by move=> _.
- rewrite -(card_imset _ (@inr_inj A B)); apply: eq_card => x.
  rewrite !inE; case: x => [u|u] /=; rewrite ?andbF ?andbT //;
    apply/idP/imsetP => [Qu|[v]]; rewrite ?inE.
  + by [].
  + by move=> _.
  + by exists u; rewrite ?inE.
  + by move=> Qv [->].
Qed.

(** Count a predicate over a subtype [{x : T | P x}] by lifting to the base [T],
    conjoined with the subtype predicate. *)
Lemma card_sig_pred (T : finType) (P : pred T) (Q : pred T) :
  #|[set w : {x : T | P x} | Q (val w)]| = #|[set w : T | P w & Q w]|.
Proof.
rewrite -(card_imset _ val_inj); apply: eq_card => z.
rewrite inE; apply/imsetP/idP => [[w]|].
- by rewrite inE => Qw ->; rewrite (valP w) Qw.
- move=> /andP[Pz Qz].
  by exists (exist _ z Pz); rewrite ?inE.
Qed.

(** ** §1 — the degree-unioning binary amalgam [ueglue] (subtype/delete-b-redirect) *)

Section UEGlue.
Variables (D1 D2 : diGraphType).
Variables (a : D1) (b : D2).

(** The deleted-[b] carrier: [D2] minus [b]. *)
Definition D2mb : finType := {x : D2 | x != b}.

(** The explicit finite carrier — [D1] disjoint-union ([D2] minus [b]). *)
Definition uesum : Type := (D1 + D2mb)%type.
HB.instance Definition _ := Finite.on uesum.

(** The arc relation: [b]'s incidences are redirected onto the merged vertex
    [inl a] (standalone [Definition] for the match — HB gotcha). *)
Definition uearc (x y : uesum) : bool :=
  match x, y with
  | inl u, inl v => u --> v
  | inr w, inr w' => (val w) --> (val w')
  | inl u, inr w' => (u == a) && (b --> val w')
  | inr w, inl v => (v == a) && (val w --> b)
  end.
HB.instance Definition _ := HasArc.Build uesum uearc.

(** The degree-unioning binary glue [D1 ⊔_{a=b} D2] as a [diGraphType]. *)
Definition ueglue : diGraphType := uesum.

Lemma ueglue_arcE (x y : ueglue) : (x --> y) = uearc x y.
Proof. by []. Qed.

(** The merged vertex (inherits BOTH [a]'s and [b]'s incidences). *)
Definition uemerged : ueglue := inl a.

(** A self-loop would live entirely inside [D1] or inside [D2]. *)
Lemma ueglue_loopless :
  loopless D1 -> loopless D2 -> loopless ueglue.
Proof.
move=> l1 l2 x; rewrite ueglue_arcE /uearc.
by case: x => [u|w] /=; [exact: l1 | exact: l2].
Qed.

(** A digon would live entirely inside [D1] or [D2] (cross-arcs only at the
    merged vertex, where an antiparallel pair is a [b]–[w] digon of [D2]). *)
Lemma ueglue_digonfree :
  (forall u v : D1, ~~ ((u --> v) && (v --> u))) ->
  (forall u v : D2, ~~ ((u --> v) && (v --> u))) ->
  (forall x y : ueglue, ~~ ((x --> y) && (y --> x))).
Proof.
move=> df1 df2 x y; rewrite !ueglue_arcE /uearc.
case: x => [u|w]; case: y => [v|w'] /=.
- exact: df1.
- apply/negP => /andP[/andP[_ Hbw] /andP[_ Hwb]].
  by move: (df2 b (val w')); rewrite Hbw Hwb.
- apply/negP => /andP[/andP[_ Hwb] /andP[_ Hbw]].
  by move: (df2 (val w) b); rewrite Hwb Hbw.
- exact: df2.
Qed.

(** ** §2 — per-vertex degree formulas and EULERIAN-PRESERVATION *)

(** Generic out-degree split for [ueglue]: count the [inl]- and [inr]-neighbours
    separately. *)
Lemma ueglue_outdeg_split (z : ueglue) :
  outdeg z = #|[set v : D1 | uearc z (inl v)]|
           + #|[set w : D2mb | uearc z (inr w)]|.
Proof.
rewrite /outdeg.
rewrite (card_set_sum (A:=D1) (B:=D2mb) (fun w => z --> w)).
by congr (_ + _); apply: eq_card => t; rewrite !inE ueglue_arcE.
Qed.

(** Generic in-degree split for [ueglue]. *)
Lemma ueglue_indeg_split (z : ueglue) :
  indeg z = #|[set v : D1 | uearc (inl v) z]|
          + #|[set w : D2mb | uearc (inr w) z]|.
Proof.
rewrite /indeg /Nin.
rewrite (card_set_sum (A:=D1) (B:=D2mb) (fun u : ueglue => u --> z)).
by congr (_ + _); apply: eq_card => t; rewrite !inE ueglue_arcE.
Qed.

(** A [D2]-vertex (other than [b]) keeps its [D2] out-degree: its redirected arc
    to [b] is still counted (now landing on the merged vertex). *)
Lemma ueglue_outdeg_inr (w0 : D2mb) :
  outdeg (inr w0 : ueglue) = outdeg (val w0 : D2).
Proof.
rewrite ueglue_outdeg_split.
rewrite (eq_card (B := [set w : D2mb | val w0 --> val w])); last first.
  by move=> w; rewrite !inE.
rewrite (@card_sig_pred D2 (fun x : D2 => x != b) (fun z => val w0 --> z)).
have inlcard : #|[set v : D1 | uearc (inr w0) (inl v)]| = (val w0 --> b : nat).
  rewrite /uearc /=.
  case E: (val w0 --> b).
    rewrite (_ : [set v : D1 | (v == a) && true] = [set a]) ?cards1 //.
    by apply/setP => v; rewrite !inE andbT.
  rewrite (_ : [set v : D1 | (v == a) && false] = set0) ?cards0 //.
  by apply/setP => v; rewrite !inE andbF.
rewrite inlcard.
rewrite /outdeg.
rewrite -(cardsID [set b] [set w : D2 | val w0 --> w]).
congr (_ + _).
- rewrite (_ : _ :&: _ = if val w0 --> b then [set b] else set0).
    by case: (val w0 --> b); rewrite ?cards1 ?cards0.
  apply/setP => v; rewrite !inE.
  case: (altP (v =P b)) => [->|Nvb].
    by rewrite andbT; case: (val w0 --> b); rewrite ?inE ?eqxx.
  rewrite andbF; case: (val w0 --> b); rewrite ?inE //.
  by apply/esym/negbTE.
- by apply: eq_card => v; rewrite !inE andbC.
Qed.

(** A [D2]-vertex (other than [b]) keeps its [D2] in-degree. *)
Lemma ueglue_indeg_inr (w0 : D2mb) :
  indeg (inr w0 : ueglue) = indeg (val w0 : D2).
Proof.
rewrite ueglue_indeg_split.
rewrite (eq_card (B := [set w : D2mb | val w --> val w0])); last first.
  by move=> w; rewrite !inE.
rewrite (@card_sig_pred D2 (fun x : D2 => x != b) (fun z => z --> val w0)).
have inlcard : #|[set v : D1 | uearc (inl v) (inr w0)]| = (b --> val w0 : nat).
  rewrite /uearc /=.
  case E: (b --> val w0).
    rewrite (_ : [set v : D1 | (v == a) && true] = [set a]) ?cards1 //.
    by apply/setP => v; rewrite !inE andbT.
  rewrite (_ : [set v : D1 | (v == a) && false] = set0) ?cards0 //.
  by apply/setP => v; rewrite !inE andbF.
rewrite inlcard.
rewrite /indeg /Nin.
rewrite -(cardsID [set b] [set w : D2 | w --> val w0]).
congr (_ + _).
- rewrite (_ : _ :&: _ = if b --> val w0 then [set b] else set0).
    by case: (b --> val w0); rewrite ?cards1 ?cards0.
  apply/setP => v; rewrite !inE.
  case: (altP (v =P b)) => [->|Nvb].
    by rewrite andbT; case: (b --> val w0); rewrite ?inE ?eqxx.
  rewrite andbF; case: (b --> val w0); rewrite ?inE //.
  by apply/esym/negbTE.
- by apply: eq_card => v; rewrite !inE andbC.
Qed.

(** A non-merged [D1]-vertex ([u != a]) keeps its [D1] out-degree (no cross-arcs
    leave it). *)
Lemma ueglue_outdeg_inl_ne (u : D1) : u != a ->
  outdeg (inl u : ueglue) = outdeg (u : D1).
Proof.
move=> Nua; rewrite ueglue_outdeg_split.
rewrite (_ : #|[set w : D2mb | uearc (inl u) (inr w)]| = 0); last first.
  apply/eqP; rewrite cards_eq0; apply/eqP/setP => w.
  by rewrite !inE /uearc /= (negbTE Nua).
by rewrite addn0; apply: eq_card => v; rewrite !inE.
Qed.

(** A non-merged [D1]-vertex ([u != a]) keeps its [D1] in-degree. *)
Lemma ueglue_indeg_inl_ne (u : D1) : u != a ->
  indeg (inl u : ueglue) = indeg (u : D1).
Proof.
move=> Nua; rewrite ueglue_indeg_split.
rewrite (_ : #|[set w : D2mb | uearc (inr w) (inl u)]| = 0); last first.
  apply/eqP; rewrite cards_eq0; apply/eqP/setP => w.
  by rewrite !inE /uearc /= (negbTE Nua).
by rewrite addn0; rewrite /indeg /Nin; apply: eq_card => v; rewrite !inE.
Qed.

(** THE DEGREE-UNION at the merged vertex (out): [outdeg (inl a) = outdeg_{D1} a +
    outdeg_{D2} b].  [loopless D2] (no arc [b --> b]) ensures [b]'s out-arcs are not
    lost in the redirection. *)
Lemma ueglue_outdeg_merged :
  loopless D2 ->
  outdeg (inl a : ueglue) = outdeg (a : D1) + outdeg (b : D2).
Proof.
move=> l2; rewrite ueglue_outdeg_split.
congr (_ + _).
rewrite (eq_card (B := [set w : D2mb | b --> val w])); last first.
  by move=> w; rewrite !inE /uearc /= eqxx.
rewrite (@card_sig_pred D2 (fun x : D2 => x != b) (fun z => b --> z)).
rewrite /outdeg; apply: eq_card => v; rewrite !inE.
case: (altP (v =P b)) => [->|//].
by rewrite (l2 b) andbF.
Qed.

(** THE DEGREE-UNION at the merged vertex (in): [indeg (inl a) = indeg_{D1} a +
    indeg_{D2} b]. *)
Lemma ueglue_indeg_merged :
  loopless D2 ->
  indeg (inl a : ueglue) = indeg (a : D1) + indeg (b : D2).
Proof.
move=> l2; rewrite ueglue_indeg_split.
congr (_ + _).
rewrite (eq_card (B := [set w : D2mb | val w --> b])); last first.
  by move=> w; rewrite !inE /uearc /= eqxx.
rewrite (@card_sig_pred D2 (fun x : D2 => x != b) (fun z => z --> b)).
rewrite /indeg /Nin; apply: eq_card => v; rewrite !inE.
case: (altP (v =P b)) => [->|//].
by rewrite (l2 b) andbF.
Qed.

(** EULERIAN-PRESERVATION — THE KEY NEW CONTENT.  At every non-merged vertex the
    degree is unchanged; at the merged vertex [inl a] the in/out-degrees are the
    SUMS of [a]'s (in [D1]) and [b]'s (in [D2]), so both balance.  [Eulerian D1] /
    [Eulerian D2] supply [indeg a = outdeg a] and [indeg b = outdeg b] at the two
    interface vertices. *)
Lemma ueglue_Eulerian :
  loopless D2 -> Eulerian D1 -> Eulerian D2 -> Eulerian ueglue.
Proof.
move=> l2 e1 e2 z; change (indeg z = outdeg z).
have e1' : forall v : D1, indeg v = outdeg v := e1.
have e2' : forall v : D2, indeg v = outdeg v := e2.
case: z => [u|w].
- case: (altP (u =P a)) => [->|Nua].
  + rewrite ueglue_indeg_merged // ueglue_outdeg_merged //.
    by rewrite (e1' a) (e2' b).
  + by rewrite ueglue_indeg_inl_ne // ueglue_outdeg_inl_ne // (e1' u).
- by rewrite ueglue_indeg_inr ueglue_outdeg_inr (e2' (val w)).
Qed.

End UEGlue.

(** ** §3 — the degree-unioning recursive fold [glue_tree_e] over a plane tree

    An [eadigraph] is a [diGraphType] with a designated ANCHOR vertex (the interface
    vertex by which the parent glues this block).  [eglue_one acc child] amalgamates
    [child] onto [acc] across their two anchors via the degree-unioning [ueglue],
    and keeps [acc]'s anchor (which survives as [inl (ad_anchor acc)]) as the new
    anchor.  [glue_tree_e] folds [eglue_one] over a node's children in PLANE order,
    starting from the base block [eleaf_block := di_cycle 3] at each leaf. *)

Record eadigraph := EADigraph { ead_car :> diGraphType ; ead_anchor : ead_car }.
Arguments EADigraph : clear implicits.

(** Base block at every leaf: the rim triangle [di_cycle 3], anchored at [ord0]. *)
Definition eleaf_block : eadigraph := EADigraph (di_cycle 3) (@ord0 2).

(** Glue [child] onto [acc] at their anchors by degree-union; the new anchor is the
    surviving image [inl (ad_anchor acc)] of [acc]'s anchor. *)
Definition eglue_one (acc child : eadigraph) : eadigraph :=
  EADigraph (ueglue (ead_anchor acc) (ead_anchor child))
            (inl (ead_anchor acc)).

(** The recursive fold: amalgamate every child subtree onto the leaf base block,
    in plane order. *)
Fixpoint glue_tree_e (t : ptree) : eadigraph :=
  foldr (fun p acc => eglue_one acc (glue_tree_e p.2)) eleaf_block (pt_children t).

(** A bare leaf assembles to the base block. *)
Lemma glue_tree_e_leaf t : pt_is_leaf t -> glue_tree_e t = eleaf_block.
Proof. by case: t => ch; rewrite /pt_is_leaf /= => /nilP ->. Qed.

(** Base-block facts (committed [di_cycle_*]). *)
Lemma eleaf_loopless : loopless eleaf_block.
Proof. by apply: di_cycle_loopless. Qed.

Lemma eleaf_digonfree : forall u v : eleaf_block, ~~ ((u --> v) && (v --> u)).
Proof. by apply: di_cycle_digonfree. Qed.

Lemma eleaf_Eulerian : Eulerian eleaf_block.
Proof. by apply: di_cycle_Eulerian. Qed.

(** [eglue_one] preserves looplessness, digon-freeness and Eulerianness (the §1/§2
    binary lemmas, on the anchored wrapper). *)
Lemma eglue_one_loopless (acc child : eadigraph) :
  loopless acc -> loopless child -> loopless (eglue_one acc child).
Proof. by move=> ? ?; apply: ueglue_loopless. Qed.

Lemma eglue_one_digonfree (acc child : eadigraph) :
  (forall u v : acc, ~~ ((u --> v) && (v --> u))) ->
  (forall u v : child, ~~ ((u --> v) && (v --> u))) ->
  (forall u v : eglue_one acc child, ~~ ((u --> v) && (v --> u))).
Proof. by move=> ? ?; apply: ueglue_digonfree. Qed.

Lemma eglue_one_Eulerian (acc child : eadigraph) :
  loopless child -> Eulerian acc -> Eulerian child ->
  Eulerian (eglue_one acc child).
Proof. by move=> ? ? ?; apply: ueglue_Eulerian. Qed.

(** INVARIANT 1 — the whole recursive assembly is loopless. *)
Lemma glue_tree_e_loopless (t : ptree) : loopless (glue_tree_e t).
Proof.
elim/ptree_ind': t => ch IH.
rewrite /glue_tree_e -/glue_tree_e /=.
elim: ch IH => [_ /=|[l p] s IHs] /=.
- exact: eleaf_loopless.
- move=> [Hp Hrest]; apply: eglue_one_loopless; [exact: IHs | exact: Hp].
Qed.

(** INVARIANT 2 — the whole recursive assembly is digon-free. *)
Lemma glue_tree_e_digonfree (t : ptree) :
  forall u v : glue_tree_e t, ~~ ((u --> v) && (v --> u)).
Proof.
elim/ptree_ind': t => ch IH.
rewrite /glue_tree_e -/glue_tree_e /=.
elim: ch IH => [_ /=|[l p] s IHs] /=.
- exact: eleaf_digonfree.
- move=> [Hp Hrest]; apply: eglue_one_digonfree; [exact: IHs | exact: Hp].
Qed.

(** INVARIANT 3 (THE RESIDUAL, NOW CLOSED) — the whole recursive assembly is
    EULERIAN.  Folds [eglue_one_Eulerian] over the children; each step needs the
    child loopless ([glue_tree_e_loopless]) to know [b]'s arcs are not lost. *)
Lemma glue_tree_e_Eulerian (t : ptree) : Eulerian (glue_tree_e t).
Proof.
elim/ptree_ind': t => ch IH.
rewrite /glue_tree_e -/glue_tree_e /=.
elim: ch IH => [_ /=|[l p] s IHs] /=.
- exact: eleaf_Eulerian.
- move=> [Hp Hrest]; apply: eglue_one_Eulerian.
  + exact: glue_tree_e_loopless.
  + exact: IHs.
  + exact: Hp.
Qed.

(** INVARIANT 4 (THE HARD ONE) — the digon graph of the whole assembly is a FOREST,
    for any chosen looplessness witness.  Via the committed general lemma
    [two_extremal_glue.digonfree_forest] applied to invariant 2. *)
Lemma glue_tree_e_digonG_forest (t : ptree) (llD : loopless (glue_tree_e t)) :
  is_forest [set: digonG llD].
Proof. by apply: digonfree_forest; exact: glue_tree_e_digonfree. Qed.

(** A packaged summary: ALL FOUR invariants of the degree-unioning fold, proved
    UNCONDITIONALLY (no carried Eulerian hypothesis). *)
Theorem glue_tree_e_invariants (t : ptree) (llD : loopless (glue_tree_e t)) :
  [/\ loopless (glue_tree_e t),
      (forall u v : glue_tree_e t, ~~ ((u --> v) && (v --> u))),
      Eulerian (glue_tree_e t)
    & is_forest [set: digonG llD]].
Proof.
split.
- exact: glue_tree_e_loopless.
- exact: glue_tree_e_digonfree.
- exact: glue_tree_e_Eulerian.
- exact: glue_tree_e_digonG_forest.
Qed.

(** ** §4 — fully-concrete [realises], membership and the Conjecture-9.2 edges

    [realises_E t D] records (faithfully) that [D] is loopless, digon-free, Eulerian
    and digon-forest — the four Def-9.1 realisation side conditions.  The three
    [two_extremal_hajos] faithful constraints are proved for it, and EVERY assembly
    [glue_tree_e t] realises [t] WITH NO HYPOTHESIS (all four invariants are now
    unconditional). *)

(** The concrete witness realisation relation (all four side conditions). *)
Definition realises_E (t : ptree) (D : diGraphType) : Prop :=
  exists llD : loopless D,
    [/\ (forall u v : D, ~~ ((u --> v) && (v --> u))),
        Eulerian D
      & is_forest [set: digonG llD]].

(** [realises_E] satisfies [realises_loopless]. *)
Theorem realises_E_loopless : realises_loopless realises_E.
Proof. by move=> t D [llD _]. Qed.

(** [realises_E] satisfies [realises_Eulerian]. *)
Theorem realises_E_Eulerian : realises_Eulerian realises_E.
Proof. by move=> t D [llD [_ eul _]]. Qed.

(** [realises_E] satisfies [realises_digonG_forest]. *)
Theorem realises_E_digonG_forest : realises_digonG_forest realises_E.
Proof.
move=> t D llD [llD' [df _ _]].
exact: digonfree_forest.
Qed.

(** THE MAIN RESULT — every degree-unioning assembly realises its tree
    UNCONDITIONALLY (all four constraints, no carried Eulerian hypothesis). *)
Theorem glue_tree_e_realises_E (t : ptree) : realises_E t (glue_tree_e t).
Proof.
exists (@glue_tree_e_loopless t); split.
- exact: glue_tree_e_digonfree.
- exact: glue_tree_e_Eulerian.
- exact: glue_tree_e_digonG_forest.
Qed.

(** For any LEGAL Def-9.1 datum [t], [glue_tree_e t] is a 2-Hajós tree-join
    realisation under [realises_E] — UNCONDITIONALLY. *)
Theorem glue_tree_e_is_treejoin (t : ptree) :
  is_two_hajos_data (in_H2_concrete realises_E) t ->
  is_two_hajos_treejoin (in_H2_concrete realises_E) realises_E (glue_tree_e t).
Proof.
by move=> hd; exists t; split; [exact: hd | exact: glue_tree_e_realises_E].
Qed.

(** Hence membership of the concrete class via the tree-join constructor, for any
    legal datum — UNCONDITIONALLY. *)
Theorem glue_tree_e_in_H2 (t : ptree) :
  is_two_hajos_data (in_H2_concrete realises_E) t ->
  in_H2_concrete realises_E (glue_tree_e t).
Proof.
move=> hd.
by apply: (inH2_treejoin (t := t)); [exact: hd | exact: glue_tree_e_realises_E].
Qed.

(** [realises_E] is INHABITED: the canonical legal datum [canon_tree] is realised by
    its degree-unioning assembly — UNCONDITIONALLY (Eulerian no longer hypothesised). *)
Theorem realises_E_inhabited : realises_E canon_tree (glue_tree_e canon_tree).
Proof. exact: glue_tree_e_realises_E. Qed.

(** The tree-join generator of the concrete [H₂] is non-vacuous at [realises_E]. *)
Theorem is_two_hajos_treejoin_E_nonvacuous :
  exists D : diGraphType,
    is_two_hajos_treejoin (in_H2_concrete realises_E) realises_E D.
Proof.
exists (glue_tree_e canon_tree); exists canon_tree; split.
- exact: canon_legal.
- exact: glue_tree_e_realises_E.
Qed.

(** *** The fully-instantiated concrete Conjecture 9.2 and the implication edges.

    [conj_9_2_glued_e] is [conj_9_2_concrete] at the concrete witness [realises_E].
    The [two_extremal_hajos] relative edges chain at this instance (RELATIVE:
    nothing is resolved; they show the glued statement is at least as strong as the
    committed targets). *)

Definition conj_9_2_glued_e : Prop := conj_9_2_concrete realises_E.

Theorem conj_9_2_glued_e_implies_conj_9_2 :
  conj_9_2_glued_e -> conj_9_2 (in_H2_concrete realises_E).
Proof. exact: conj_9_2_concrete_implies_conj_9_2. Qed.

Theorem conj_9_2_glued_e_implies_conjecture_P :
  conj_9_2_glued_e ->
  (forall (D : diGraphType) (llD : loopless D),
     in_H2_concrete realises_E D -> planar_sg (underlyingG llD)) ->
  conjecture_P.
Proof. exact: conj_9_2_concrete_implies_conjecture_P. Qed.

Theorem conj_9_2_glued_e_implies_three_connected_gw
    (generalised_wheel : diGraphType -> Prop) :
  conj_9_2_glued_e ->
  (forall (D : diGraphType) (llD : loopless D),
     in_H2_concrete realises_E D ->
     three_connected_sg (underlyingG llD) -> generalised_wheel D) ->
  three_connected_generalised_wheel generalised_wheel.
Proof. exact: conj_9_2_concrete_implies_three_connected_gw. Qed.

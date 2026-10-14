(** * Digraph.foundations.neighbourhoods — out-, in- and second out-neighbourhoods (family directed-neighbourhood)

    For a vertex [v] of a finite digraph, [Nout v] is the out-neighbourhood [[set w | v --> w]],
    [Nin v] is the in-neighbourhood [[set u | u --> v]], and [Nout2 v] is the second
    out-neighbourhood: the vertices at directed distance exactly two, i.e. out-neighbours of an
    out-neighbour of [v] that are neither [v] itself nor out-neighbours of [v].  The three bodies
    are verbatim those of [Digraph.conjectures.classic_core] (contract
    master-directed-neighbourhood-contract.md, option C).  No degree is defined here:
    [Digraph.core.oriented.outdeg] and [Digraph.foundations.degree_balance.indeg] stay the
    canonical degrees, and [degree_balance] states the bridges [outdeg v = #|Nout v|] and
    [indeg v = #|Nin v|].

    Upstream audit (2026-10-08; MathComp 2.5.0, coq-graph-theory 0.9.7, Digraph core).
    coq-graph-theory's [open_neigh] ([GraphTheory.core.digraph]) is the out-neighbourhood
    [[set v | u -- v]] of its record [diGraph]; it has no in-neighbourhood, no second
    neighbourhood and no degree.  The bridge [open_neigh (to_GT D) u = Nout u] would hold by
    conversion; it is not stated here, so this module imports [prelude] and [core/digraph] only.
    The Digraph core has the tournament-only [N_out]/[N_in] ([core/tournament.v]); the other
    copies are conjecture-local.

    Specification, every clause proved below:
    - membership: [NoutE] and [NinE] with the views [NoutP] and [NinP]; [Nout2E] and the view
      [Nout2P]; the introduction rule [Nout2I];
    - the distance-two exclusion: [Nout2 v] contains neither [v] nor any out-neighbour of [v]
      ([Nout2_neq], [self_notin_Nout2], [Nout2_notin_Nout], [arc_notin_Nout2],
      [disjoint_Nout2_Nout], [Nout2_subC]), even when a loop or a digon gives a walk of length
      two back to them;
    - loops count: [v] is its own out-neighbour exactly when it is its own in-neighbour, exactly
      when [v --> v] ([loop_Nout_Nin]); digons are allowed: the partner of a digon is both an out-
      and an in-neighbour, and the return walk of length two does not put [v] in [Nout2 v]
      ([digon_Nout_Nin], [digon_notin_Nout2]);
    - an arcless digraph has empty neighbourhoods ([arcless_Nout], [arcless_Nin],
      [arcless_Nout2]); no connectivity, looplessness or inhabited-carrier premise is assumed;
    - the converse digraph swaps [Nout] and [Nin] ([Nout_converse], [Nin_converse]). *)

From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Neighbourhoods.
Variable D : diGraphType.
Implicit Types (v w : D).

Definition Nout v : {set D} := [set w | v --> w].
Definition Nin  v : {set D} := [set u | u --> v].

(** Second out-neighbourhood: vertices at directed distance exactly two from [v]
    (an out-neighbour of an out-neighbour, distinct from [v] and not itself an
    out-neighbour). *)
Definition Nout2 v : {set D} :=
  [set w | [&& w != v, w \notin Nout v & [exists u, (u \in Nout v) && (u --> w)]]].

(** ** Membership *)

Lemma NoutE v w : (w \in Nout v) = (v --> w).
Proof. by rewrite inE. Qed.

Lemma NinE v (u : D) : (u \in Nin v) = (u --> v).
Proof. by rewrite inE. Qed.

Lemma NoutP v w : reflect (v --> w) (w \in Nout v).
Proof. by rewrite NoutE; apply: idP. Qed.

Lemma NinP v (u : D) : reflect (u --> v) (u \in Nin v).
Proof. by rewrite NinE; apply: idP. Qed.

Lemma Nout2E v w :
  (w \in Nout2 v) = [&& w != v, ~~ (v --> w) & [exists u, (v --> u) && (u --> w)]].
Proof.
rewrite [w \in Nout2 v]inE NoutE; congr [&& _, _ & _].
by apply: eq_existsb => u; rewrite NoutE.
Qed.

Lemma Nout2P v w :
  reflect [/\ w != v, ~~ (v --> w) & exists2 u, v --> u & u --> w] (w \in Nout2 v).
Proof.
rewrite Nout2E; apply: (iffP and3P) => -[wv nvw].
  by case/existsP=> u /andP[vu uw]; split=> //; exists u.
by case=> u vu uw; split=> //; apply/existsP; exists u; rewrite vu.
Qed.

Lemma Nout2I v (u : D) w : v --> u -> u --> w -> w != v -> ~~ (v --> w) -> w \in Nout2 v.
Proof. by move=> vu uw wv nvw; apply/Nout2P; split=> //; exists u. Qed.

(** ** The distance-two exclusion *)

Lemma Nout2_neq v w : w \in Nout2 v -> w != v.
Proof. by case/Nout2P. Qed.

Lemma self_notin_Nout2 v : v \notin Nout2 v.
Proof. by apply/negP=> /Nout2_neq; rewrite eqxx. Qed.

Lemma Nout2_notin_Nout v w : w \in Nout2 v -> w \notin Nout v.
Proof. by case/Nout2P=> _ nvw _; rewrite NoutE. Qed.

Lemma arc_notin_Nout2 v w : v --> w -> w \notin Nout2 v.
Proof. by move=> vw; apply/negP=> /Nout2_notin_Nout; rewrite NoutE vw. Qed.

Lemma disjoint_Nout2_Nout v : [disjoint Nout2 v & Nout v].
Proof.
rewrite disjoints_subset; apply/subsetP=> w w2.
by rewrite in_setC; apply: Nout2_notin_Nout.
Qed.

Lemma Nout2_subC v : Nout2 v \subset ~: (v |: Nout v).
Proof.
apply/subsetP=> w w2; rewrite in_setC in_setU1 negb_or.
by rewrite (Nout2_neq w2) (Nout2_notin_Nout w2).
Qed.

(** ** Corners: loops, digons, arcless digraphs *)

(** A loop makes [v] its own out- and in-neighbour at once. *)
Lemma loop_Nout_Nin v : (v \in Nout v) = (v \in Nin v).
Proof. by rewrite NoutE NinE. Qed.

(** The partner of a digon is both an out- and an in-neighbour ... *)
Lemma digon_Nout_Nin v w : v --> w -> w --> v -> (w \in Nout v) && (w \in Nin v).
Proof. by move=> vw wv; rewrite NoutE NinE vw wv. Qed.

(** ... and the return walk [v --> w --> v] does not put [v] at distance two. *)
Lemma digon_notin_Nout2 v w : v --> w -> w --> v -> v \notin Nout2 v.
Proof. by move=> _ _; apply: self_notin_Nout2. Qed.

Section Arcless.
Hypothesis none : forall x y : D, ~~ (x --> y).

Lemma arcless_Nout v : Nout v = set0.
Proof. by apply/setP=> w; rewrite NoutE in_set0 (negbTE (none _ _)). Qed.

Lemma arcless_Nin v : Nin v = set0.
Proof. by apply/setP=> u; rewrite NinE in_set0 (negbTE (none _ _)). Qed.

Lemma arcless_Nout2 v : Nout2 v = set0.
Proof.
apply/setP=> w; rewrite in_set0; apply/negP=> /Nout2P[_ _ [u vu _]].
by move: (none v u); rewrite vu.
Qed.

End Arcless.

End Neighbourhoods.

(** ** The converse digraph swaps the two neighbourhoods *)

Lemma Nout_converse (D : diGraphType) (v : D) : @Nout (converse D) v = Nin v.
Proof. by []. Qed.

Lemma Nin_converse (D : diGraphType) (v : D) : @Nin (converse D) v = Nout v.
Proof. by []. Qed.

(** * Digraph.conjectures.grounding_classic_core — faithfulness grounding for classic_core

    GROUNDING (not new mathematics): prove small, KNOWN textbook facts that the new
    primitives in [classic_core.v] (Nout / Nin / indeg / Nout2 / diregular) and the
    open-conjecture statements (Seymour, Caccetta–Häggkvist) must satisfy if the
    definitions are faithful encodings.

    Facts grounded here:
      - [tournament_indeg_outdeg]  : in a tournament, indeg v + outdeg v = #|T| - 1
                                     (the textbook tournament degree identity: every other
                                      vertex is exactly one of an in- or out-neighbour).
      - [Nout_is_outdeg]           : outdeg v = #|Nout v| (Nout matches the lib outdeg).
      - [C3_diregular1]            : the directed triangle is 1-diregular.
      - [TT_has_source]/[TT_has_sink] : TT n.+1 has a vertex of out-degree n (source) and
                                     a vertex of in-degree n (sink).
      - [Nout2_disjoint_self]/[Nout2_disjoint_Nout] : Nout2 v avoids v and Nout v
                                     (sanity of the second-out-neighbourhood definition).
      - [C3_has_seymour_vertex]    : C3 has a vertex v with outdeg v <= #|Nout2 v|
                                     (the SNC conclusion is SATISFIABLE; Fisher proved SNC
                                      for tournaments).
      - red-flag falsification probes for the open statements (see the comments and
                                     [seymour_nonvacuous] / [ch_triangle_nonvacuous]). *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude digraph oriented dipath strong tournament.
From Digraph Require Import classic_core.
Set SsrOldRewriteGoalsOrder.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** [Nout] / [Nin] match the library degrees *)

Section MatchLib.
Variable D : diGraphType.
Implicit Types v : D.

(** [outdeg] (lib, oriented.v) is literally [#|Nout v|]. *)
Lemma Nout_is_outdeg v : outdeg v = #|Nout v|.
Proof. by []. Qed.

(** [indeg] is [#|Nin v|] by definition. *)
Lemma indeg_is_card v : indeg v = #|Nin v|.
Proof. by []. Qed.

End MatchLib.

(** ** The tournament degree identity: indeg v + outdeg v = n - 1.

    Grounds: in a tournament, every vertex other than [v] is joined to [v] by exactly one
    arc, in one direction; so the out- and in-neighbourhoods partition [set~ v]. *)

Section TournamentDegrees.
Variable T : tournament.
Implicit Types v : T.

(** [Nout]/[Nin] (classic_core, digraph level) coincide with [N_out]/[N_in] (tournament). *)
Lemma Nout_N_out v : Nout v = N_out v.
Proof. by apply/setP=> w; rewrite !inE. Qed.

Lemma Nin_N_in v : Nin v = N_in v.
Proof. by apply/setP=> w; rewrite !inE. Qed.

Lemma outdeg_card_Nout v : outdeg v = #|Nout v|.
Proof. by []. Qed.

Lemma tournament_indeg_outdeg v : indeg v + outdeg v = #|T|.-1.
Proof.
have [E D'] := N_out_in_partition v.
have key : #|[set~ v]| = #|N_out v| + #|N_in v|.
  by rewrite E cardsU (disjoint_setI0 D') cards0 subn0.
rewrite indeg_is_card outdeg_card_Nout Nin_N_in Nout_N_out addnC.
by rewrite -key cardsC1.
Qed.

(** Same identity in the usual "+1" form, avoiding [pred]. *)
Lemma tournament_indeg_outdeg_S v : (indeg v + outdeg v).+1 = #|T|.
Proof.
rewrite tournament_indeg_outdeg prednK //.
by apply/card_gt0P; exists v.
Qed.

End TournamentDegrees.

(** ** The directed triangle is 1-diregular.

    Grounds: in C3 = Z/3, vertex u has the single out-neighbour u+1 and single in-neighbour
    u-1, so out-degree = in-degree = 1 everywhere. *)

Section C3Degrees.
Local Open Scope ring_scope.
Import GRing.Theory.

Lemma C3_outdeg (u : C3) : outdeg u = 1%N.
Proof.
rewrite /outdeg (_ : [set w | u --> w] = [set u + 1]) ?cards1 //.
by apply/setP=> w; rewrite !inE arcC3E.
Qed.

Lemma C3_indeg (u : C3) : indeg u = 1%N.
Proof.
rewrite /indeg /degree_balance.indeg (_ : [set w | w --> u] = [set u - 1]) ?cards1 //.
apply/setP=> w; rewrite !inE arcC3E.
by case: u w => -[|[|[|]]] // ? [[|[|[|]]] //].
Qed.

Lemma C3_diregular1 : diregular C3 1.
Proof. by apply/forallP=> u; rewrite C3_outdeg (C3_indeg u : degree_balance.indeg u = 1%N) !eqxx. Qed.

End C3Degrees.

(** ** Source and sink in the transitive tournament.

    Grounds: TT n.+1 (arcs u-->v iff u<v) has ord0 = source (beats everyone:
    out-degree n) and ord_max = sink (beaten by everyone: in-degree n). *)

Section TTSourceSink.
Variable n : nat.

(** The source [ord0] of [TT n.+1] has out-degree [n]. *)
Lemma TT_has_source : outdeg (ord0 : TT n.+1) = n.
Proof.
rewrite /outdeg (_ : [set w | (ord0 : TT n.+1) --> w] = [set~ ord0]).
  by rewrite cardsC1 card_TT.
apply/setP=> w; rewrite !inE arcTTE /=.
by rewrite lt0n -val_eqE /= eq_sym.
Qed.

(** The sink [ord_max] of [TT n.+1] has in-degree [n]. *)
Lemma TT_has_sink : indeg (ord_max : TT n.+1) = n.
Proof.
rewrite /indeg /degree_balance.indeg (_ : [set w | w --> (ord_max : TT n.+1)] = [set~ ord_max]).
  by rewrite cardsC1 card_TT.
apply/setP=> w; rewrite !inE arcTTE /=.
have wle : (w <= n)%N by have := ltn_ord w; rewrite ltnS.
rewrite ltn_neqAle wle andbT -val_eqE /=.
by congr (~~ _); apply/idP/idP=> /eqP->.
Qed.

End TTSourceSink.

(** ** [Nout2] sanity: it avoids [v] and [Nout v].

    Grounds: the second out-neighbourhood is, by construction, the set of vertices at
    directed distance EXACTLY two — disjoint from [v] itself and from the (distance-one)
    out-neighbours. A definition where these overlapped would be wrong. *)

Section Nout2Sanity.
Variable D : diGraphType.
Implicit Types v : D.

Lemma Nout2_not_self v : v \notin Nout2 v.
Proof. by rewrite inE eqxx. Qed.

Lemma Nout2_disjoint_self v : [disjoint [set v] & Nout2 v].
Proof.
rewrite disjoints1; exact: Nout2_not_self.
Qed.

Lemma Nout2_sub_NNout v : Nout2 v \subset ~: Nout v.
Proof. by apply/subsetP=> w; rewrite !inE => /and3P[_ -> _]. Qed.

Lemma Nout2_disjoint_Nout v : [disjoint Nout2 v & Nout v].
Proof.
rewrite disjoint_subset; apply/subsetP=> w w2.
by have := subsetP (Nout2_sub_NNout v) w w2; rewrite !inE.
Qed.

End Nout2Sanity.

(** ** A Seymour vertex in C3 (SNC conclusion is satisfiable).

    Grounds: Seymour's Second Neighbourhood Conjecture asserts some vertex [v] has
    outdeg v <= #|Nout2 v|. We exhibit such a [v] concretely in C3, confirming the
    conclusion is achievable (Fisher's theorem proves SNC for all tournaments).
    In C3, outdeg = 1 and the unique distance-2 vertex is u-1, so #|Nout2 u| = 1. *)

Section C3Seymour.
Local Open Scope ring_scope.
Import GRing.Theory.

(** Membership in [Nout2 u] is decided by [w == u + 1 + 1] (the unique distance-2
    vertex), by a finite case analysis over the 3x3 vertex pairs of C3. *)
Lemma C3_Nout2_mem (u w : C3) : (w \in Nout2 u) = (w == u + 1 + 1).
Proof.
rewrite inE; apply/idP/idP.
- case/and3P=> _ _ /existsP[x]; rewrite inE !arcC3E.
  by case/andP=> /eqP-> /eqP->.
- move=> /eqP->; apply/and3P; split.
  + by case: u => -[|[|[|]]].
  + by rewrite inE arcC3E; case: u => -[|[|[|]]].
  + apply/existsP; exists (u + 1).
    by rewrite inE arcC3E eqxx /= arcC3E eqxx.
Qed.

Lemma C3_Nout2 (u : C3) : Nout2 u = [set u + 1 + 1].
Proof. by apply/setP=> w; rewrite C3_Nout2_mem inE. Qed.

Lemma C3_card_Nout2 (u : C3) : #|Nout2 u| = 1%N.
Proof. by rewrite C3_Nout2 cards1. Qed.

Lemma C3_has_seymour_vertex : exists v : C3, (outdeg v <= #|Nout2 v|)%N.
Proof. by exists 0; rewrite C3_outdeg C3_card_Nout2. Qed.

(** C3 also positively satisfies the (general) Seymour conclusion shape for ALL vertices —
    a stronger sanity that the predicate is realisable, not just on one vertex. *)
Lemma C3_seymour_all (v : C3) : (outdeg v <= #|Nout2 v|)%N.
Proof. by rewrite C3_outdeg C3_card_Nout2. Qed.

End C3Seymour.

(** ** RED-FLAG falsification probes.

    An OPEN conjecture statement must be NEITHER provably true NOR provably false, and
    must not be vacuous. We check the hypotheses of the Seymour / CH-triangle statements
    are satisfiable (non-vacuous) by exhibiting a concrete instance that meets them, so the
    [forall D, hyp -> concl] statement actually quantifies over a nonempty class. *)

(** C3 satisfies the (nonempty) hypothesis of Seymour's statement: this shows the universal
    statement is not vacuous (there exist oriented graphs with 0 < #|D|). *)
Lemma seymour_nonvacuous : (0 < #|{: C3}|)%N.
Proof. by rewrite card_C3. Qed.

(** C3 is a witness that the CH-triangle hypotheses are SATISFIABLE: #|C3| = 3, each vertex
    has out-degree 1, and 3 <= 3 * 1. So the antecedent [forall v, #|D| <= 3*outdeg v] is
    met by a genuine instance — the statement is not vacuous. And indeed C3 DOES contain a
    directed triangle, consistent with (but not proving) the conjecture. *)
Lemma ch_triangle_hyp_C3 : (forall v : C3, (#|{: C3}| <= 3 * outdeg v)%N).
Proof. by move=> v; rewrite card_C3 C3_outdeg. Qed.

(** C3 satisfies the CH-statement hypotheses: looplessness, positive order, r=1 min
    out-degree. Non-vacuity witness for [caccetta_haggkvist_statement]. *)
Lemma ch_hyp_C3 :
  (0 < #|{: C3}|)%N /\ (forall v : C3, ~~ ((v : C3) --> v)) /\
  (0 < 1)%N /\ (forall v : C3, (1 <= outdeg v)%N).
Proof.
split; first by rewrite card_C3.
split; first by move=> v; rewrite arcxx.
by split=> // v; rewrite C3_outdeg.
Qed.

(** Print Assumptions audit on the load-bearing grounded facts. *)
Print Assumptions tournament_indeg_outdeg.
Print Assumptions C3_diregular1.
Print Assumptions C3_has_seymour_vertex.
Print Assumptions TT_has_source.

(** ** [outdeg_in] on the FULL vertex set matches [outdeg] — grounds the
    load-bearing [outdeg_in] primitive on which the (fixed) splitting-min-outdegree
    statement is built: restricting the out-neighbourhood to [set: D] is no
    restriction. *)
Lemma outdeg_inT_eq (D : diGraphType) (v : D) : outdeg_in [set: D] v = outdeg v.
Proof. by rewrite /outdeg_in /outdeg; apply: eq_card => w; rewrite !inE. Qed.

(** ** [diregular] genuinely constrains: C3 is 1-diregular (C3_diregular1) but is
    NOT 2-diregular — so the [diregular D d] hypothesis has teeth (it is not
    satisfied at every degree). *)
Lemma not_diregular_C3_2 : ~~ diregular C3 2.
Proof.
apply/forallPn; exists (0%R : C3).
by rewrite negb_and C3_outdeg.
Qed.

(** ** GROUNDING: Laborde–Payan–Xuong — a stable set meeting all longest dipaths.

    The open row [stable_meeting_longest_dipaths_statement] asks, for EVERY digraph,
    for a stable (independent) set [S] that meets every longest directed path. The
    genuine open content lives in the interior regime 0 < ell D < #|D|-1, where the
    stability constraint and the "stab every longest path" constraint really compete.
    We ground only the honest right-polarity fragments:

      - [stable_set0]                     : the stable-guard witness class is inhabited.
      - [not_stable_setT_C3]              : TEETH — [stable] is a real constraint (you can
                                            NOT always take S := setT: setT of C3 is unstable).
      - [exists_meeting_set]             : ALWAYS-TRUE HALF — the meeting conjunct alone is
                                            unconditionally satisfiable (S := setT meets every
                                            longest path at its start), so any LPX
                                            counterexample must fail on stability, never on
                                            meeting.
      - [stable_meeting_when_setT_stable] : the FULL conclusion holds on the ell D = 0
                                            (edgeless) boundary, where setT is itself stable.
      - [stable_meeting_hamiltonian]      : SETTLED SUB-CASE — the FULL conclusion holds for
                                            every LOOPLESS digraph carrying a Hamiltonian
                                            directed path (ell D = #|D|-1); a longest path then
                                            covers ALL vertices, so a single vertex is a stable
                                            meeting set. Covers every tournament (incl. C3).
    We do NOT attempt the open interior or any non-trivial structured settled family. *)

(** The stable guard is realizable: [set0] is stable in every digraph
    (no members, hence no forbidden arc between members). *)
Lemma stable_set0 (D : diGraphType) : stable (set0 : {set D}).
Proof. by apply/forallP=> u; rewrite inE. Qed.

(** TEETH on a real object: the full vertex set of C3 is NOT stable — the arc
    0 --> 1 lies inside it. So one cannot always take S := setT; the [stable]
    requirement genuinely constrains the LPX witness. *)
Section StableC3Teeth.
Local Open Scope ring_scope.
Import GRing.Theory.

Lemma not_stable_setT_C3 : ~~ stable [set: C3].
Proof.
apply/negP => /forall_inP/(_ (0%R : C3) (in_setT _))
              /forall_inP/(_ (1%R : C3) (in_setT _)).
by rewrite arcC3E add0r eqxx.
Qed.

End StableC3Teeth.

(** ALWAYS-TRUE HALF: the "meets every longest directed path" conjunct on its own is
    unconditionally satisfiable — S := setT meets every longest path at its start vertex.
    This isolates the difficulty of LPX entirely into the simultaneous stability constraint. *)
Lemma exists_meeting_set (D : diGraphType) :
  exists S : {set D}, forall (x : D) (s : seq D),
    dipath x s -> size s = ell D -> exists2 v : D, v \in S & v \in x :: s.
Proof.
exists [set: D] => x s _ _.
by exists x; [exact: in_setT | exact: mem_head].
Qed.

(** BOUNDARY ell D = 0 (edgeless regime): whenever setT is itself stable, it is a stable
    set meeting every longest path (at its start), so the FULL statement conclusion holds.
    Pins the correct TRUE value on the edgeless boundary of LPX. *)
Lemma stable_meeting_when_setT_stable (D : diGraphType) :
  stable [set: D] ->
  exists S : {set D}, stable S /\
    forall (x : D) (s : seq D), dipath x s -> size s = ell D ->
      exists2 v : D, v \in S & v \in x :: s.
Proof.
move=> Hst; exists [set: D]; split=> // x s _ _.
by exists x; [exact: in_setT | exact: mem_head].
Qed.

(** Helper: a duplicate-free list whose length equals #|T| enumerates all of T, hence
    contains every element. (Used to show a Hamiltonian dipath covers every vertex.) *)
Lemma mem_uniq_full (T : finType) (l : seq T) (y : T) :
  uniq l -> size l = #|T| -> y \in l.
Proof.
move=> ul sl.
have /card_uniqP cardE := ul.
have cE : #|mem l| = #|T| by rewrite cardE.
have hs : (mem l) =i predT by apply/(subset_cardP cE); exact: subset_predT.
by rewrite (hs y).
Qed.

(** SETTLED SUB-CASE, Hamiltonian-dipath class (ell D = #|D|-1, includes every tournament
    and C3): for a LOOPLESS digraph whose longest directed path is Hamiltonian, [dipath_size]
    forces size (x :: s) <= #|D| and the hypothesis forces #|D| <= size (x :: s), so a longest
    path is a uniq list of length #|D| covering EVERY vertex. Hence a single (loopless) vertex
    [set x0] is a stable set meeting every longest path. The looplessness hypothesis is the
    standard LPX class restriction, not a vacuizer (it is exactly what makes a singleton
    stable). Pins the correct TRUE value on the ell D = #|D|-1 boundary. *)
Lemma stable_meeting_hamiltonian (D : diGraphType) :
  (forall v : D, ~~ (v --> v)) -> #|D| <= (ell D).+1 ->
  exists S : {set D}, stable S /\
    forall (x : D) (s : seq D), dipath x s -> size s = ell D ->
      exists2 v : D, v \in S & v \in x :: s.
Proof.
move=> loopless Hell.
have [n0|n0] := posnP #|D|.
  exists set0; split; first exact: stable_set0.
  move=> x s _ _; exfalso.
  have h : (0 < #|D|)%N by apply/card_gt0P; exists x.
  by rewrite n0 in h.
have /card_gt0P[x0 _] := n0.
exists [set x0]; split.
  apply/forallP=> u; apply/implyP; rewrite inE => /eqP->.
  apply/forallP=> v; apply/implyP; rewrite inE => /eqP->; exact: loopless.
move=> x s dp sE; exists x0; first by rewrite inE.
have usz : uniq (x :: s) by case/andP: dp.
have szle : size (x :: s) <= #|D|.
  by have /card_uniqP cardE := usz; rewrite -cardE; apply: max_card.
have szge : #|D| <= size (x :: s) by rewrite /= sE.
have szxs : size (x :: s) = #|D| by apply/eqP; rewrite eqn_leq szle szge.
by apply: mem_uniq_full.
Qed.

(** * Digraph.foundations.tournament_unavoidability -- exact-order tournament unavoidability

    [tournament_unavoidable D N]: EVERY bundled tournament [T] with exactly [N]
    vertices contains [D] through an injective map that preserves arcs one way
    (upstream [GraphTheory.core.digraph.is_dhom] on [to_GT]); non-arcs of [D] may map
    anywhere, so this is not induced containment ([isubgraph]).  [D] is an arbitrary
    finite digraph: loops and digons are allowed, and then no tournament contains it.

    [unavoidability_number D N]: [D] is [N]-unavoidable and is not [M]-unavoidable for
    EVERY smaller [M]; the empty digraph has value 0.  [linearly_unavoidable F]: one
    natural [C], chosen before all digraphs, bounds every pinned value of a member of
    [F] by [C * #|D|]; there is no existence, positivity or acyclicity requirement.
    Upward monotonicity in [N] is a proved lemma, not part of any definition.

    [tournament_unavoidable_unbundledE] is the same-carrier factory bridge: a
    [diGraphType] that is irreflexive, semicomplete and asymmetric becomes a bundled
    tournament on the same carrier with the same arcs, so the bundled quantification
    agrees with quantification over such digraphs.  This module imports no
    conjecture file. *)
From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude interop_graph_theory digraph oriented tournament.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition tournament_unavoidable (D : diGraphType) (N : nat) : Prop :=
  forall T : tournament, #|T| = N ->
    exists f : D -> T,
      injective f /\ @GraphTheory.core.digraph.is_dhom (to_GT D) (to_GT T) f.

Definition unavoidability_number (D : diGraphType) (N : nat) : Prop :=
  tournament_unavoidable D N /\ (forall M : nat, M < N -> ~ tournament_unavoidable D M).

Definition linearly_unavoidable (F : diGraphType -> Prop) : Prop :=
  exists C : nat,
    forall (D : diGraphType) (N : nat), F D -> unavoidability_number D N -> (N <= C * #|D|)%N.

(** ** The same-carrier factory bridge *)

Section SameCarrier.
Variable T : diGraphType.
Hypothesis irr : irreflexive (@arc T).
Hypothesis semi : forall u v : T, u != v -> (u --> v) || (v --> u).
Hypothesis asym : forall u v : T, u --> v -> ~~ (v --> u).

Definition same_carrier : Type := T.
HB.instance Definition _ := Finite.on same_carrier.
HB.instance Definition _ := HasArc.Build same_carrier (@arc T).

Fact same_carrier_irrefl : irreflexive (arc : rel same_carrier).
Proof. exact: irr. Qed.

Lemma unbundled_arc_total (u v : T) : (u != v) = (u --> v) (+) (v --> u).
Proof.
have [<-|uv] := eqVneq u v; first by rewrite (irr u).
case/orP: (semi uv) => a.
- by rewrite a (negbTE (asym a)).
- by rewrite a (negbTE (asym a)).
Qed.

Fact same_carrier_total (u v : same_carrier) : (u != v) = (arc u v) (+) (arc v u).
Proof. exact: unbundled_arc_total. Qed.

HB.instance Definition _ :=
  DiGraph_IsTournament.Build same_carrier same_carrier_irrefl same_carrier_total.

Definition same_carrier_tournament : tournament := same_carrier.

Lemma same_carrier_card : #|same_carrier_tournament| = #|T|.
Proof. by []. Qed.

End SameCarrier.

Lemma tournament_unavoidable_unbundledE (D : diGraphType) (N : nat) :
  tournament_unavoidable D N <->
  forall T : diGraphType,
    irreflexive (@arc T) ->
    (forall u v : T, u != v -> (u --> v) || (v --> u)) ->
    (forall u v : T, u --> v -> ~~ (v --> u)) ->
    #|T| = N ->
    exists f : D -> T, injective f /\ forall u v : D, u --> v -> f u --> f v.
Proof.
split=> [un T irr semi asym cardT|un T cardT].
- have [f [inj hom]] := un (same_carrier_tournament irr semi asym) cardT.
  by exists f.
- have [f [inj hom]] := un (T : diGraphType) (@arcxx T) (@arc_or T) (@arc_asym T) cardT.
  by exists f.
Qed.

(** ** Basic API *)

Lemma tournament_unavoidable_card (D : diGraphType) (N : nat) :
  tournament_unavoidable D N -> (#|D| <= N)%N.
Proof.
move=> /(_ (TT N : tournament) (card_TT N)) [f [inj _]].
by rewrite -(card_TT N); exact: leq_card inj.
Qed.

Lemma tournament_unavoidable_empty (D : diGraphType) (N : nat) :
  #|D| = 0 -> tournament_unavoidable D N.
Proof.
move=> D0 T _; have nd : D -> False.
  by move=> x; move: D0 => /eqP; rewrite -leqn0 leqNgt => /negP; apply; apply/card_gt0P; exists x.
by exists (fun x => match nd x with end); split=> [x|x]; case: (nd x).
Qed.

(** Upward monotonicity, proved rather than assumed: deleting any vertex of a
    tournament on [N.+1] vertices leaves a sub-tournament on exactly [N] vertices. *)
Lemma tournament_unavoidable_succ (D : diGraphType) (N : nat) :
  tournament_unavoidable D N -> tournament_unavoidable D N.+1.
Proof.
move=> un T cardT.
have [v _] : {v : T | v \in T} by apply/sigW/card_gt0P; rewrite cardT.
have cardS : #|del_tournament v| = N by rewrite card_sig cardsC1 cardT.
have [f [inj hom]] := un (del_tournament v) cardS.
exists (val \o f); split; first exact: inj_comp val_inj inj.
by move=> x y xy; exact: hom x y xy.
Qed.

Lemma tournament_unavoidable_monotone (D : diGraphType) (N M : nat) :
  (N <= M)%N -> tournament_unavoidable D N -> tournament_unavoidable D M.
Proof.
move=> /subnK <-; elim: (M - N) => [|k IH] un; first by rewrite add0n.
by rewrite addSn; apply: tournament_unavoidable_succ; exact: IH.
Qed.


Lemma unavoidability_number_empty (D : diGraphType) : #|D| = 0 -> unavoidability_number D 0.
Proof. by move=> D0; split; [exact: tournament_unavoidable_empty | case]. Qed.

Lemma unavoidability_number_card (D : diGraphType) (N : nat) :
  unavoidability_number D N -> (#|D| <= N)%N.
Proof. by move=> [un _]; exact: tournament_unavoidable_card un. Qed.

Lemma unavoidability_number_unique (D : diGraphType) (N M : nat) :
  unavoidability_number D N -> unavoidability_number D M -> N = M.
Proof.
move=> [uN mN] [uM mM]; apply/eqP; rewrite eqn_leq.
by apply/andP; split; rewrite leqNgt; apply/negP => lt; [exact: mN M lt uM | exact: mM N lt uN].
Qed.

(** A loop or a digon of [D] cannot be mapped into any tournament. *)
Lemma not_tournament_unavoidable_loop (D : diGraphType) (u : D) (N : nat) :
  u --> u -> ~ tournament_unavoidable D N.
Proof.
move=> uu /(_ (TT N : tournament) (card_TT N)) [f [_ hom]].
have a : (f u : TT N) --> f u := hom u u uu.
by move: a; rewrite arcxx.
Qed.

Lemma not_tournament_unavoidable_digon (D : diGraphType) (u v : D) (N : nat) :
  u --> v -> v --> u -> ~ tournament_unavoidable D N.
Proof.
move=> uv vu /(_ (TT N : tournament) (card_TT N)) [f [_ hom]].
have a1 : (f u : TT N) --> f v := hom u v uv.
have a2 : (f v : TT N) --> f u := hom v u vu.
by have := arc_asym a1; rewrite a2.
Qed.

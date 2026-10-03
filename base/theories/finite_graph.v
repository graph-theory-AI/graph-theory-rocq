(** * GTBase.finite_graph -- labelled finite graphs and finite counting events *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph.
From GTBase Require Import asymptotics.
From GTBase Require common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Symmetric, irreflexive closure of a boolean relation. *)
Definition fg_srel (V : finType) (r : rel V) : rel V :=
  fun x y => (x != y) && (r x y || r y x).

Lemma fg_srel_sym (V : finType) (r : rel V) : symmetric (fg_srel r).
Proof. by move=> x y; rewrite /fg_srel eq_sym orbC. Qed.

Lemma fg_srel_irrefl (V : finType) (r : rel V) : irreflexive (fg_srel r).
Proof. by move=> x; rewrite /fg_srel eqxx. Qed.

Definition fg_mk_sgraph (V : finType) (r : rel V) : sgraph :=
  @SGraph V (fg_srel r) (@fg_srel_sym V r) (@fg_srel_irrefl V r).

(** Labelled simple graphs are encoded as sets of 2-subsets of a finite carrier. *)
Definition fg_valid_edge_set (V : finType) (E : {set {set V}}) : bool :=
  [forall e : {set V}, (e \in E) ==> (#|e| == 2)].

Definition fg_edge_set_rel (V : finType) (E : {set {set V}}) : rel V :=
  fun x y => [set x; y] \in E.

Definition fg_labelled_sgraph (V : finType) (E : {set {set V}}) : sgraph :=
  fg_mk_sgraph (fg_edge_set_rel E).

Definition fg_edges (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x != y) && (x -- y) && (e == [set x; y])]]].

(** The number of edges: the canonical [GTBase.common.edge_count] (library migration A7).  It
    was [#|fg_edges G|]; [fg_edges] is unchanged and equals the upstream edge set [E(G)]
    ([fg_edgesE]), so the two counts agree ([card_fg_edges]). *)
Definition fg_edge_count (G : sgraph) : nat := GTBase.common.edge_count G.

(** The labelled-graph edge set is the upstream edge set: the explicit [x != y] guard is implied
    by irreflexivity.  (The proof is adapted from C1's certificate lemma of the same name.) *)
Lemma fg_edgesE (G : sgraph) : fg_edges G = E(G).
Proof.
apply/setP => e; rewrite GTBase.common.in_sg_edge_set inE.
apply/existsP/existsP => -[x /existsP[y H]]; exists x; apply/existsP; exists y;
  move: H.
- by case/andP=> /andP[_ xy] /eqP->; rewrite xy eqxx.
- by case/andP=> xy /eqP->; rewrite xy eqxx (sg_edgeNeq xy).
Qed.

Lemma card_fg_edges (G : sgraph) : #|fg_edges G| = GTBase.common.edge_count G.
Proof. by rewrite fg_edgesE. Qed.

Definition fg_complete_edge_universe (n : nat) : {set {set 'I_n}} :=
  [set e : {set 'I_n} | #|e| == 2].

Definition fg_valid_labelled_edges (n : nat) (E : {set {set 'I_n}}) : bool :=
  E \subset fg_complete_edge_universe n.

(** Integer weight for labelled [G(n,p/q)] edge sets.  Invalid edge sets receive
    weight zero; valid [E] receives [p^|E| (q-p)^(N-|E|)]. *)
Definition fg_gnp_weight (p q n : nat) (E : {set {set 'I_n}}) : nat :=
  if (0 < p) && (p < q) && fg_valid_labelled_edges E then
    p ^ #|E| * (q - p) ^ (#|fg_complete_edge_universe n| - #|E|)
  else 0.

(** Exact finite probability/event vocabulary, encoded by cross-multiplied
    natural weights.  A zero total weight makes threshold assertions false. *)
Definition fg_total_weight (T : finType) (w : T -> nat) : nat :=
  \sum_(x : T) w x.

Definition fg_event_weight (T : finType) (w : T -> nat) (P : pred T) : nat :=
  \sum_(x : T | P x) w x.

Definition fg_event_at_least_ratio
    (T : finType) (w : T -> nat) (P : pred T) (num den : nat) : Prop :=
  0 < den /\ num <= den /\
  0 < fg_total_weight w /\
  den * fg_event_weight w P >= num * fg_total_weight w.

Definition fg_event_at_most_ratio
    (T : finType) (w : T -> nat) (P : pred T) (num den : nat) : Prop :=
  0 < den /\ num <= den /\
  0 < fg_total_weight w /\
  den * fg_event_weight w P <= num * fg_total_weight w.

Definition fg_whp
    (T : nat -> finType) (w : forall n : nat, T n -> nat)
    (P : forall n : nat, pred (T n)) : Prop :=
  forall a b : nat, 0 < a -> a <= b ->
    eventually (fun n =>
      0 < fg_total_weight (w n) /\
      b * fg_event_weight (w n) (P n) >= (b - a) * fg_total_weight (w n)).

Definition fg_probability_bounded_away_from_one
    (T : nat -> finType) (w : forall n : nat, T n -> nat)
    (P : forall n : nat, pred (T n)) : Prop :=
  exists a b : nat, 0 < a /\ a <= b /\
    eventually (fun n =>
      0 < fg_total_weight (w n) /\
      b * fg_event_weight (w n) (P n) <= (b - a) * fg_total_weight (w n)).

(** The probability predicates expose their positive-mass contract. *)
Lemma fg_event_at_least_ratio_total_weight_pos
    (T : finType) (w : T -> nat) (P : pred T) (num den : nat) :
  fg_event_at_least_ratio w P num den -> 0 < fg_total_weight w.
Proof. by move=> [_ [_ [H _]]]. Qed.

Lemma fg_event_at_most_ratio_total_weight_pos
    (T : finType) (w : T -> nat) (P : pred T) (num den : nat) :
  fg_event_at_most_ratio w P num den -> 0 < fg_total_weight w.
Proof. by move=> [_ [_ [H _]]]. Qed.

Lemma fg_whp_eventually_total_weight_pos
    (T : nat -> finType) (w : forall n : nat, T n -> nat)
    (P : forall n : nat, pred (T n)) :
  fg_whp w P -> eventually (fun n => 0 < fg_total_weight (w n)).
Proof.
move=> Hwhp; move: (Hwhp 1 1 erefl erefl) => [N HN].
by exists N => n Nn; have [] := HN n Nn.
Qed.

Lemma fg_probability_bounded_away_from_one_eventually_total_weight_pos
    (T : nat -> finType) (w : forall n : nat, T n -> nat)
    (P : forall n : nat, pred (T n)) :
  fg_probability_bounded_away_from_one w P ->
  eventually (fun n => 0 < fg_total_weight (w n)).
Proof.
move=> [a [b [_ [_ [N HN]]]]].
by exists N => n Nn; have [] := HN n Nn.
Qed.

(** * Digraph.conjectures.grounding_fas_unvd — GROUNDING for path_fas.v + unvd.v

    Faithfulness checks: small KNOWN textbook/paper facts the NEW definitions of
    [Delta_star] / [has_LFO] (path_fas.v) and [contains_subdigraph] / [unvd]
    (unvd.v) MUST satisfy.  Every lemma is Qed; no Admitted/Axiom.

    Grounded facts:
      - [Delta_star (TT n) = 0]      : a transitive tournament is "sparse"; its
                                        natural (acyclic) order has zero back-arcs,
                                        so its degreewidth is 0
                                        (Davot–Isenmann–Roy–Thiebaut, arXiv:2212.06007).
      - [has_LFO (TT n)]             : that same edgeless back-arc graph is a linear
                                        forest, so a transitive tournament trivially
                                        has a linear-forest ordering.
      - [contains_subdigraph D D]    : reflexivity of containment.
      - [unvd K1 1] / [~ unvd K1 0]  : a 1-vertex digraph is exactly 1-unavoidable;
                                        the degenerate value 0 is refuted (red-flag
                                        probe: every tournament contains a vertex, but
                                        the EMPTY tournament does not contain [K1]).
      - [unvd K2 2]                  : the single arc is exactly 2-unavoidable (every
                                        2-vertex tournament IS an arc; a 1-vertex
                                        tournament has no arc).                          *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude interop_graph_theory digraph oriented dipath.
From Digraph Require Import tournament order.
From Digraph Require Import heroes path_fas unvd.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** GROUNDING path_fas.v: degreewidth and LFO of transitive tournaments *)

(** The identity order [1%g] on [TT n] agrees with the arc direction:
    [u --> v] (i.e. [u < v]) implies [u] precedes [v].  Because [enum_rank] on
    ['I_n] is the identity (up to the [card_ord] cast), [ltp 1 u v = (u < v)]. *)
Lemma ltp1_TT (n : nat) (u v : TT n) : ltp 1%g u v = (u < v)%N.
Proof.
by rewrite /ltp !perm1 !enum_rank_ord /=.
Qed.

(** Under the identity order, every arc of [TT n] points forward, so the
    back-arc (backedge) graph is EDGELESS.  This is the zero-back-arc witness. *)
Lemma backedge_TT_id_edgeless (n : nat) (u v : backedge (1%g : {perm TT n})) :
  ~~ (u -- v).
Proof.
apply: backedge_arc_forward => {u v} u v.
by rewrite arcTTE ltp1_TT.
Qed.

(** Hence under the identity order every vertex has back-degree 0. *)
Lemma backdeg_TT_id (n : nat) (v : TT n) : backdeg (1%g : {perm TT n}) v = 0%N.
Proof.
rewrite /backdeg /sdeg; apply/eqP; rewrite cards_eq0; apply/eqP.
apply/setP => w; rewrite !inE; apply/negbTE.
exact: backedge_TT_id_edgeless.
Qed.

(** The maximum back-degree under the identity order is 0. *)
Lemma maxbackdeg_TT_id (n : nat) : maxbackdeg (1%g : {perm TT n}) = 0%N.
Proof.
apply/eqP; rewrite -leqn0; apply: maxbackdeg_leP => v.
by rewrite backdeg_TT_id.
Qed.

(** GROUNDING: the degreewidth of the transitive tournament [TT n] is 0.
    (Davot–Isenmann–Roy–Thiebaut, arXiv:2212.06007: a sparse / acyclic-orderable
    tournament has degreewidth 0; a transitive tournament is the extreme case.) *)
Theorem Delta_star_TT (n : nat) : Delta_star (TT n) = 0%N.
Proof.
apply/eqP; rewrite -leqn0.
by apply: (leq_trans (Delta_star_min (1%g : {perm TT n}))); rewrite maxbackdeg_TT_id.
Qed.

(** In an edgeless simple graph, connectivity collapses to equality. *)
Lemma edgeless_connect (G : sgraph) :
  (forall x y : G, ~~ (x -- y)) ->
  forall x y : G, connect (--) x y -> x = y.
Proof.
move=> edgeless x y /connectP[p]; case: p => [_ /= ->//|z s /=].
by rewrite (negbTE (edgeless x z)).
Qed.

(** An edgeless simple graph is a linear forest (vacuously a forest, all degrees 0). *)
Lemma linear_forest_edgeless (G : sgraph) :
  (forall x y : G, ~~ (x -- y)) -> linear_forest G.
Proof.
move=> edgeless; split.
- move=> x y p1 p2 [irr1 _] [irr2 _].
  have xy : x = y by apply: (edgeless_connect edgeless); apply: (Path_connect p1).
  move: p1 p2 irr1 irr2; case: y / xy => p1 p2 /irredxx -> /irredxx ->.
  reflexivity.
- move=> x; rewrite /sdeg [#|_|](_ : _ = 0) //.
  apply: eq_card0 => y; rewrite !inE.
  by apply/negbTE; apply: edgeless.
Qed.

(** GROUNDING: a transitive tournament has a linear-forest ordering (its identity
    order has an edgeless — hence linear-forest — back-arc graph). *)
Theorem has_LFO_TT (n : nat) : has_LFO (TT n).
Proof.
exists (1%g : {perm TT n}); apply: linear_forest_edgeless.
exact: backedge_TT_id_edgeless.
Qed.

(** ** GROUNDING unvd.v: containment reflexivity and the smallest unvd values *)

(** GROUNDING: containment is reflexive (identity map is injective and arc-preserving). *)
Theorem contains_subdigraph_refl (D : diGraphType) : contains_subdigraph D D.
Proof. by exists id; split=> // u v. Qed.

(** [K1 = TT 1] has no arc (the only candidate is [0 < 0], false). *)
Lemma K1_no_arc (u v : K1) : ~~ (u --> v).
Proof. by rewrite /K1 arcTTE; case: u v => -[|//] ? [[|//] ?]. Qed.

(** [K1 = TT 1] has a single vertex, so any two vertices are equal. *)
Lemma K1_unique (u v : K1) : u = v.
Proof. by apply: val_inj; case: u v => -[|//] ? [[|//] ?]. Qed.

(** The empty tournament [TT 0] is a genuine tournament with 0 vertices. *)
Lemma is_tournament_TT (n : nat) : is_tournament (TT n).
Proof.
split.
- exact: (@arc_irrefl (TT n)).
- move=> u v; rewrite arc_total => uv.
  by case: (u --> v) (v --> u) uv => [] [].
- by move=> u v; apply: arc_asym.
Qed.

(** No injective map into a strictly smaller type: if [#|A| <= #|B|] fails for an
    injection [A -> B], contradiction.  We use it via [leq_card]. *)
Lemma no_inj_into_smaller (A B : finType) (f : A -> B) :
  injective f -> (#|B| < #|A|)%N -> False.
Proof. by move=> /leq_card; rewrite leqNgt => /negP. Qed.

(** GROUNDING: the unavoidability number of the single vertex [K1] is exactly 1.
    Every (non-empty) tournament contains a vertex; the empty tournament does not. *)
Theorem unvd_K1 : unvd K1 1.
Proof.
split.
- (* 1-unavoidable: every 1-vertex tournament contains K1 *)
  apply/unavoidableP => T _ cardT.
  have [t _] : { t : T | t \in T }.
    by apply/sigW; apply/card_gt0P; rewrite cardT.
  exists (fun _ => t); split.
  + (* injective: K1 has a single vertex *)
    move=> a b _; apply: val_inj => /=.
    by case: a b => -[|//] ? [[|//] ?].
  + by move=> u v uv; rewrite (negbTE (K1_no_arc u v)) in uv.
- (* minimal: 0 is not unavoidable — TT 0 has no K1 *)
  move=> M; rewrite ltnS leqn0 => /eqP -> /unavoidableP/(_ (TT 0) (is_tournament_TT 0) (card_ord 0)).
  case=> f [inj_f _].
  by apply: (no_inj_into_smaller inj_f); rewrite card_ord card_TT.
Qed.

(** RED-FLAG PROBE: [unvd K1 0] is FALSE (the degenerate value 0 must NOT satisfy
    the definition).  If this were provable, the "least unavoidable [N]" framing
    would be broken. *)
Theorem not_unvd_K1_0 : ~ unvd K1 0.
Proof.
case=> /unavoidableP/(_ (TT 0) (is_tournament_TT 0) (card_ord 0)) [f [inj_f _]] _.
by apply: (no_inj_into_smaller inj_f); rewrite card_ord card_TT.
Qed.

(** ** The single arc [K2 := djoin K1 K1] *)

Definition K2 : diGraphType := djoin K1 K1.

Lemma card_K2 : #|K2| = 2.
Proof. by rewrite /K2 /djoin card_sum !card_TT. Qed.

(** The only arc of [K2] is [inl _ --> inr _]; in particular [u --> v] forces
    [u] on the left and [v] on the right. *)
Lemma K2_arc (u v : K2) :
  u --> v -> exists a b : K1, u = inl a /\ v = inr b.
Proof.
case: u v => [a|a] [b|b] //=.
- by move=> ab; case/negP: (K1_no_arc a b).
- by move=> _; exists a, b.
- by move=> ab; case/negP: (K1_no_arc a b).
Qed.

Lemma K2_arc_lr (a b : K1) : (inl a : K2) --> (inr b).
Proof. by []. Qed.

(** GROUNDING: the unavoidability number of the single arc is exactly 2.  Every
    2-vertex tournament IS an arc (so contains [K2]); no tournament on < 2
    vertices does. *)
Theorem unvd_K2 : unvd K2 2.
Proof.
split.
- (* 2-unavoidable: every 2-vertex tournament contains the arc K2 *)
  apply/unavoidableP => T isT cardT.
  have /card_gt1P[x [y [_ _ xy_ne]]] : (1 < #|T|)%N by rewrite cardT.
  have [isT_irr isT_sc isT_as] := isT.
  (* pick the arc orientation between x and y *)
  case/orP: (isT_sc x y xy_ne) => [xy|yx].
  + exists (fun w => match w with inl _ => x | inr _ => y end); split.
    * move=> [a|a] [b|b] //= e.
      -- by rewrite (K1_unique a b).
      -- by rewrite e eqxx in xy_ne.
      -- by rewrite -e eqxx in xy_ne.
      -- by rewrite (K1_unique a b).
    * by move=> u v /K2_arc[a [b [-> ->]]].
  + exists (fun w => match w with inl _ => y | inr _ => x end); split.
    * move=> [a|a] [b|b] //= e.
      -- by rewrite (K1_unique a b).
      -- by rewrite -e eqxx in xy_ne.
      -- by rewrite e eqxx in xy_ne.
      -- by rewrite (K1_unique a b).
    * by move=> u v /K2_arc[a [b [-> ->]]].
- (* minimal: neither 0 nor 1 is unavoidable (K2 has 2 vertices) *)
  move=> M; rewrite ltnS leq_eqVlt => /orP[/eqP->|].
  + (* M = 1 : witness TT 1 *)
    move=> /unavoidableP/(_ (TT 1) (is_tournament_TT 1) (card_ord 1)) [f [inj_f _]].
    by apply: (no_inj_into_smaller inj_f); rewrite card_TT card_K2.
  + rewrite ltnS leqn0 => /eqP -> .
    move=> /unavoidableP/(_ (TT 0) (is_tournament_TT 0) (card_ord 0)) [f [inj_f _]].
    by apply: (no_inj_into_smaller inj_f); rewrite card_ord card_K2.
Qed.

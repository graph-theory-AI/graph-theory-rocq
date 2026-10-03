(** * Raw support of supplied branch maps and edge lists

    [model_support br ep x] holds when [x] is the image [br h] of some pattern
    vertex, or occurs in the supplied list [ep u v] of some GENUINE pattern edge
    [u -- v].  The pattern [H] comes before the host [G].  This is RAW SUPPORT,
    not the validity of a minor or subdivision model: [br] need not be injective,
    and [ep u v] need not be a path, simple, induced, reversible or disjoint from
    other lists.  Both orientations [ep u v] and [ep v u] of an edge contribute;
    lists on non-edges are ignored ([model_support_eq_on_edges]); with the empty
    pattern the predicate is false ([model_support_K0]); without pattern edges it
    is exactly the image of [br] ([model_support_edgeless]).

    The three existing copies (X98 and X114 on full edge paths, and
    Minor's [sdm_covers] on subdivision INTERIORS) read the same raw predicate on
    their supplied lists.  The surrounding model Records are not identified:
    their path, reversal, disjointness and inducedness fields stay where they
    are.  Import explicitly; [GTBase.base] does not re-export this module. *)
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition model_support (H G : sgraph) (br : H -> G) (ep : H -> H -> seq G) (x : G) : Prop :=
  (exists h : H, br h = x) \/ (exists u v : H, u -- v /\ x \in ep u v).

Section ModelSupport.
Variables (H G : sgraph).

Lemma model_support_branch (br : H -> G) (ep : H -> H -> seq G) (h : H) : model_support br ep (br h).
Proof. by left; exists h. Qed.

Lemma model_support_edge (br : H -> G) (ep : H -> H -> seq G) (u v : H) (x : G) :
  u -- v -> x \in ep u v -> model_support br ep x.
Proof. by move=> uv xin; right; exists u, v. Qed.

(** Both orientations of a pattern edge contribute. *)
Lemma model_support_edge_rev (br : H -> G) (ep : H -> H -> seq G) (u v : H) (x : G) :
  u -- v -> x \in ep v u -> model_support br ep x.
Proof. by move=> uv; apply: model_support_edge; rewrite sg_sym. Qed.

(** Lists on non-edges are ignored. *)
Lemma model_support_eq_on_edges (br : H -> G) (ep ep' : H -> H -> seq G) (x : G) :
  (forall u v : H, u -- v -> ep u v = ep' u v) ->
  model_support br ep x <-> model_support br ep' x.
Proof.
move=> same; split=> -[[h hx]|[u [v [uv xin]]]].
- by left; exists h.
- by right; exists u, v; rewrite -(same u v uv).
- by left; exists h.
- by right; exists u, v; rewrite (same u v uv).
Qed.

(** Larger lists on pattern edges only enlarge the support. *)
Lemma model_support_sub (br : H -> G) (ep ep' : H -> H -> seq G) (x : G) :
  (forall u v : H, u -- v -> {subset ep u v <= ep' u v}) ->
  model_support br ep x -> model_support br ep' x.
Proof.
move=> sub [[h hx]|[u [v [uv xin]]]]; first by left; exists h.
by right; exists u, v; split=> //; exact: sub uv x xin.
Qed.

(** Empty lists on every pattern edge leave exactly the branch images. *)
Lemma model_support_nil (br : H -> G) (ep : H -> H -> seq G) (x : G) :
  (forall u v : H, u -- v -> ep u v = [::]) ->
  model_support br ep x <-> exists h : H, br h = x.
Proof.
move=> nil; split=> [[//|[u [v [uv]]]]|[h hx]]; last by left; exists h.
by rewrite (nil u v uv) in_nil.
Qed.

(** Without pattern edges the support is exactly the image of [br]. *)
Lemma model_support_edgeless (br : H -> G) (ep : H -> H -> seq G) (x : G) :
  (forall u v : H, ~~ (u -- v)) ->
  model_support br ep x <-> exists h : H, br h = x.
Proof. by move=> edgeless; apply: model_support_nil => u v; rewrite (negbTE (edgeless u v)). Qed.

(** With no pattern vertex nothing is supported. *)
Lemma model_support_card0 (br : H -> G) (ep : H -> H -> seq G) (x : G) : #|H| = 0 -> ~ model_support br ep x.
Proof.
move=> H0 supp.
have [h _] : exists h : H, True by case: supp => [[h _]|[u _]]; [exists h | exists u].
have : 0 < #|H| by apply/card_gt0P; exists h.
by rewrite H0.
Qed.

End ModelSupport.

Lemma model_support_K0 (G : sgraph) (br : 'K_0 -> G) (ep : 'K_0 -> 'K_0 -> seq G) (x : G) :
  ~ model_support br ep x.
Proof. by apply: model_support_card0; rewrite card_ord. Qed.

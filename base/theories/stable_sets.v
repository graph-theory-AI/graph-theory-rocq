(** * GTBase.stable_sets -- raw views of the upstream stable-set predicate

    The canonical stable-set predicate is upstream [stable S] ([GraphTheory.core.dom], re-exported by [GTBase.base]):
    the Boolean [[disjoint NS(S) & S]] on a supplied vertex set [S], with [stableP], [stablePn] and [stableEedge]
    upstream.  No stable-set predicate is added here: the lemmas below relate it, for every graph (the empty one
    included) and every supplied set, to the raw presentations used by the corpus.
    - [stable_noedgeP]: no supplied pair is an edge, [x -- y -> False];
    - [stable_nonadjP]: every supplied pair is nonadjacent, [~~ (x -- y)], the diagonal included;
    - [stable_distinctP]: distinct supplied vertices are nonadjacent, [x != y -> ~~ (x -- y)];
    - [stable_eqbE]: the bounded Boolean [[forall x in S, [forall y in S, (x == y) || ~~ (x -- y)]]].
    The diagonal and unequal-vertex variants agree by sgraph irreflexivity; no nonemptiness, cardinality or
    looplessness hypothesis is involved.  [stable_pair] is the two-vertex case.  Upstream also supplies [stable0],
    [stable1], [sub_stable], [stable_isubgraph] and [stable_induced]; its [diso_stable] is unproved ([Abort]) and is
    not used.  Stable sets of a directed graph, which must exclude loops as well, are a separate contract.
    Registry: meta/library_primitives/stable-set.json (A20). *)
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section StableSetViews.
Variable G : sgraph.
Implicit Types S : {set G}.

(** No supplied pair is an edge. *)
Lemma stable_noedgeP S :
  reflect (forall x y : G, x \in S -> y \in S -> x -- y -> False) (stable S).
Proof.
apply: (iffP (stableP S)) => [st x y xS yS xy|st x y xS yS].
  by move: (st x y xS yS); rewrite xy.
by apply/negP; exact: st.
Qed.

(** Every supplied pair, the diagonal included, is nonadjacent. *)
Lemma stable_nonadjP S :
  reflect (forall x y : G, x \in S -> y \in S -> ~~ (x -- y)) (stable S).
Proof. exact: stableP. Qed.

(** Distinct supplied vertices are nonadjacent: the guard is redundant by irreflexivity. *)
Lemma stable_distinctP S :
  reflect (forall x y : G, x \in S -> y \in S -> x != y -> ~~ (x -- y)) (stable S).
Proof.
apply: (iffP (stableP S)) => [st x y xS yS _|st x y xS yS]; first exact: st.
by have [<-|xy] := eqVneq x y; [rewrite sg_irrefl | exact: st].
Qed.

(** The bounded Boolean form with an explicit equality disjunct. *)
Lemma stable_eqbE S :
  stable S = [forall x in S, [forall y in S, (x == y) || ~~ (x -- y)]].
Proof.
apply/stable_distinctP/forall_inP => [st x xS|st x y xS yS xy].
  by apply/forall_inP => y yS; have [//|xy] := eqVneq x y; exact: st.
by have /forall_inP/(_ y yS) := st x xS; rewrite (negbTE xy).
Qed.

(** Two vertices form a stable set exactly when they are nonadjacent. *)
Lemma stable_pair (x y : G) : stable [set x; y] = ~~ (x -- y).
Proof.
apply/stable_nonadjP/idP => [st|xy u v]; first by apply: st; rewrite !inE eqxx ?orbT.
by rewrite !inE => /orP[]/eqP-> /orP[]/eqP->; rewrite ?sg_irrefl // sg_sym.
Qed.

End StableSetViews.

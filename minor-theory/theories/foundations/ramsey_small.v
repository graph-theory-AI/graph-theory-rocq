(** * Minor.foundations.ramsey_small -- a finite Ramsey bound for the width edges

    The width-parameter edges of waves X42 / X220 need one quantitative
    ingredient beyond the tree-decomposition bookkeeping: a set with independence
    number at most [a] and no clique on [s] vertices is SMALL.  That is finite
    Ramsey, in exactly the "bounded size" form the edges use, and it is proved
    here by the classical double induction: pick a vertex [v] of the set and
    split the set into [v], its neighbours (where the clique parameter drops,
    because [v] is adjacent to all of them) and its non-neighbours (where the
    independence parameter drops, because [v] extends every stable set there).

    The clique hypothesis is stated as [#|S| != s] rather than [#|S| < s]: it is
    the weaker hypothesis (so the lemma is stronger), and it is what the callers
    have -- "no INDUCED ['K_s]" only forbids cliques of size exactly [s].

    Also here: [alphaS] (monotonicity of the independence number in the set) and
    the two "extend by [v]" lemmas on cliques and stable sets, which are the
    combinatorial content of the induction step. *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma alphaS (G : sgraph) (A B : {set G}) : A \subset B -> α(A) <= α(B).
Proof.
move=> sub; case: (alphaP A) => S HS.
apply: stabset_bound; rewrite in_stabsets (maxstabset_stable HS) andbT.
exact: subset_trans (maxstabsetS HS) sub.
Qed.

Lemma clique_set0 (G : sgraph) : clique (set0 : {set G}).
Proof. by move=> x y; rewrite inE. Qed.

Lemma clique_addv (G : sgraph) (A : {set G}) (v : G) (S : {set G}) :
  S \subset [set x in A | x -- v] -> clique S -> clique (v |: S).
Proof.
move=> sS cS x y; rewrite !inE => /orP[/eqP->|xS] /orP[/eqP->|yS] xy.
- by rewrite eqxx in xy.
- by move: (subsetP sS _ yS); rewrite !inE => /andP[_ h]; rewrite sgP.
- by move: (subsetP sS _ xS); rewrite !inE => /andP[_ h].
- exact: (cS _ _ xS yS xy).
Qed.

Lemma stable_addv (G : sgraph) (A : {set G}) (v : G) (S : {set G}) :
  S \subset [set x in A | (x != v) && ~~ (x -- v)] -> stable S -> stable (v |: S).
Proof.
move=> sS /stableP stS; apply/stableP => x y.
rewrite !inE => /orP[/eqP->|xS] /orP[/eqP->|yS].
- by rewrite sg_irrefl.
- by move: (subsetP sS _ yS); rewrite !inE => /andP[_ /andP[_ h]]; rewrite sgP.
- by move: (subsetP sS _ xS); rewrite !inE => /andP[_ /andP[_ h]].
- exact: (stS _ _ xS yS).
Qed.

(** Finite Ramsey, in the "bounded size" form needed by the width edges: a set
    with independence number at most [a] and no clique on [s] vertices has
    bounded size.  Classical double induction on [s] and [a]: pick [v] in the
    set and split it into [v], its neighbours (clique parameter drops) and its
    non-neighbours (independence parameter drops). *)
Lemma ramsey_bound (s : nat) : forall a : nat, exists N : nat,
  forall (G : sgraph) (A : {set G}),
    α(A) <= a ->
    (forall S : {set G}, S \subset A -> clique S -> #|S| != s) ->
    #|A| <= N.
Proof.
elim: s => [|s IHs] a.
- exists 0 => G A _ h.
  by move: (h set0 (sub0set A) (@clique_set0 G)); rewrite cards0 eqxx.
- elim: a => [|a IHa].
  + exists 0 => G A a0 _.
    have /eqP -> : A == set0 by rewrite -alpha_eq0 -leqn0.
    by rewrite cards0.
  + have [N1 H1] := IHs a.+1.
    have [N2 H2] := IHa.
    exists (N1 + N2).+1 => G A aA cl.
    have [->|AN0] := eqVneq A set0; first by rewrite cards0.
    have /set0Pn[v vA] := AN0.
    pose A1 : {set G} := [set x in A | x -- v].
    pose A2 : {set G} := [set x in A | (x != v) && ~~ (x -- v)].
    have A1A : A1 \subset A by apply/subsetP => x; rewrite !inE => /andP[].
    have A2A : A2 \subset A by apply/subsetP => x; rewrite !inE => /andP[].
    have vA1 : v \notin A1 by rewrite /A1 !inE sg_irrefl andbF.
    have vA2 : v \notin A2 by rewrite /A2 !inE eqxx andbF.
    have sub : A \subset [set v] :|: (A1 :|: A2).
      apply/subsetP => x xA; rewrite /A1 /A2 !inE xA.
      by case: (x == v); case: (x -- v).
    have c1 : #|A1| <= N1.
      apply: (H1 G); first by apply: leq_trans (alphaS A1A) aA.
      move=> S sS cS.
      have vS : v \notin S by apply/negP => h; move: vA1; rewrite (subsetP sS _ h).
      have subA : (v |: S) \subset A.
        by rewrite subUset sub1set vA (subset_trans sS A1A).
      move: (cl _ subA (clique_addv sS cS)).
      by rewrite cardsU1 vS /= -eqSS.
    have c2 : #|A2| <= N2.
      apply: (H2 G); last first.
        by move=> S sS cS; apply: cl (subset_trans sS A2A) cS.
      case: (alphaP A2) => S HS.
      have vS : v \notin S.
        by apply/negP => h; move: vA2; rewrite (subsetP (maxstabsetS HS) _ h).
      have subA : (v |: S) \subset A.
        by rewrite subUset sub1set vA (subset_trans (maxstabsetS HS) A2A).
      have hb : #|v |: S| <= α(A).
        apply: stabset_bound; rewrite in_stabsets subA /=.
        exact: (stable_addv (maxstabsetS HS) (maxstabset_stable HS)).
      move: hb; rewrite cardsU1 vS /= => h.
      by rewrite -ltnS; apply: leq_trans h aA.
    apply: leq_trans (subset_leq_card sub) _.
    apply: leq_trans (leq_card_setU _ _).1 _.
    rewrite cards1 ltnS.
    apply: leq_trans (leq_card_setU _ _).1 _.
    exact: leq_add c1 c2.
Qed.

Print Assumptions alphaS.
Print Assumptions ramsey_bound.

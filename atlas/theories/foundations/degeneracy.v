(** * Atlas.foundations.degeneracy -- greedy colouring and dense cores

    If every nonempty subset of [S] has a vertex of inner degree below [d], then
    [S] is properly [d]-colourable (greedy colouring along the degeneracy order);
    contrapositively a graph of chromatic number above [d] has a nonempty vertex
    set in which every vertex has at least [d] neighbours.  General chromatic
    facts that would belong in [chromatic-theory]'s foundations; kept in the atlas
    because that package is not owned by this wave. *)

From GTBase Require Import base.
From Chromatic.foundations Require Import chi_bounding.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Greedy colouring along a degeneracy order: if every nonempty subset of [S]
    has a vertex with fewer than [d] neighbours inside it, [S] is properly
    [d]-colourable ([0 < d]). *)
Lemma degenerate_colouring (G : sgraph) (d : nat) (S : {set G}) : 0 < d ->
  (forall T : {set G}, T \subset S -> T != set0 ->
     exists2 v, v \in T & #|N(v) :&: T| < d) ->
  exists f : G -> 'I_d, forall x y, x \in S -> y \in S -> x -- y -> f x != f y.
Proof.
move=> d0; move: {2}#|S| (leqnn #|S|) => n; elim: n S => [|n IH] S.
  rewrite leqn0 cards_eq0 => /eqP -> _.
  by exists (fun _ => Ordinal d0) => x y; rewrite inE.
move=> Sn H.
case: (eqVneq S set0) => [->|S0].
  by exists (fun _ => Ordinal d0) => x y; rewrite inE.
have [v vS dv] := H S (subxx S) S0.
have [||f hf] := IH (S :\ v).
- by rewrite -ltnS (leq_trans _ Sn) // (cardsD1 v S) vS.
- by move=> T TS T0; apply: H T0; exact: subset_trans TS (subsetDl _ _).
have [c hc] : exists c : 'I_d, c \notin f @: (N(v) :&: S).
  have small : #|f @: (N(v) :&: S)| < #|'I_d|.
    by rewrite card_ord (leq_ltn_trans (leq_imset_card _ _)).
  have nz : 0 < #|~: (f @: (N(v) :&: S))| by rewrite cardsCs setCK subn_gt0.
  by have [c] := card_gt0P nz; exists c; move: p; rewrite inE.
have spare z : z \in S -> v -- z -> c != f z.
  move=> zS vz; apply: contraNneq hc => ->; apply/imsetP; exists z => //.
  by rewrite !inE vz.
exists (fun x => if x == v then c else f x) => x y xS yS xy.
case: (eqVneq x v) => [ex|nx]; case: (eqVneq y v) => [ey|ny].
- by subst; rewrite sg_irrefl in xy.
- by subst x; apply: spare.
- by subst y; rewrite eq_sym; apply: spare => //; rewrite sg_sym.
- by apply: hf => //; rewrite !inE ?nx ?ny.
Qed.

(** A graph with [d < chi] has a nonempty vertex set [S] in which every vertex
    has at least [d] neighbours. *)
Lemma dense_core_of_chi (G : sgraph) (d : nat) : 0 < d -> d < χ([set: G]) ->
  exists2 S : {set G}, S != set0 & forall v, v \in S -> d <= #|N(v) :&: S|.
Proof.
move=> d0 dchi.
case: (boolP [exists S : {set G}, (S != set0) && [forall v in S, d <= #|N(v) :&: S|]]).
  by case/existsP => S /andP [S0 /forall_inP h]; exists S.
move=> nex; exfalso.
have [|f hf] := @degenerate_colouring G d [set: G] d0.
  move=> T _ T0; move: nex; rewrite negb_exists => /forallP /(_ T).
  rewrite T0 /= negb_forall_in => /exists_inP [v vT]; rewrite -ltnNge => lt.
  by exists v.
have := chi_le_palette (f := f) (fun x y xy => hf x y (in_setT x) (in_setT y) xy).
by rewrite card_ord leqNgt dchi.
Qed.

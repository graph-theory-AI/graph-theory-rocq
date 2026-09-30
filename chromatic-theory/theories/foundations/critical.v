(** * Chromatic.foundations.critical -- criticality helpers for the chromatic number

    Elementary facts about [chi_mem] that coq-graph-theory does not provide and
    that the criticality edge of wave X213 needs (corpus relation e228,
    Erdos-Lovasz-Tihany ==> the double-critical graph conjecture):

      [sg_has_neighbour]      -- in a connected graph with at least two vertices
                                 every vertex has a neighbour;
      [chi_le1_stable]        -- a stable set has chromatic number at most one;
      [chi_gt1_edge]          -- conversely, chromatic number at least two
                                 produces an edge inside the set;
      [omega_le1_stableT]     -- clique number at most one means no edge at all;
      [double_critical_del1]  -- a DOUBLE-critical graph is VERTEX-critical in the
                                 weak sense that deleting ONE vertex strictly
                                 lowers the chromatic number;
      [clique_of_chi_full]    -- in a graph that is vertex-critical in that weak
                                 sense, a clique whose size is the chromatic
                                 number is the whole vertex set.

    [double_critical_del1] takes double-criticality as an explicit hypothesis, in
    the unfolded form of [U1.double_critical], so that this foundation file
    depends on no conjecture file. *)

From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Critical.
Variable G : sgraph.

(** In a connected graph with at least two vertices every vertex has a
    neighbour: walk from [v] to any other vertex and take the first step. *)
Lemma sg_has_neighbour :
  connected [set: G] -> 2 <= #|G| -> forall v : G, exists u : G, v -- u.
Proof.
move=> con cd v.
have [u uv] : exists u : G, u != v.
  move: cd; rewrite -cardsT => /card_gt1P[x [y [_ _ xy]]].
  case: (eqVneq x v) => [xv|xv]; last by exists x.
  by exists y; rewrite -xv eq_sym.
have /connectP[p pth lastp] := connectedTE con v u.
case: p pth lastp => [|a p'] /=; first by move=> _ e; rewrite e eqxx in uv.
by move=> /andP[va _] _; exists a.
Qed.

(** A stable set is 1-colourable. *)
Lemma chi_le1_stable (A : {set G}) : stable A -> χ(A) <= 1.
Proof. by move=> st; have := chiD1 A st; rewrite setDv chi0. Qed.

(** ... hence a set with no internal edge is 1-colourable. *)
Lemma chi_le1_of_no_edge (A : {set G}) :
  (forall x y : G, x \in A -> y \in A -> ~~ (x -- y)) -> χ(A) <= 1.
Proof. by move=> h; apply: chi_le1_stable; apply/stableP => u v uA vA; exact: h. Qed.

(** Two colours are needed only if there is an edge inside the set. *)
Lemma chi_gt1_edge (A : {set G}) :
  1 < χ(A) -> exists x y : G, [/\ x \in A, y \in A & x -- y].
Proof.
move=> lt.
have: [exists x, exists y, [&& x \in A, y \in A & x -- y]].
  case: (boolP [exists x, exists y, [&& x \in A, y \in A & x -- y]]) => // hn.
  suff : χ(A) <= 1 by rewrite leqNgt lt.
  apply: chi_le1_of_no_edge => x y xA yA.
  move/existsPn: hn => /(_ x) /existsPn /(_ y).
  by rewrite xA yA.
by case/existsP=> x /existsP[y /and3P[xA yA xy]]; exists x, y; split.
Qed.

(** Clique number at most one means: no edge at all. *)
Lemma omega_le1_stableT : ω([set: G]) <= 1 -> stable [set: G].
Proof.
move=> w1; apply/stableP => u v _ _; apply/negP => uv.
have uvne : u != v by apply: contraTneq uv => ->; rewrite sg_irrefl.
have cl : [set u; v] \in cliques [set: G].
  rewrite inE subsetT /=; apply/cliqueP => x y; rewrite !inE.
  case/orP=> /eqP->; case/orP=> /eqP-> ne.
  - by rewrite eqxx in ne.
  - exact: uv.
  - by rewrite sgP.
  - by rewrite eqxx in ne.
have := clique_bound cl; rewrite cards2 uvne /=.
by rewrite leqNgt (leq_ltn_trans w1).
Qed.

(** A double-critical graph is vertex-critical (weak form): deleting a single
    vertex strictly lowers the chromatic number.  Indeed [v] has a neighbour [u],
    deleting both drops chi by exactly two, and putting [u] back can raise it by
    at most one. *)
Lemma double_critical_del1 :
  (forall x y : G, x -- y -> χ([set: G] :\: [set x; y]) + 2 = χ([set: G])) ->
  connected [set: G] -> 2 <= #|G| ->
  forall v : G, χ([set: G] :\: [set v]) < χ([set: G]).
Proof.
move=> dc con cd v.
have [u vu] := sg_has_neighbour con cd v.
have stu : stable [set u].
  by apply/stableP => x y; rewrite !inE => /eqP-> /eqP->; rewrite sg_irrefl.
have step := chiD1 ([set: G] :\: [set v]) stu.
rewrite setDDl in step.
by rewrite -(dc v u vu) addn2 ltnS.
Qed.

(** In a graph that is vertex-critical in the above weak sense, a clique of size
    [chi] must be the whole vertex set: a vertex outside it could be deleted,
    and the clique would survive with the full chromatic number. *)
Lemma clique_of_chi_full (K : {set G}) :
  clique K -> #|K| = χ([set: G]) ->
  (forall v : G, χ([set: G] :\: [set v]) < χ([set: G])) ->
  clique [set: G].
Proof.
move=> clK cardK crit.
suff KT : K = [set: G] by rewrite -KT.
apply/eqP; rewrite eqEsubset subsetT /=; apply/subsetP=> v _.
case: (boolP (v \in K)) => // vK.
have sub : K \subset [set: G] :\: [set v].
  apply/subsetP=> x xK; apply/setDP; split; first by rewrite inE.
  by rewrite inE; apply: contraNneq vK => <-.
have := leq_ltn_trans (sub_chi sub) (crit v).
by rewrite (chi_clique clK) cardK ltnn.
Qed.

End Critical.

Print Assumptions sg_has_neighbour.
Print Assumptions chi_gt1_edge.
Print Assumptions omega_le1_stableT.
Print Assumptions double_critical_del1.
Print Assumptions clique_of_chi_full.

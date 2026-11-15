(** * Extremal.conjectures.implications_X310 -- a dependency-graph EDGE with an X310 endpoint.

    Same role as [implications_X309.v]: a machine-checked implication between two statements of
    extremal-graph-theory.  The edge is a RELATIVE theorem: a [Qed]-closed [Theorem A -> B] proved WITHOUT resolving
    either endpoint.  Axiom-free: no [Axiom] / [Parameter] / [Admitted] / [Conjecture].

    The edge below is a Rocq-only edge (no corpus relation): the fractional 8/3 conjecture of Cames van Batenburg,
    Goedgebeur and Joret (X310: a triangle-free subcubic G containing none of the six graphs [x287_bb_graph i] as a
    subgraph has an (a:b)-fold colouring with a / b <= 8/3) implies the Fraughnaugh-Locke statement (X309: such a G
    has 3 #|G| <= 8 alpha(G)), as its record says: the conjecture extends the main theorem to fractional colourings
    (arXiv:1911.12471v2, Revision_IndependenceRatio8over3.tex l.2072-2076, the main theorem l.243-246), and
    n / alpha(G) <= chi_f(G) (l.2062).  The counting is grounding_X310's [g310_bfold_n_alpha]: an (a:b)-fold colouring
    of G gives #|G| * b <= a * alpha(G) (each of the a colour classes is stable, and every vertex lies in b of them);
    with 3 a <= 8 b and 0 < b, 3 #|G| <= 8 alpha(G).
    X309 is true before the pin (Theorem 7 of arXiv:1911.12471v2, recorded solved through ERRATA by lit35); X310 is
    open; the edge relates them as encoded. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph.
From GTBase Require Import base common.
From Extremal.conjectures Require Import X309 X310 grounding_X310.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The fractional 8/3 conjecture (X310) ==> Fraughnaugh-Locke (X309) *)

(*@EDGE from=cames_van_batenburg_forbidden_subgraph_fractional_statement to=fraughnaugh_locke_forbidden_subgraph_independence_statement kind=implies status=verified proof=cames_van_batenburg_forbidden_subgraph_fractional_implies_fraughnaugh_locke_forbidden_subgraph_independence note="Rocq-only edge (no corpus relation), routed by Lancelot's NOTE 2026-11-15T12:15:05Z: the fractional 8/3 conjecture (X310) implies the Fraughnaugh-Locke statement (X309), as arXiv:1911.12471v2 l.2062 and l.2072-2076 say (n / alpha <= chi_f, and the conjecture extends the main theorem l.243-246 to fractional colourings). For G meeting the three common hypotheses, X310 gives an (a:b)-fold colouring with 0 < b and 3 a <= 8 b; grounding_X310's g310_bfold_n_alpha gives #|G| * b <= a * alpha(G), so 3 #|G| b <= 3 a alpha(G) <= 8 b alpha(G), and 3 #|G| <= 8 alpha(G) since b > 0. X309 is true before the pin (Theorem 7 of arXiv:1911.12471v2); X310 is open." *)
Theorem cames_van_batenburg_forbidden_subgraph_fractional_implies_fraughnaugh_locke_forbidden_subgraph_independence :
  cames_van_batenburg_forbidden_subgraph_fractional_statement ->
  fraughnaugh_locke_forbidden_subgraph_independence_statement.
Proof.
move=> hC G tf sc nf.
have [a [b [f [b0 cf ab]]]] := hC G tf sc nf.
have hn : #|G| * b <= a * α([set: G]) := g310_bfold_n_alpha cf.
rewrite -(leq_pmul2r b0).
apply: (@leq_trans (3 * (a * α([set: G])))).
  by rewrite -mulnA leq_mul2l hn orbT.
have e1 : 3 * (a * α([set: G])) = a * 3 * α([set: G]) by rewrite mulnA (mulnC 3 a).
have e2 : 8 * α([set: G]) * b = 8 * b * α([set: G]) by rewrite -!mulnA (mulnC b).
by rewrite e1 e2 leq_mul2r ab orbT.
Qed.

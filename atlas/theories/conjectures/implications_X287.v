(** * Atlas.conjectures.implications_X287 -- a cross-package dependency-graph EDGE with an X287 endpoint.

    Same role as [implications_A1.v]: a machine-checked implication between statements of two
    packages (extremal-graph-theory and graph-theory-misc), hosted in the atlas.  The edge is a
    RELATIVE theorem: a [Qed]-closed [Theorem A -> B] proved WITHOUT resolving either endpoint.
    Axiom-free: no [Axiom] / [Parameter] / [Admitted] / [Conjecture].

    The edge below is a Rocq-only edge (no corpus relation): the Bajnok-Brinkmann conjecture
    (X287: every 2-connected triangle-free subcubic graph G with 8 alpha(G) < 3n is isomorphic to
    one of six fixed graphs) implies Locke's conjecture (X285: the 3-connected triangle-free cubic
    graphs with 8 alpha(G) < 3n have bounded order).  A 3-connected cubic graph is 2-connected and
    subcubic, and isomorphic graphs have the same order, so the bound is the largest order of the
    six graphs (22).  Both statements are true before the pin (Corollary 8 of arXiv:1911.12471v2,
    recorded through ERRATA by lit23); the edge relates them as encoded. *)

From GTBase Require Import base.
From GraphTheory Require Import bij.
From Extremal.conjectures Require Import X287.
From GTMisc.conjectures Require Import X285.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Bajnok-Brinkmann (X287) ==> Locke (X285) *)

(*@EDGE from=bajnok_brinkmann_six_exceptional_graphs_statement to=locke_finitely_many_statement kind=implies status=verified proved=true proof=bajnok_brinkmann_six_exceptional_graphs_implies_locke_finitely_many note="Rocq-only edge (no corpus relation), noted with X287's selection (Marcol's (362), Lancelot's (459)): a 3-connected cubic graph is 2-connected (k_connected is monotone in k) and subcubic (regular_subcubic), so the first clause of the Bajnok-Brinkmann statement makes it isomorphic to one of the six graphs (card_bij of the isomorphism), and N is the largest of their orders (22)." *)
Theorem bajnok_brinkmann_six_exceptional_graphs_implies_locke_finitely_many :
  bajnok_brinkmann_six_exceptional_graphs_statement -> locke_finitely_many_statement.
Proof.
case=> H _ _.
exists (\max_(i < 6) #|x287_bb_graph i|); move=> G [n3 h3] tf reg ha.
have k2 : k_connected G 2.
  split; first exact: ltn_trans (ltnSn 2) n3.
  by move=> S hS; apply: h3; exact: ltn_trans hS (ltnSn 2).
have [i [f]] := H G k2 tf (regular_subcubic reg (leqnn 3)) ha.
by rewrite (card_bij (diso_v f)); exact: leq_bigmax.
Qed.

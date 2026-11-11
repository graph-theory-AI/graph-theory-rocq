(** * GTMisc.conjectures.implications_X300 -- a cross-package dependency-graph EDGE with an X300 endpoint.

    A machine-checked implication between statements of two packages (minor-theory and
    topological-graph-theory), hosted in graph-theory-misc, whose _CoqProject maps both (as X102
    imports Minor.conjectures.X27).  The edge is a RELATIVE theorem: a [Qed]-closed
    [Theorem A -> B] proved WITHOUT resolving either endpoint.  Axiom-free: no [Axiom] /
    [Parameter] / [Admitted] / [Conjecture].

    The edge below is a Rocq-only edge (no corpus relation): Grytczuk's conjecture (X300: for every
    graph X some k bounds the nonrepetitive chromatic number of every X-minor-free graph) implies
    the conjecture of Alon, Grytczuk, Haluszczak and Riordan (X23: planar graphs have bounded
    nonrepetitive chromatic number).  Take X = K_5: X23's planarity [wagner_planar] excludes a K_5
    minor, so X300's bound k serves, widened to k + 1 colours for X23's positive k.  X23's
    nonrepetitive colouring compares [take h p] with [take h (drop h p)], which is [drop h p] for a
    path on 2h vertices, X300's form.  Both statements are true before the pin (arXiv:1904.05269v4,
    Theorems 1 and 3, recorded through ERRATA by lit30 and lit33); the edge relates them as
    encoded. *)

From GTBase Require Import base.
From Minor.conjectures Require Import X300.
From Topological.conjectures Require Import X23.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Grytczuk (X300) ==> Alon, Grytczuk, Haluszczak and Riordan (X23) *)

(*@EDGE from=grytczuk_minor_free_nonrepetitive_statement to=planar_bounded_nonrepetitive_chromatic_statement kind=implies status=verified proved=true proof=grytczuk_minor_free_nonrepetitive_implies_planar_bounded_nonrepetitive_chromatic note="Rocq-only edge (no corpus relation), routed after wave X300 (Lancelot's (667)): X300 at X = K_5, since wagner_planar excludes a K_5 minor; the bound k becomes k + 1 colours by widen_ord (injective, so the halves stay different), and take h (drop h p) = drop h p for a path on 2h vertices." *)
Theorem grytczuk_minor_free_nonrepetitive_implies_planar_bounded_nonrepetitive_chromatic :
  grytczuk_minor_free_nonrepetitive_statement -> planar_bounded_nonrepetitive_chromatic_statement.
Proof.
move=> S; have [k Hk] := S 'K_5.
exists k.+1; split=> // G [nK5 _].
have [col Hc] := Hk G nK5.
exists (fun v => widen_ord (leqnSn k) (col v)) => p h gp sz h0.
have ->: take h (drop h p) = drop h p.
  by apply: take_oversize; rewrite size_drop sz mul2n -addnn addnK.
have winj : injective (widen_ord (leqnSn k)).
  by move=> i j E; apply: val_inj; exact: (congr1 val E).
apply: contraNneq (Hc p h gp sz h0) => E; apply/eqP; apply: (inj_map winj).
by rewrite -!map_comp; exact: E.
Qed.

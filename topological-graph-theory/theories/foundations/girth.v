(** * Topological.foundations.girth -- girth at least 4 is triangle-freeness

    Wave V (2026-09-24).  meta/STATEMENT_IMPROVEMENTS.md (section
    "## topological-graph-theory", entry
    [studies:std_esperet_joret_question_on_clustered_colouring_of], X138.v)
    records that triangle-freeness is written [girth_geq G 4] there rather than
    with base's [triangle_free] -- "equivalent for simple graphs, but a different
    notion read literally".  This file proves that equivalence, so the two
    spellings can be exchanged without changing any statement body.

    Both notions are GTBase/library vocabulary ([base.girth_geq],
    [base.triangle_free], MathComp's [ucycle]), so the lemma belongs in
    [foundations/].

    Axiom-free: no Axiom/Parameter/Admitted. *)

From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A triangle of [G] is a [ucycle] of size 3. *)
Lemma triangle_ucycle (G : sgraph) (x y z : G) :
  x -- y -> y -- z -> z -- x -> ucycle (--) [:: x; y; z].
Proof.
move=> xy yz zx; rewrite /ucycle /= xy yz zx !inE !andbT /=.
by rewrite (sg_edgeNeq xy) (sg_edgeNeq yz) eq_sym (sg_edgeNeq zx).
Qed.

(** Conversely a [ucycle] of size 3 is a triangle. *)
Lemma ucycle3_triangle (G : sgraph) (c : seq G) :
  ucycle (--) c -> size c = 3 ->
  exists x y z : G, [/\ c = [:: x; y; z], x -- y, y -- z & z -- x].
Proof.
case: c => [|x [|y [|z [|w s]]]] // /andP[] /=.
by rewrite !andbT => /andP[xy /andP[yz zx]] _ _; exists x, y, z; split.
Qed.

(** Girth at least 4 is exactly triangle-freeness. *)
Lemma girth_geq4_equiv_triangle_free (G : sgraph) :
  girth_geq G 4 <-> triangle_free G.
Proof.
split=> [g4 x y z xy yz zx|tf c uc c2].
  by move: (g4 [:: x; y; z] (triangle_ucycle xy yz zx) (isT : 2 < 3)).
have {}c2 : 3 <= size c by exact: c2.
rewrite ltn_neqAle c2 andbT eq_sym; apply/eqP => c3.
by have [x [y [z [_ xy yz zx]]]] := ucycle3_triangle uc c3; exact: (tf _ _ _ xy yz zx).
Qed.

Print Assumptions girth_geq4_equiv_triangle_free.

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

    A15 (2026-10-03): the three proofs moved unchanged to GTBase.base, which owns
    the public bridge; the lemmas below keep their qualified names and statements.

    Axiom-free: no Axiom/Parameter/Admitted. *)

From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A triangle of [G] is a [ucycle] of size 3. *)
Lemma triangle_ucycle (G : sgraph) (x y z : G) :
  x -- y -> y -- z -> z -- x -> ucycle (--) [:: x; y; z].
Proof. exact: GTBase.base.triangle_ucycle. Qed.

(** Conversely a [ucycle] of size 3 is a triangle. *)
Lemma ucycle3_triangle (G : sgraph) (c : seq G) :
  ucycle (--) c -> size c = 3 ->
  exists x y z : G, [/\ c = [:: x; y; z], x -- y, y -- z & z -- x].
Proof. exact: GTBase.base.ucycle3_triangle. Qed.

(** Girth at least 4 is exactly triangle-freeness. *)
Lemma girth_geq4_equiv_triangle_free (G : sgraph) :
  girth_geq G 4 <-> triangle_free G.
Proof. exact: GTBase.base.girth_geq4_equiv_triangle_free. Qed.

Print Assumptions girth_geq4_equiv_triangle_free.

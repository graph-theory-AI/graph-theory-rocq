(** * Topological.conjectures.implications_U13 — milestone U13 edges

    Implication / refutation EDGES among the four U13 planar nodes
    (large induced forest; Earth–Moon; Wegner square-colouring; degenerate
    colouring), as Qed-closed RELATIVE theorems where one exists.

    OUTCOME (honest).  The four U13 rows are four MUTUALLY-INDEPENDENT famous
    open problems, grouped only by topic (planarity).  The verified-literature
    edge table of OPG_FULL_FORMALIZATION_PLAN.md §6 lists NONE of them: there is
    no textbook "A ⟹ B" between any pair.  Consequently this milestone schedules
    ZERO verified edges — there is no real [Theorem A_implies_B. Qed] to add,
    because forcing one would either fail to compile or misstate the
    mathematics.  Per the edge policy a false/unclosing edge must NOT be forced.

    The single literature-MOTIVATED direction is recorded as a CANDIDATE
    annotation only (proved=false): the degenerate-colouring conjecture's k = 2
    clause makes the union of any two colour classes 1-degenerate, i.e. an
    induced forest (this is exactly an acyclic 5-colouring).  Taking the two
    largest of the five classes yields an induced forest on ≥ 2n/5 vertices
    (Albertson–Berman / Borodin), which is STRICTLY short of the n/2 (i.e.
    [#|G| <= 2*#|S|]) demanded by [large_induced_forest_in_a_planar_graph_statement].
    The constant gap 2/5 < 1/2 is real (five equal colour classes is a witness:
    every 2-class union has exactly 2n/5 vertices), so the implication does NOT
    close as a relative theorem and the edge stays a candidate, never scheduled.
    This is the same "looks-like-an-edge but the constant is wrong" pattern as
    the §6 withdrawn edges (list-total ⟹ Behzad, list-Hadwiger ⟹ Hadwiger).

    The file imports Topological.conjectures.U13, so the edge endpoints are U13's own
    statements (concrete [wagner_planar]).  Until 2026-10-27 it re-stated the four nodes over a
    universally-quantified oracle [is_planar : sgraph -> Prop] (the pre-G2 encoding, which had
    diverged from U13.v and is false at [is_planar := fun _ => True]); the re-audit of
    2026-10-27 (Lancelot; reviewer Arthur) removed those copies and their helpers, so that no
    statement name is defined twice.  Axiom-free: no Conjecture/Axiom/Parameter/Admitted, and
    no [Theorem … Qed] asserting an unproven edge. *)

From GTBase Require Import base.
From Topological.conjectures Require Import U13.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Edges

    No verified-literature edge exists among the four nodes (plan §6 lists
    none).  The only literature-motivated direction is a CANDIDATE blocked by a
    constant gap, recorded as an annotation only — there is no Qed theorem for
    it because it does not logically close. *)

(*@EDGE from=degenerate_colorings_of_planar_graphs_statement to=large_induced_forest_in_a_planar_graph_statement kind=implies status=refuted-direction cite="Albertson & Berman 1979 (induced-forest conj.); Borodin 1979 (acyclic 5-colouring of planar graphs)" note="REFUTED-DIRECTION (metadata wave M, 2026-09-24): strict weakening: the best 2-class union gives 2n/5 < n/2 (five equal classes show 2/5 is unimprovable by this route). Earlier note: k=2 clause: union of any two of the five colour classes is 1-degenerate, i.e. an induced forest (acyclic colouring). Largest 2-class union has only >= 2n/5 vertices, strictly short of the n/2 (#|G| <= 2*#|S|) required by the target. Five equal classes is a witness that 2/5 cannot be improved by this argument, so the edge does NOT close; candidate, never scheduled." *)

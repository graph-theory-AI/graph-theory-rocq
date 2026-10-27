(** * GTMisc.conjectures.implications_U13 — milestone U13 (misc) edges

    Implication / refutation EDGES among the twelve U13 "miscellaneous graph
    theory" nodes (Row 1 monochromatic-max-clique 2-colouring; Row 2
    book-thickness of subdivisions; Row 3 high-girth subgraph of large average
    degree; Row 4 union of degenerate graphs; Row 5 shuffle-exchange; Row 6
    pebbling of a Cartesian product; Row 7 the 57-regular Moore graph; Row 8
    Graceful Tree; Row 9 imbalance; Row 10 gold-grabbing game; Row 11 Beneš;
    Row 12 weighted colouring of hexagonal graphs), as Qed-closed RELATIVE
    theorems where one genuinely exists.

    OUTCOME (honest).  These twelve rows are MUTUALLY-INDEPENDENT open problems
    grouped only by the "miscellaneous" bucket; they share no textbook
    "A ⟹ B".  The verified-literature edge table of
    OPG_FULL_FORMALIZATION_PLAN.md §6 lists NONE of them.  Consequently this
    milestone schedules ZERO verified edges — there is no real
    [Theorem A_implies_B. Qed] to add, and per the edge policy a
    false/unclosing edge must NOT be forced (it must simply fail to compile).

    The single literature-MOTIVATED direction is the multistage-network pair
    (Rows 5 and 11), recorded below as a CANDIDATE annotation only
    (proved=false).  Beneš in the graph-theoretic form
    [bene_conjecture_graph_theoretic_form_0_statement] is the GENERAL claim:
    every square stage-regular relation [L] that is externally connected in [m]
    steps is rearrangeable in [2*m] stages.  The shuffle-exchange graph
    [se_adj k n] is one such network, externally connected in [n-1] steps, so
    Beneš would yield rearrangeability of [se_adj] at [2*(n-1) = 2*n-2] stages —
    EXACTLY the UPPER-BOUND conjunct of
    [shuffle_exchange_conjecture_statement].  But that statement is a CONJUNCTION
    whose second conjunct is the matching LOWER bound (optimality:
    [2*n-1 <= r] whenever [r-1] stages already rearrange), which Beneš does NOT
    deliver and which is itself open.  Hence the edge does NOT close as a
    relative theorem: deriving the full target from Beneš would require proving
    the open optimality conjunct, and additionally the external facts that
    [se_adj k n] is stage-regular and externally connected in [n-1] steps.  The
    direction therefore stays a candidate, never scheduled — the same
    "looks-like-an-edge but the target carries an extra open conjunct" pattern
    as the §6 withdrawn edges (list-total ⟹ Behzad, list-Hadwiger ⟹ Hadwiger).

    The file imports GTMisc.conjectures.U13, so the edge endpoints and their helpers are
    U13's own definitions.  Until 2026-10-27 it re-stated them verbatim (byte-identical
    bodies); the re-audit of 2026-10-27 (Lancelot; reviewer Arthur) removed the copies so
    that no statement name is defined twice.  Axiom-free: no Conjecture/Axiom/Parameter/
    Admitted, and no [Theorem … Qed] asserting an unproven edge. *)

From GTBase Require Import base.
From mathcomp Require Import fingroup perm.
From GTMisc.conjectures Require Import U13.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Edges.

    No verified-literature edge exists among the twelve U13 (misc) nodes, so no
    [Theorem … Qed] is asserted here.  The lone literature-motivated direction
    is recorded as a candidate only. *)

(*@EDGE from=bene_conjecture_graph_theoretic_form_0_statement to=shuffle_exchange_conjecture_statement kind=implies status=refuted-direction cite="Beneš 1965; Stone 1971 (shuffle-exchange); Beauquier–Darrot 2002 (graph-theoretic Beneš)" note="REFUTED-DIRECTION (metadata wave M, 2026-09-24): gives only the upper conjunct; the 2n-1 optimality lower bound is itself open. Earlier note: General stage-regular rearrangeability (Beneš) would give the UPPER-bound conjunct (se_adj k n rearrangeable at 2*n-2) via external connectivity of the shuffle-exchange graph in n-1 steps, but shuffle_exchange_conjecture_statement also demands the matching LOWER bound (optimality 2*n-1<=r), which Beneš does not yield and is itself open; also needs external facts that se_adj is stage-regular and externally connected in n-1. Does NOT close as a single relative theorem." *)

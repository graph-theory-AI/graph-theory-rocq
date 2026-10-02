(** * GTMisc.conjectures.vocabulary_misc -- wave-V vocabulary equivalences

    meta/STATEMENT_IMPROVEMENTS.md (section "## graph-theory-misc",
    "### Duplicated vocabulary") lists the local notions of this package that
    duplicate a coq-graph-theory / GTBase notion, or each other.  This file
    records ONE lemma per group of copies so the duplicates can later be retired
    by rewriting with these lemmas.  No statement body is changed.

    Canonical notions: [E(_)] = [sgraph.sg_edge_set] (bridged by
    [GTBase.common.sg_edge_setE]), MathComp's [ucycle], and
    [connectivity.matching].

    PLACEMENT.  Every lemma mentions a notion of a [theories/conjectures/X*.v]
    file, so none may live in [theories/foundations/].  The phases concerned
    (X14, X20, X37, X38, X77, X102, X113, XE1) have no
    [implications_<phase>.v] / [grounding_<phase>.v] file, so the bridges are
    collected here rather than in eight new per-phase files.

    Axiom-free: no Axiom/Parameter/Admitted. *)

From GTBase Require Import base common.
From GTMisc.conjectures Require Import X102 X113 X14 X20 X37 X38 X77 XE1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The edge set of a simple graph: six copies of [E(G)] ***************

    Five of the six are the boolean comprehension of [sg_edge_setE]. *)

Lemma x14_edge_setE (G : sgraph) : x14_edge_set G = E(G).
Proof. by []. Qed.

Lemma x20_edge_setE (G : sgraph) : x20_edge_set G = E(G).
Proof. by []. Qed.

Lemma x37_edge_setE (G : sgraph) : x37_edge_set G = E(G).
Proof. by []. Qed.

Lemma x38_edge_setE (G : sgraph) : x38_edge_set G = E(G).
Proof. by []. Qed.

Lemma x77_edge_setE (G : sgraph) : x77_edge_set G = E(G).
Proof. by []. Qed.

(** The sixth spells an edge as a 2-element CLIQUE instead; the two descriptions
    agree because a 2-set is a clique exactly when its two (distinct) elements
    are adjacent. *)
Lemma x102_edge_setE (G : sgraph) : x102_edge_set G = E(G).
Proof. by []. Qed.

(** ** Cycles: [X113] and [XE1] declare the same [ucycle] wrapper *********)

Lemma x113_is_cycleE (G : sgraph) (c : seq G) :
  x113_is_cycle c = (ucycle (--) c /\ 2 < size c).
Proof. by []. Qed.

Lemma x113_is_cycle_equiv_xe1_rel_cycle (G : sgraph) (c : seq G) :
  x113_is_cycle c <-> xe1_rel_cycle (--) c.
Proof. by split=> H; exact: H. Qed.

(** ** Matchings: [X14]'s pairwise-disjoint form is [connectivity.matching]

    Since the C1 library migration (2026-10-02) [x14_matching] IS a transparent
    alias of [matching], so the bridge holds by reflexivity.  The original
    pairwise-disjoint body is frozen and certified in
    theories/migration/matching.v ([x14_matching_compat]). *)

Lemma x14_matching_equiv_matching (G : sgraph) (M : {set {set G}}) :
  x14_matching M <-> matching M.
Proof. by []. Qed.

Print Assumptions x14_edge_setE.
Print Assumptions x102_edge_setE.
Print Assumptions x113_is_cycle_equiv_xe1_rel_cycle.
Print Assumptions x14_matching_equiv_matching.

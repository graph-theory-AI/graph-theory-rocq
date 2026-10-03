(** * Packing.conjectures.vocabulary_packing -- wave-V vocabulary equivalences

    meta/STATEMENT_IMPROVEMENTS.md (section "## packing-theory",
    "### Duplicated vocabulary") lists the local notions of this package that
    duplicate a coq-graph-theory / GTBase notion, or each other.  This file
    records ONE lemma per group of copies, tying the local spelling to the
    canonical notion, so that the duplicates can later be retired by rewriting
    with these lemmas.  No statement body is changed here.

    Canonical notions used below:
      - [E(_)] = [sgraph.sg_edge_set], with [GTBase.common.sg_edge_setE] as the
        bridging rewrite (base/theories/common.v explains why [common.v]
        deliberately has NO [edge_set]);
      - [connectivity.matching];
      - [GTBase.common.hamiltonian_cycle];
      - and, for the pairs that duplicate each other inside the package, the
        first-declared copy.

    PLACEMENT.  Every lemma mentions a notion defined in a
    [theories/conjectures/X*.v] file, so none may live in [theories/foundations/]
    (a foundations file must not import a conjectures file).  The phases
    concerned (X5, X15, X18, X25, X26, X47, X111, XE1) have no
    [implications_<phase>.v] / [grounding_<phase>.v] file, so the bridges are
    collected here rather than in eight new per-phase files.

    [X15alone.v] is deliberately NOT imported: it is a scratch duplicate that
    [_CoqProject] does not track (ledger, "### Other").

    Axiom-free: no Axiom/Parameter/Admitted. *)

From GTBase Require Import base common.
From Packing.foundations Require Import matching.
From Packing.conjectures Require Import U9 X5 X15 X18 X25 X26 X47 X111 XE1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The edge set of a simple graph: six copies of [E(G)] ***************

    All six local definitions are the boolean comprehension of
    [GTBase.common.sg_edge_setE], hence equal to [E(G)] by that single rewrite. *)

Lemma edge_setGE (G : sgraph) : edge_setG G = E(G).
Proof. by rewrite sg_edge_setE. Qed.

Lemma x5_edge_setE (G : sgraph) : x5_edge_set G = E(G).
Proof. by []. Qed.

Lemma x15_edge_setE (G : sgraph) : x15_edge_set G = E(G).
Proof. by []. Qed.

Lemma x25_edge_setE (G : sgraph) : x25_edge_set G = E(G).
Proof. by []. Qed.

Lemma x47_edge_setE (G : sgraph) : x47_edge_set G = E(G).
Proof. by []. Qed.

Lemma xe1_edge_setE (G : sgraph) : xe1_edge_set G = E(G).
Proof. by []. Qed.

(** ** Hamilton cycles: [U9.hamiltonian_cycleG] is [common.hamiltonian_cycle] *)

Lemma hamiltonian_cycleGE (G : sgraph) (c : seq G) :
  hamiltonian_cycleG G c = hamiltonian_cycle G c.
Proof. by []. Qed.

(** ** Triangles: [U9] and [X5] declare the same two notions **************)

Lemma x5_is_triangle_equiv_is_triangle (G : sgraph) (T : {set G}) :
  x5_is_triangle T <-> is_triangle T.
Proof. by split=> H; exact: H. Qed.

Lemma x5_tri_edgesE (G : sgraph) (T : {set G}) : x5_tri_edges T = tri_edges T.
Proof. by []. Qed.

(** ** Independent / stable sets: [X18] and [XE1] declare the same notion **)

Lemma x18_independent_set_equiv_xe1_stable_set (G : sgraph) (S : {set G}) :
  x18_independent_set S <-> xe1_stable_set S.
Proof. by split=> H; exact: H. Qed.

(** ** Balls: [X26] and [X111] declare the same ball **********************

    Since the A22 library migration (2026-10-03) [x26_ball] and [x111_ball]
    ARE transparent aliases of [GTBase.base.ball], so the two sides are
    convertible and the radius induction below still checks.  The original
    local [Fixpoint]s (not convertible: their recursive calls went through
    two different constants) are frozen and certified in
    theories/migration/balls.v. *)

Lemma x26_ballE (G : sgraph) (r : nat) (x : G) : x26_ball r x = x111_ball r x.
Proof. by elim: r => //= r ->. Qed.

(** ** Matchings: [X15]'s edge-set form is [connectivity.matching] ********

    Since the C1 library migration (2026-10-02) [x15_matching] IS a transparent
    alias of [matching], so the bridge holds by reflexivity.  The original
    body ("every member is an edge, and every vertex lies in at most one
    member"; [card_le1_eqP] apart from the library clause) is frozen and
    certified in theories/migration/matching.v; the general presentation lemma
    is [Packing.foundations.matching.matching_at_most_oneP]. *)

Lemma x15_matching_equiv_matching (G : sgraph) (M : {set {set G}}) :
  x15_matching M <-> matching M.
Proof. by []. Qed.

(** ** Perfect matchings: [X18] and [X25] declare the same notion *********

    Since the C2 library migration (2026-10-02) both [x18_perfect_matching] and
    [x25_perfect_matching] ARE transparent aliases of
    [GTBase.common.perfect_matching], so the bridge holds by reflexivity.  The
    original bodies ([x15_matching] saturating every vertex; a set of edges
    saturating every vertex) are frozen and certified in
    theories/migration/matching.v (C1) and theories/migration/simple_edges.v (M1). *)

Lemma x18_perfect_matching_equiv_x25_perfect_matching
    (G : sgraph) (M : {set {set G}}) :
  x18_perfect_matching M <-> x25_perfect_matching M.
Proof. by []. Qed.

Print Assumptions x15_edge_setE.
Print Assumptions hamiltonian_cycleGE.
Print Assumptions x26_ballE.
Print Assumptions x15_matching_equiv_matching.
Print Assumptions x18_perfect_matching_equiv_x25_perfect_matching.

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
Proof. by rewrite sg_edge_setE. Qed.

Lemma x15_edge_setE (G : sgraph) : x15_edge_set G = E(G).
Proof. by rewrite sg_edge_setE. Qed.

Lemma x25_edge_setE (G : sgraph) : x25_edge_set G = E(G).
Proof. by rewrite sg_edge_setE. Qed.

Lemma x47_edge_setE (G : sgraph) : x47_edge_set G = E(G).
Proof. by rewrite sg_edge_setE. Qed.

Lemma xe1_edge_setE (G : sgraph) : xe1_edge_set G = E(G).
Proof. by rewrite sg_edge_setE. Qed.

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

(** ** Balls: [X26] and [X111] declare the same [Fixpoint] ****************

    Not convertible (the recursive calls go through two different constants),
    so the bridge needs an induction on the radius. *)

Lemma x26_ballE (G : sgraph) (r : nat) (x : G) : x26_ball r x = x111_ball r x.
Proof. by elim: r => //= r ->. Qed.

(** ** Matchings: [X15]'s edge-set form is [connectivity.matching] ********

    [x15_matching] says "every member is an edge, and every vertex lies in at
    most one member"; the library's [matching] says "every member is an edge,
    and two members sharing a vertex are equal".  The two second clauses are
    [card_le1_eqP] apart. *)

Lemma x15_matching_equiv_matching (G : sgraph) (M : {set {set G}}) :
  x15_matching M <-> matching M.
Proof.
split=> [[MS M1]|[MS M1]]; split.
- by move=> e eM; rewrite -x15_edge_setE; exact: (subsetP MS).
- move=> e1 e2 e1M e2M x xe1 xe2; symmetry.
  move/card_le1_eqP: (M1 x) => H; apply: H; rewrite !inE.
  + by rewrite e1M xe1.
  + by rewrite e2M xe2.
- by apply/subsetP => e eM; rewrite x15_edge_setE; exact: MS.
- move=> v; apply/card_le1_eqP => e1 e2.
  rewrite !inE => /andP[e1M ve1] /andP[e2M ve2].
  exact: (M1 _ _ e2M e1M v ve2 ve1).
Qed.

(** ** Perfect matchings: [X18] and [X25] declare the same notion *********

    [x18_perfect_matching] asks for an [x15_matching] saturating every vertex;
    [x25_perfect_matching] asks for a set of edges saturating every vertex.  The
    "at most one" clause of [x15_matching] is implied by saturation, so the two
    agree. *)

Lemma x18_perfect_matching_equiv_x25_perfect_matching
    (G : sgraph) (M : {set {set G}}) :
  x18_perfect_matching M <-> x25_perfect_matching M.
Proof.
split=> [[[MS _] M1]|[MS M1]]; first by split.
by split=> //; split=> // v; rewrite (M1 v).
Qed.

Print Assumptions x15_edge_setE.
Print Assumptions hamiltonian_cycleGE.
Print Assumptions x26_ballE.
Print Assumptions x15_matching_equiv_matching.
Print Assumptions x18_perfect_matching_equiv_x25_perfect_matching.

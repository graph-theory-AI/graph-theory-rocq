(** * Hom.conjectures.implications_U3 — milestone U3 dependency-graph EDGES

    Machine-checked implication / refutation EDGES between the ten committed
    U3 homomorphism statements (see [U3.v]).  As in the digraph-theory
    [implications.v] / [implications2.v] layer and the chromatic
    [implications_U1.v] / Hamiltonicity [implications_U2.v] files, every edge
    here is meant to be a *relative* theorem: a [Qed]-closed
    [Theorem A_statement -> B_statement] provable WITHOUT resolving (proving or
    refuting) either endpoint — it only transports one conjectural hypothesis to
    another, or specialises one committed conjecture on a restricted subclass.
    Any bridge fact that would need resolving a conjecture or heavy out-of-scope
    machinery is carried as an EXPLICIT hypothesis (never [Admitted], never
    [Axiom]), keeping the file axiom-free.

    ────────────────────────────────────────────────────────────────────────
    AUDIT RESULT: no [verified-literature] edge among the ten U3 nodes.
    ────────────────────────────────────────────────────────────────────────

    Cross-check with the plan §6: the verified-literature table carries NO U3
    entry (its rows are Petersen-colouring / Berge–Fulkerson / CDC / 4-flow, i.e.
    U6 / U10 / D1).  The only U3-touching catalogued edge is the CANDIDATE
    "pentagon ⟹ weak-pentagon" — re-derived below and REJECTED by the Qed gate
    as formulated (see Row 2 → Row 10).

    The ten U3 nodes:

      Row 1  hedetniemis_statement                              (χ(G×H) = min, DISPROVED)
      Row 2  pentagon_statement                                 (∃g cubic girth≥g ⟹ →C5)
      Row 3  chords_of_longest_cycles_statement                 (3-conn ⟹ longest cycle chord)
      Row 4  cores_of_cayley_graphs_statement                   (core of Cayley is Cayley)
      Row 5  chromatic_number_of_frac_3_3_power_…_statement      (χ(G^{3/3}) ≤ 2Δ+1)
      Row 6  cores_of_strongly_regular_graphs_statement         (core = self or K_n)
      Row 7  mapping_planar_graphs_to_odd_cycles_statement      (PLANARITY-GATED, →C_{2k+1})
      Row 8  do_any_three_longest_paths_…_have_statement         (3 longest paths share vertex)
      Row 9  extremal_problem_…_tree_endomorphism_statement      (path min / star max endos)
      Row 10 weak_pentagon_statement                            (cubic Δ-free ⟹ 5-edge-col)

    ── Why no pair carries an honest [verified-literature] relative edge ──

    • Row 2 → Row 10 — the §6 CANDIDATE "pentagon ⟹ weak-pentagon" — FAILS the
      Qed gate as formulated, for TWO independent reasons (both fatal):

        (a) GIRTH GAP.  [pentagon_statement] is [exists g, forall G, regular G 3
            -> girth_geq G g -> homs_to G C5]: it only constrains cubic graphs
            of girth ≥ g for ONE existential threshold g.  [weak_pentagon_statement]
            quantifies over EVERY triangle-free cubic graph — including girth-4
            and girth-5 graphs (e.g. the Petersen graph, girth 5, triangle-free,
            cubic).  A proof of Row 10 hands an ARBITRARY triangle-free cubic G;
            the residual obligation [girth_geq G g] is NOT derivable from
            [triangle_free G] (triangle-free only forbids girth 3), so the
            pentagon hypothesis never fires.  Unprovable.

        (b) CONSTRUCTION GAP.  Even granting a homomorphism [h : G -> C5], the
            conclusion of Row 10 is not [homs_to G C5] but the EXISTENCE of a
            symmetric [col : G -> G -> 'I_5] whose every colour-class complement
            is [bipartite_rel].  Deriving that colouring from [h] is itself a
            non-trivial construction (label edge xy by [h x + h y : 'I_5] — the
            five C5-edges get the five distinct sums {0,1,2,3,4}; deleting one
            colour class leaves edges mapping into C5 minus an edge = a path =
            bipartite).  This construction is true but is NOT what
            [pentagon_statement] asserts, so Row 2 ⊬ Row 10 even on its
            high-girth subclass.

      Hence the candidate stays status=candidate, proved=false.  The honest,
      robustly-true HALF of it is the construction (b) — a relation between the
      PRIMITIVE [homs_to _ C5] and the colouring, NOT a node-to-node edge — and
      per the §6 convention for such structural fragments is left to grounding,
      not asserted here as an [A_implies_B] edge.

    • Row 1 (Hedetniemi) is DISPROVED (Shitov 2019), not a hypothesis other rows
      can use.  Its truth-value is settled to FALSE, so the only catalogued
      "edge" would be the refutation [~ hedetniemis_statement]; per the edge
      policy a refuted record is a SEPARATE negated statement (out of scope for
      this milestone, see U3.v Row 1 header), never a global negation folded
      into an inter-node edge.  No Row-1 implication is scheduled.

    • Rows 3, 8 both concern longest cycles/paths but with DISJOINT hypothesis
      classes and incomparable conclusions (Row 3: 3-connected ⟹ a chord on the
      longest CYCLE; Row 8: connected ⟹ three longest PATHS share a vertex).
      Neither hypothesis specialises to the other (3-connected ⊄ connected for
      the conclusion's purpose, and a chord existence does not transport to a
      common-vertex statement).  Independent.

    • Rows 4, 6 both ask "is the core a nice graph?" but over DISJOINT carriers
      and classes: Row 4 over Cayley graphs on powers of an abelian group
      ([pcayley] on [{ffun 'I_k -> M}]), Row 6 over strongly regular [sgraph]s.
      A Cayley graph on an abelian power need not be strongly regular and a
      strongly regular graph need not be such a Cayley graph, so neither
      core-statement transports to the other.  Independent.

    • Row 5 (a χ upper bound on a fractional power) and Row 9 (extremal
      endomorphism COUNTS on trees) share no hypothesis class with any other
      node; Row 7 is PLANARITY-GATED (its [is_planar] is a discharged section
      [Variable], so the final constant is [(sgraph -> Prop) -> Prop] — it cannot
      be specialised into another node without first fixing the genuine planarity
      predicate, the G2 gate, which is not installed).  None specialises to
      another U3 node.

    Consequently this file commits ZERO conjecture-EDGES: there is no honest
    [verified-literature] node-to-node implication to schedule, and the single
    §6 candidate (Row 2 → Row 10) is rejected by the Qed gate as formulated.  The
    file loads axiom-free, so the milestone's edge layer is present and green.

    This matches the U1 / U2 prior: for diverse slices of the open-problem
    corpus, expect FEW or NO verified edges — these ten homomorphism problems are
    mutually independent; we do not fabricate. *)

From Hom.conjectures Require Import U3.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** No conjecture-edge is scheduled: see the AUDIT RESULT above.  Among the ten
    U3 nodes there is no [verified-literature] relative implication; the §6
    candidate (Row 2 → Row 10, "pentagon ⟹ weak-pentagon") is rejected by the
    Qed gate as formulated — blocked independently by a GIRTH gap (pentagon
    only constrains high-girth cubic graphs, weak-pentagon all triangle-free
    cubic graphs) and a CONSTRUCTION gap (the C5-homomorphism ⟹ 5-edge-colouring
    step is not what pentagon asserts).  So the candidate stays proved=false.
    The disproved Row 1 (Hedetniemi) is recorded as a separate refutation, not
    an inter-node edge.  This file is therefore intentionally theorem-free and
    axiom-free. *)

(** Machine-readable edge records (extracted by meta/build_edge_graph.py): *)
(*@EDGE from=pentagon_statement to=weak_pentagon_statement kind=implies status=refuted-direction cite="Nesetril; girth+construction gaps, not Qed-closed as formulated" note="REFUTED-DIRECTION (metadata wave M, 2026-09-24): unprovable as formulated: girth-threshold gap and homs_to C5 vs 5-colouring-with-bipartite-complements construction gap" *)

(** ** Wave-V vocabulary equivalence (2026-09-24) *************************

    meta/STATEMENT_IMPROVEMENTS.md (section "## homomorphism-theory",
    "### Duplicated vocabulary") records [U3.v:418 bipartite_rel] as the
    relation-level form of [GTBase.base.bipartite]: instantiating the relation
    argument at the adjacency of [G] gives back base's notion.  The two bodies
    are convertible, so the identity holds by [erefl]; it is recorded as a lemma
    so that a future drift of either definition breaks this file rather than
    silently changing the meaning of the two rows that use [bipartite_rel]
    ([mapping_planar_graphs_to_odd_cycles_statement] and the girth row).

    Statement bodies are unchanged: this only makes the duplication formal. *)

Lemma bipartite_relE (G : sgraph) : bipartite_rel (G := G) (--) = bipartite G.
Proof. by []. Qed.

Lemma bipartite_rel_equiv_bipartite (G : sgraph) :
  bipartite_rel (G := G) (--) <-> bipartite G.
Proof. by split=> H; exact: H. Qed.

Print Assumptions bipartite_relE.
Print Assumptions bipartite_rel_equiv_bipartite.

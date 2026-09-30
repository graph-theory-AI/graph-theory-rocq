(** * Topological.conjectures.implications_D3cr — milestone D3cr edges

    Implication / refutation EDGES among the four D3cr crossing-number nodes
    (Zarankiewicz cr(K_{m,n}); Guy cr(K_n); Albertson cr vs. χ; cube cr(Q_d)),
    as Qed-closed RELATIVE theorems where one exists.

    OUTCOME (honest).  The verified-literature edge table of
    OPG_FULL_FORMALIZATION_PLAN.md §6 lists NONE of the crossing-number rows:
    there is no textbook "A ⟹ B" between any pair that closes as a relative
    theorem on the FORMAL statement shapes here.  Consequently this milestone
    schedules ZERO verified edges — there is no real [Theorem A_implies_B. Qed]
    to add, because forcing one would either fail to compile or misstate the
    mathematics.  Per the edge policy a false/unclosing edge must NOT be forced.

    WHY THE STATEMENTS DO NOT LINK FORMALLY.  Each node is of the shape
      [forall ... v, is_crossing_number X v -> <arithmetic in v>],
    i.e. it CONSTRAINS the (relationally pinned, [is_crossing_number_uniq])
    crossing number of a specific carrier X.  An edge A ⟹ B would have to push
    a value/inequality from one carrier to a DIFFERENT carrier (K_{m,n} → K_n,
    arbitrary G → K_t, …).  Every such transfer in the literature goes through a
    genuine combinatorial crossing-number inequality — counting K_{m,n}/K_{n-1}
    copies inside a drawing of K_n, or subgraph monotonicity cr(H) ≤ cr(G).  In
    THIS geometry-free model the full subgraph monotonicity of cr is itself OPEN
    (only the planar base case [wagner_planar_sub] is proved — see crossing.v),
    so the building blocks an edge would need are unavailable.  Hence no edge
    closes; the one literature-motivated direction is a CANDIDATE annotation
    only (proved=false), never scheduled.

    THE LITERATURE-MOTIVATED CANDIDATE (Zarankiewicz ⟹ Guy).  Guy's counting
    argument shows cr(K_{2n}) ≥ cr(K_{n,n}) + 2·cr(K_n) (a drawing of K_{2n}
    splits its 2n vertices into two halves: the bipartite crossings between the
    halves form a K_{n,n} drawing, and each half a K_n drawing), and more
    generally cr(K_n) ≥ (n/(n−4))·cr(K_{n−1}); these tie Guy's conjecture to
    Zarankiewicz's.  There is even an exact arithmetic coincidence of the two
    conjectured FORMULAS: with the Guy product
      G(n) = ⌊n/2⌋⌊(n−1)/2⌋⌊(n−2)/2⌋⌊(n−3)/2⌋ / 4
    and the Zarankiewicz product
      Z(m,n) = ⌊m/2⌋⌊(m−1)/2⌋⌊n/2⌋⌊(n−1)/2⌋,
    one has 4·G(n) = Z(n, n−2) on the nose.  But a coincidence of VALUES is not a
    logical implication of one [is_crossing_number] constraint from the other:
    deriving Guy's value from Zarankiewicz's needs the counting inequality above
    (plus cr subgraph monotonicity, open here), which is exactly the missing
    combinatorial content.  So the edge does NOT close as a relative theorem and
    stays a candidate — the same "looks-like-an-edge but the transfer step is the
    whole conjecture" pattern as the §6 withdrawn edges.

    Albertson (Row 3) and the cube row (Row 4) are MUTUALLY INDEPENDENT of the
    other nodes: Albertson is a lower bound cr(G) ≥ cr(K_t) for arbitrary G with
    χ(G) ≥ t (it yields no VALUE, so it cannot deliver Guy/Zarankiewicz, and
    arbitrary-G crossing facts cannot be delivered TO it); the cube limit 5/32 is
    an asymptotic about a third carrier with no textbook reduction to the others.

    The file imports the four node Definitions verbatim from
    [Topological.conjectures.D3cr] (so the edge endpoints are the EXACT
    [_statement] names) and is axiom-free: no Conjecture/Axiom/Parameter/
    Admitted, and no [Theorem … Qed] asserting an unproven edge. *)

From Topological Require Import foundations.crossing.
From Topological Require Import conjectures.D3cr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Edges

    No verified-literature edge exists among the four nodes (plan §6 lists none
    for the crossing-number rows).  The single literature-motivated direction is
    a CANDIDATE blocked by missing combinatorial content (cr subgraph
    monotonicity is open in this model, and the Guy↔Zarankiewicz counting
    inequality is not derivable from the bare value constraints), recorded as an
    annotation only — there is no Qed theorem for it because it does not logically
    close on the formal statement shapes. *)

(*@EDGE from=the_crossing_number_of_the_complete_bipartite_graph_statement to=the_crossing_number_of_the_complete_graph_statement kind=implies status=refuted-direction cite="Guy, The decline and fall of Zarankiewicz's theorem, 1969; Kleitman 1970 (cr(K_{m,n}) for min<=6); Guy 1972 counting bound cr(K_{2n}) >= cr(K_{n,n}) + 2 cr(K_n)" note="REFUTED-DIRECTION (metadata wave M, 2026-09-24): needs Guy's counting inequality plus crossing-number subgraph monotonicity, open in this geometry-free model. Earlier note: Zarankiewicz (exact cr(K_{m,n})) is conjectured to imply Guy (exact cr(K_n)) via the counting inequality cr(K_{2n}) >= cr(K_{n,n}) + 2 cr(K_n) and cr(K_n) >= (n/(n-4)) cr(K_{n-1}). The conjectured formulas even satisfy 4*Guy(n) = Zarankiewicz(n,n-2) exactly. But transferring a value from carrier K_{m,n} to carrier K_n needs that counting inequality plus cr subgraph monotonicity, which is OPEN in this geometry-free model (only wagner_planar_sub, the planar base case, is proved in crossing.v). The bare is_crossing_number value constraints do not yield it, so the edge does not close as a Qed relative theorem; candidate, never scheduled." *)

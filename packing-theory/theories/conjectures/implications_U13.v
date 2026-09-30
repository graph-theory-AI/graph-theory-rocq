(** * Packing.conjectures.implications_U13 — internal implication spine for U13

    Qed-closed RELATIVE theorems [Theorem A_implies_B : A_statement -> B_statement]
    between the open-problem nodes of milestone U13 (Packing namespace, the two
    DOMINATION rows), each provable WITHOUT resolving either endpoint, plus the
    machine-readable [@EDGE] annotations that [meta/build_edge_graph.py] extracts.

    EDGE POLICY (plan §6): schedule ONLY 'verified-literature' edges; a verified
    edge MUST carry a real [Theorem A_implies_B] closing with [Qed].  'candidate'
    edges are re-derived under the Qed gate before promotion and appear here as the
    annotation ONLY (no theorem).  A genuinely false edge must FAIL to compile — it
    is never forced.

    THE TWO U13 NODES.

      R1  domination_in_cubic_graphs_statement
            carrier sgraph; class = cubic ([regular G 3]) AND 3-connected
            ([k_connected G 3]); claims γ(G) ≤ ⌈|G|/3⌉  ([m <= ceil_div #|G| 3]).
      R2  domination_in_plane_triangulations_statement
            carrier sgraph; class = plane triangulation (historical G2 proxy
            predicate [plane_triangulation : sgraph -> Prop]); claims, for
            sufficiently large G, γ(G) ≤ ⌊|G|/4⌋  ([m <= #|G| %/ 4]).

    FINDING — the two nodes are MUTUALLY INDEPENDENT.

    The hypotheses constrain essentially disjoint graph classes: R1 ranges over
    3-REGULAR graphs (every vertex degree 3), R2 over plane TRIANGULATIONS
    (maximal planar; the only 3-regular plane triangulation is K4).  The two
    conclusions assert different constants on different objects (⌈n/3⌉ vs ⌊n/4⌋),
    so neither is a logical weakening, specialization, or refutation of the other.
    Plan §6's verified-literature edge table lists NO domination edge.  This
    milestone therefore schedules ZERO verified edges — there is no real
    [Theorem A_implies_B. Qed] to add between R1 and R2, and forcing one would
    either fail to compile or misstate the mathematics.

    Both directed candidates are recorded as annotations only (proved=false):

      • R1 ⟹ R2 (cubic ⟹ triangulations): does NOT close.  R2's conclusion is the
        historical G2 proxy target, which (with [plane_triangulation] universally
        quantified and unconstrained — e.g. [fun _ => True]) is REFUTABLE on
        edgeless graphs (γ = n > ⌊n/4⌋).  A true hypothesis paired with a
        refutable conclusion cannot be derived; asserting the edge would FAIL to
        compile.  Recorded refuted-direction, never asserted.

      • R2 ⟹ R1 (triangulations ⟹ cubic): closes only VACUOUSLY, and only as an
        artifact of the historical G2 proxy: because R2 is refutable it is a
        provably-false hypothesis, so [R2 -> R1] is ex-falso true.  But that
        derivation must first REFUTE R2 (i.e. resolve the endpoint), which the
        edge framing forbids, and it reflects the G2 placeholder rather than the
        genuine geometric conjecture.  It is NOT a verified-literature edge and is
        NOT scheduled; recorded candidate, proved=false.

    The file is self-contained via the [Require Import U13] of the node
    definitions and is axiom-free: no Conjecture/Axiom/Parameter/Admitted, and no
    [Theorem … Qed] asserting an unproven edge. *)

From GTBase Require Import base.
From Packing.conjectures Require Import U13.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ================================================================= *)
(** ** Verified-literature edges: NONE.

    Plan §6's verified-literature table carries no U13-internal domination edge,
    and the independence analysis above re-confirms it: there is no ordered pair
    (A,B) of U13 nodes with a Qed-closable [A_statement -> B_statement] that does
    not resolve an endpoint.  No [Theorem _implies_] is scheduled. *)

(** ================================================================= *)
(** ** Candidate / refuted-direction edges (annotations only — NOT scheduled).

    R1 ⟹ R2 — refuted-direction: the historical G2 proxy target was refutable; a
    true cubic hypothesis cannot yield it, so the edge would fail to compile and
    is never asserted (per policy a false edge must NOT be forced).

    R2 ⟹ R1 — candidate: closes only vacuously, as an artifact of the placeholder
    being refutable (ex falso), which requires resolving R2 and is not the genuine
    conjecture; not a verified-literature edge, not scheduled. *)

(*@EDGE from=domination_in_cubic_graphs_statement to=domination_in_plane_triangulations_statement kind=implies status=refuted-direction proved=false cite="OPG_FULL_FORMALIZATION_PLAN.md §6 (no domination edge in the verified table); Reed, Paths/stars/the domination number, Combin. Probab. Comput. 1996 (cubic γ<=⌈n/3⌉); Matheson & Tarjan 1996 (planar triangulation γ<=n/3, conj. n/4)" note="Disjoint classes (3-regular vs maximal planar; only common member K4) and different constants (⌈n/3⌉ vs ⌊n/4⌋). The historical G2 proxy target was refutable on edgeless graphs (γ=n>⌊n/4⌋); a true cubic hypothesis cannot derive it, so the edge would FAIL to compile. Never asserted." *)

(*@EDGE from=domination_in_plane_triangulations_statement to=domination_in_cubic_graphs_statement kind=implies status=refuted-direction cite="OPG_FULL_FORMALIZATION_PLAN.md §6 (no domination edge in the verified table)" note="REFUTED-DIRECTION (metadata wave M, 2026-09-24): disjoint carriers (only K4 in common) and different constants; the historical route closed only vacuously. Earlier note: Independent nodes over disjoint classes; would close only VACUOUSLY because the historical G2 proxy target was refutable (ex-falso), which first resolves R2 — forbidden by the 'without resolving either endpoint' framing and an artifact of that proxy, not the genuine conjecture. Not verified-literature; not scheduled." *)

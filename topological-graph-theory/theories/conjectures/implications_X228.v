(** * Topological.conjectures.implications_X228 — wave X228 dependency-graph EDGES

    The two X228 nodes are the random-embedding rows of arXiv:2202.07746
    (Conjecture 4, [E[F] <= n/3 + 1]) and arXiv:2103.05036 (Conjecture 1,
    [E[F] = O(n)]).  The corpus records one confirmed relation between them,
    gc:e125 (arxiv:2202.07746#00 implies arxiv:2103.05036#00): the sharp bound
    [n/3 + 1] is in particular linear in [n].

    STATE OF THE EDGE (re-audited 2026-09-24).  The two bodies are NOT guarded the
    same way:

      - [random_embedding_expected_faces_third_statement] quantifies over
        CONNECTED graphs only ([connected [set: G]], guard added 2026-09-23: the
        additive "+1" is per connected component, and without the guard the body
        is refuted by four disjoint edges);
      - [random_embedding_expected_faces_linear_statement] quantifies over ALL
        finite simple graphs (its own Notes argue that the unguarded form is
        equivalent to the source, because rotation systems multiply and face
        counts add over connected components — a fact that is NOT formalised).

    So the edge is not a direct weakening: the source says nothing about a
    disconnected [G], and the target must bound such a [G] too.  What IS
    machine-checked below is the whole connected half of the edge
    ([x228_third_implies_linear_connected]): the source's bound gives the target's
    inequality with the explicit constant [c = 4] for every connected graph, empty
    graph included.  The remaining gap is exactly the reduction of a disconnected
    graph to its components, which needs the two missing foundation lemmas named
    in the EDGE note below.  The edge therefore stays a CANDIDATE.

    The file is axiom-free: no Axiom/Parameter/Admitted, and no [Theorem ... Qed]
    asserting the unproven edge. *)

From GTBase Require Import base.
From mathcomp Require Import fingroup perm.
From Topological.conjectures Require Import X228 grounding_X228.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The connected half of gc:e125, with the explicit constant [c = 4]: on a
    connected graph the source's cleared bound [3 * total <= (n + 3) * nrot]
    yields the target's [total <= 4 * n * nrot].  (For [n = 0] the total face
    count is [0] by [x228_total_faces0]; for [n >= 1], [n + 3 <= 4 * n].) *)
Lemma x228_third_implies_linear_connected :
  random_embedding_expected_faces_third_statement ->
  forall G : sgraph, connected [set: G] ->
    x228_total_faces G <= 4 * #|G| * x228_nrot G.
Proof.
move=> H G cG; have [n0|n0] := posnP #|G|.
  by rewrite (x228_total_faces0 n0).
have step : x228_total_faces G <= 3 * x228_total_faces G by apply: leq_pmull.
apply: (leq_trans step).
apply: (leq_trans (H G cG)); apply: leq_mul => //.
rewrite mulSn leq_add2l; apply: leq_pmulr; exact: n0.
Qed.

(*@EDGE from=random_embedding_expected_faces_third_statement
        to=random_embedding_expected_faces_linear_statement
        kind=implies status=candidate
        cite="gc:e125"
        note="BLOCKED: the source row is guarded by connected [set: G] (guard added 2026-09-23) while the target row quantifies over ALL graphs, so the corpus argument needs the component decomposition of the finite average, which is not formalised. Exact missing lemmas (theories/foundations/, F12): (1) x228_nrot (sjoin A B) = x228_nrot A * x228_nrot B, and (2) x228_total_faces (sjoin A B) = x228_total_faces A * x228_nrot B + x228_nrot A * x228_total_faces B -- i.e. the rotation systems of a disjoint union are pairs of rotation systems (surface_dart (sjoin A B) ~ surface_dart A + surface_dart B, and the face permutation splits), plus the induction that every sgraph is the join of a connected component and the rest (a diso G ~ sjoin (induced C) (induced (~: C))). Given (1)+(2), c = 4 works: the connected case is proved here as x228_third_implies_linear_connected, and summing n_i/3 + 1 <= (4/3) n_i over the components keeps the constant. No crude route exists: a single rotation system can have up to 2*#|E| faces, which is not O(n)." *)

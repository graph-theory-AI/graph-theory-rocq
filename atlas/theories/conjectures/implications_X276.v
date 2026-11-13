(** * Atlas.conjectures.implications_X276 -- a cross-package dependency-graph EDGE with an X276 endpoint.

    Same role as [implications_X287.v]: a machine-checked implication between statements of two packages
    (extremal-graph-theory and chromatic-theory, neither of which imports the other), hosted in the atlas.  The
    edge is a RELATIVE theorem: a [Qed]-closed [Theorem A -> B] proved WITHOUT resolving either endpoint.
    Axiom-free: no [Axiom] / [Parameter] / [Admitted] / [Conjecture].

    The edge below is a Rocq-only edge (no corpus relation), named a candidate in X276's Notes: (k,r)-graphs on
    every large order (X276, studies:std_erd_s_problem_on_k_r_graphs: for every k >= 4 and every r, every large
    enough n carries a k-vertex-critical graph on n vertices in which no set of at most r edges is critical)
    implies (k,r)-graphs exist (XE1, erdos:944: for every k >= 4 and r >= 1, some graph with chromatic number k,
    every vertex critical, and every critical edge set larger than r).  XE1's helpers are X276's inlined
    conditions ([xe1_delete_edges] is [del_edge_set], [xe1_edge_set] is [E(G)]): take n := n0; an edge set F
    with chi(G - F) < k and #|F| <= r would contradict X276's k <= chi(G - F), so r < #|F|.  Both rows are open. *)

From GTBase Require Import base.
From Extremal.conjectures Require Import X276.
From Chromatic.conjectures Require Import XE1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** (k,r)-graphs on every large order (X276) ==> (k,r)-graphs exist (erdos:944) *)

(*@EDGE from=erdos_kr_graphs_unbounded_statement to=erdos_944_statement kind=implies status=verified proof=erdos_kr_graphs_unbounded_implies_erdos_944 note="Rocq-only edge (no corpus relation), routed by Lancelot's (739), (740) and named a candidate in X276's Notes: (k,r)-graphs on every large order (X276, studies:std_erd_s_problem_on_k_r_graphs) imply that (k,r)-graphs exist (XE1, erdos:944). XE1's helpers are X276's inlined conditions (xe1_delete_edges is del_edge_set, xe1_edge_set is E(G)); take n := n0 and X276's graph G: chi(G) = k and vertex criticality carry over, and an edge set F with chi(G - F) < k and #|F| <= r would contradict k <= chi(G - F), so r < #|F|. Both rows are open." *)
Theorem erdos_kr_graphs_unbounded_implies_erdos_944 :
  erdos_kr_graphs_unbounded_statement -> erdos_944_statement.
Proof.
move=> h k r k4 _.
have [n0 hn0] := h k k4 r.
have [G [_ [chiG vcrit eF]]] := hn0 n0 (leqnn n0).
exists G; split=> //; split=> // F [FE chiF].
rewrite ltnNge; apply/negP => Fr.
by have := eF F FE Fr; rewrite leqNgt chiF.
Qed.

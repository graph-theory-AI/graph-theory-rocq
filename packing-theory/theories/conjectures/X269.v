(** * Packing.conjectures.X269 -- v2 rows: independence and upper irredundance on direct products of complete
    multipartite graphs, colour-balanced perfect matchings, edge decompositions of hypercubes *)

From GTBase Require Import base common hypercubes edge_copies.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X269 vocabulary *****************************************************)

(** H is complete multipartite (Alon and Defant, arXiv:1904.02595v1, source.tex l.69-73 and l.127): for some map p
    from the vertices to k part labels, two vertices are adjacent iff their parts differ.  The parts may have any
    sizes; a label may be unused (an empty part), and a single part gives an edgeless graph. *)
Definition x269_multipartite_complete (H : sgraph) : Prop :=
  exists (k : nat) (p : H -> 'I_k), forall x y : H, x -- y = (p x != p y).

(** The direct product of H 0, ..., H n (source.tex l.69: adjacent iff adjacent in every coordinate), nested as
    H 0 x (H 1 x (... x H n)) over GTBase's binary [tensor_product]; for n = 0 it is H 0 itself. *)
Fixpoint x269_tensor_prod (n : nat) : ('I_n.+1 -> sgraph) -> sgraph :=
  match n with
  | 0 => fun H => H ord0
  | n'.+1 => fun H => tensor_product (H ord0) (@x269_tensor_prod n' (fun i => H (lift ord0 i)))
  end.

(** ** X269 statements *****************************************************)

(** Corpus row: arxiv:1904.02595#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1904.02595__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1904.02595__00.json
    English statement: (Alon and Defant, Isoperimetry, Stability, and Irredundance in Direct Products,
      arXiv:1904.02595, Conjecture 1.2)
      If H_1, ..., H_n are complete multipartite graphs and G = prod_(i=1)^n H_i, then alpha(G) = IR(G).
    Definitions: [x269_multipartite_complete H] - adjacency is "in different parts" for some part map (this
      file); [x269_tensor_prod H] - the direct product of H 0, ..., H n (this file, over GTBase tensor_product);
      [α(A)] - the independence number of the subgraph induced by A (upstream coq-graph-theory); [IR G] - the
      largest size of an irredundant set of G, a set S in which every vertex v has a vertex of its closed
      neighbourhood outside the closed neighbourhood of S minus v (upstream coq-graph-theory dom.v).
    Notes: encoded as stated; pinned status open.  The conjecture is source.tex l.137-139 (arXiv:1904.02595v1,
      4 April 2019, the last version before the pin).  It removes the balance condition from Burcroff's
      Conjecture 1.1 (l.77-79, factors K[u, t] with t parts of size u), which the paper proves in all but 37 cases
      (Theorem 1.2); Theorem 1.3 gives IR(G) <= alpha(G) + 2^n for every product of n complete multipartite
      graphs.  The direct product (l.69) has adjacency in every coordinate; the nested binary product is
      isomorphic to it, and alpha and IR are isomorphism invariants.  IR (l.73): S is irredundant iff
      N[S \ {v}] <> N[S] for every v in S; as N[S] = N[S \ {v}] u N[v], that is upstream [irredundant].  The
      factors are arbitrary complete multipartite graphs (l.138), and one factor is within the paper's scope: its
      Theorem 1.4 (l.103) and the induction of Corollary 1.1 (l.263) start at n = 1; 'I_n.+1 indexes n + 1 >= 1
      factors.  A one-part factor, which [x269_multipartite_complete] allows, is edgeless and makes the product
      edgeless, where alpha = IR = the number of vertices (the whole vertex set is independent and irredundant);
      so these instances are true and the statement is the paper's either way.  Unused labels (empty parts)
      describe the same graphs, and a factor without vertices gives the empty product, where alpha = IR = 0.
      [x269_multipartite_complete G] holds iff Extremal XE1's [xe1_complete_multipartite_with_sizes G k sizes]
      holds for some k and sizes (the parts are the preimages of p; empty parts are allowed in both); Packing
      does not import Extremal.  GTBase's balanced K_k(m) (complete_multipartite_graphs.v) is the narrower class
      of Conjecture 1.1. *)
Definition alpha_ir_multipartite_products_statement : Prop :=
  forall (n : nat) (H : 'I_n.+1 -> sgraph), (forall i, x269_multipartite_complete (H i)) ->
    α([set: x269_tensor_prod H]) = IR (x269_tensor_prod H).

(** Corpus row: arxiv:2604.09449#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2604.09449__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2604.09449__01.json
    English statement: (Hogan, Scott and Tsarev, Colour-balanced subgraphs, arXiv:2604.09449, Conjecture 6.2)
      There exists some absolute constant C such that for all positive integers k and t, every colour-balanced
      k-edge-colouring of K_(2kt) admits a perfect matching M satisfying f_c(M) < C.
    Definitions: ['K_n] - the complete graph on 'I_n and [E(G)] - its edge set (upstream coq-graph-theory);
      [perfect_matching M] - a matching of G covering every vertex (GTBase common.v); a k-edge-colouring is a map
      c from the 2-sets to 'I_k, read on the edges only; it is colour-balanced if all colours have the same
      number of edges; f_c(M) is the sum over the colours i of |#(edges of M of colour i) - t|.
    Notes: encoded as stated; pinned status open.  The conjecture is main.tex l.747-749 (arXiv:2604.09449v2,
      11 July 2026, the last version before the pin), colour-balanced and f_c are l.79-83.  C is one absolute
      constant, chosen before k and t.  f_c is an integer, so f_c(M) < C for a real C iff f_c(M) is below the
      ceiling of C, and C ranges over nat.  k = 1 is included ("all positive integers"): one colour, every perfect
      matching of K_(2t) has t edges, and f_c = 0.  Known at the pin: Theorem 1.2 gives a perfect matching with
      f_c(M) = O(k^2), not uniform in k, and Theorem 5.3 (l.695-697) gives, for every k >= 3 and t >= 1, a
      colour-balanced colouring of K_(2kt) without a colour-balanced perfect matching.  The absolute
      difference |a - t| of naturals is written (a - t) + (t - a): both subtractions truncate and one of them is
      zero, so the sum is |a - t|. *)
Definition colour_balanced_perfect_matching_statement : Prop :=
  exists C : nat, forall k t : nat, 0 < k -> 0 < t ->
    forall c : {set 'K_(2 * k * t)} -> 'I_k,
      (forall i j : 'I_k,
         #|[set e in E('K_(2 * k * t)) | c e == i]| = #|[set e in E('K_(2 * k * t)) | c e == j]|) ->
      exists M : {set {set 'K_(2 * k * t)}}, perfect_matching M /\
        \sum_(i < k) (let a := #|[set e in M | c e == i]| in (a - t) + (t - a)) < C.

(** Corpus row: studies:std_gruslys_leader_tan_conjecture_hypercube_edge_dec
    Site: none
    Review: none
    English statement: (Gruslys, Leader and Tan, studies slice of the corpus)
      For k >= 1, let H be a non-empty subgraph of Q_k.  Then there exists a positive integer n such that the
      edges of Q_n can be covered by edge-disjoint copies of H (the copies of H are not required to be induced).
    Definitions: [tuple_hypercube n] - Q_n on the boolean n-tuples, adjacent iff they differ in exactly one
      coordinate (GTBase hypercubes.v); [has_subgraph G H] - an injective adjacency-preserving map from H into G
      (GTBase common.v); [edge_decomposition_exact H D] - every member of the list D is the edge set of an
      embedded (not necessarily induced) copy of H, and every edge of the host lies in exactly one member, every
      non-edge in none (GTBase edge_copies.v).
    Notes: encoded as stated; pinned status open, but FALSE at the pin.  The conjecture is Gruslys's Conjecture 11
      (arXiv:1611.02021v1, hypercube-tiling.tex l.546-550, "for some k", attributed there to Gruslys, Leader and
      Tan) and Conjecture 1.6 of Bonamy, Morrison and Scott (arXiv:1710.07255v3, 14 June 2020, torus-final.tex
      l.127-129, k >= 1), whose Theorem 1.7 (l.133-136) refutes it: for every k >= 5 some H with
      Q_(k-1) <= H <= Q_k admits no such decomposition of any Q_n.  "Non-empty" is not defined in either source;
      it is read as "has an edge", the edge-cover reading: an edgeless H covers no edge of Q_n, n >= 1, and
      Gruslys's motivation (hypercube-tiling.tex l.537-543), the divisibility e(H) | 2^(n-1) n met whenever e(H)
      divides n, presupposes e(H) >= 1.  The status does not depend on it: Theorem 1.7's H has edges, and under
      the vertex reading an edgeless H already fails.  "Covered by edge-disjoint copies" is an edge partition: each
      edge of Q_n in exactly one copy.  The positive integer n is the guard 1 <= n, which is load-bearing: Q_0 has
      no edge, so the empty list would decompose it for every H.  The status correction is a separate corpus item. *)
Definition hypercube_edge_decomposition_statement : Prop :=
  forall (k : nat) (H : sgraph), 1 <= k -> has_subgraph (tuple_hypercube k) H -> 0 < #|E(H)| ->
    exists n : nat, 1 <= n /\ exists D : seq {set {set tuple_hypercube n}}, edge_decomposition_exact H D.

(** * Extremal.conjectures.X287 -- v2 row: the Bajnok-Brinkmann conjecture (exactly six 2-connected triangle-free
      subcubic graphs with independence number below 3n/8) *)

From GTBase Require Import base finite_graph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x287 vocabulary ************************************************* *)

(** [x287_bb_tables]: the six graphs F_11, F_14^(1), F_14^(2), F_19^(1), F_19^(2), F_22 of Cames van Batenburg,
    Goedgebeur and Joret (arXiv:1911.12471v2, Figure 1, Revision_IndependenceRatio8over3.tex l.184-191), each as its
    order and edge list.  The lists are the edges of the figure source files the paper includes (figures/F_11,
    F_14_1-new, F_14_2-new, F_19_1, F_19_2 and F_22, in .graphml), verbatim and in file order, node nK being vertex
    K. *)
Definition x287_bb_tables : seq (nat * seq (nat * nat)) :=
  [:: (* F_11, figures/F_11.graphml *)
      (11, [:: (0, 1); (2, 3); (2, 1); (0, 3); (4, 5); (6, 7); (7, 0); (6, 2); (3, 4); (5, 1); (6, 8); (8, 4); (7, 9);
         (9, 5); (9, 10); (8, 10)]);
      (* F_14^(1), figures/F_14_1-new.graphml *)
      (14, [:: (0, 1); (2, 1); (0, 3); (4, 5); (6, 7); (7, 0); (6, 2); (3, 4); (5, 1); (10, 11); (11, 8); (10, 9);
         (9, 12); (12, 8); (2, 10); (11, 3); (12, 13); (6, 13); (7, 8); (4, 13); (5, 9)]);
      (* F_14^(2), figures/F_14_2-new.graphml *)
      (14, [:: (0, 1); (2, 1); (0, 3); (4, 5); (6, 7); (7, 0); (6, 2); (3, 4); (5, 1); (10, 11); (11, 8); (10, 9);
         (9, 12); (12, 8); (2, 10); (11, 3); (12, 13); (6, 13); (7, 8); (5, 13); (4, 9)]);
      (* F_19^(1), figures/F_19_1.graphml *)
      (19, [:: (4, 5); (6, 7); (7, 0); (6, 2); (3, 4); (5, 1); (8, 11); (8, 13); (10, 11); (0, 14); (14, 2); (15, 1);
         (15, 3); (15, 13); (11, 3); (1, 12); (0, 9); (2, 10); (14, 8); (9, 13); (9, 12); (10, 12); (17, 18);
         (16, 18); (6, 17); (7, 16); (16, 5); (17, 4)]);
      (* F_19^(2), figures/F_19_2.graphml *)
      (19, [:: (4, 5); (6, 7); (7, 0); (6, 2); (3, 4); (5, 1); (8, 11); (8, 13); (10, 11); (0, 14); (14, 2); (15, 1);
         (15, 3); (15, 13); (11, 3); (1, 12); (0, 9); (2, 10); (14, 8); (9, 13); (9, 12); (10, 12); (17, 18);
         (16, 18); (6, 17); (7, 16); (17, 5); (16, 4)]);
      (* F_22, figures/F_22.graphml *)
      (22, [:: (4, 5); (6, 7); (7, 0); (6, 2); (3, 4); (5, 1); (10, 11); (11, 8); (10, 9); (9, 12); (12, 8); (12, 13);
         (14, 17); (14, 19); (16, 17); (0, 20); (20, 2); (21, 1); (21, 3); (21, 19); (17, 3); (1, 18); (0, 15);
         (2, 16); (20, 14); (15, 19); (15, 18); (16, 10); (6, 9); (7, 13); (18, 11); (4, 13); (5, 8)])].

(** [x287_bb_graph i]: the i-th graph of [x287_bb_tables] on the vertices 'I_n, with an edge between the ends of each
    listed pair (fg_mk_sgraph symmetrises the relation and drops loops; the tables have none). *)
Definition x287_bb_graph (i : 'I_6) : sgraph :=
  let: (n, es) := nth (0, [::]) x287_bb_tables i in
  fg_mk_sgraph (fun x y : 'I_n => (val x, val y) \in es).

(** ** X287 statement ********************************************************* *)

(** Corpus row: studies:std_bajnok_brinkmann_conjecture_triangle_free_subcub
    Site: none
    Review: none
    English statement: (Bajnok and Brinkmann's conjecture; studies slice of the corpus, record arXiv:1911.12471)
      There are exactly six 2-connected triangle-free subcubic n-vertex graphs G with alpha(G) < 3/8 n, namely F_11,
      F_14^(1), F_14^(2), F_19^(1), F_19^(2), F_22.
    Definitions: [x287_bb_tables], [x287_bb_graph i] - the six graphs of the source's Figure 1 (this file);
      [k_connected G 2] - G has more than two vertices and stays connected after deleting any one vertex;
      [triangle_free G] - no three pairwise adjacent vertices; [subcubic G] - every vertex has at most three
      neighbours (GTBase base.v); [G ≃ H] - an isomorphism of graphs (coq-graph-theory diso, stated with inhabited as
      in U1, X112 and X142); α([set: G]) - the independence number of G (coq-graph-theory).
    Notes: encoded as stated, "exactly six, namely these" as three clauses: every 2-connected triangle-free subcubic G
      with alpha(G) < 3n/8 is isomorphic to one of the six; each of the six is such a graph; and no two of them are
      isomorphic.  alpha(G) < 3n/8 is 8 alpha(G) < 3n.  Source: Cames van Batenburg, Goedgebeur and Joret, "Large
      independent sets in triangle-free cubic graphs: beyond planarity", arXiv:1911.12471v2 (8 July 2020, the last
      version before the pin), Revision_IndependenceRatio8over3.tex l.204-210 (Bajnok and Brinkmann's computer search,
      which found these six, and their conjecture as quoted), l.161 (subcubic = maximum degree at most 3).  The graphs
      are given by drawings only; the tables are the edge lists of the figure files the paper includes (l.184-189).
      2-connectivity requires more than two vertices; no graph of order at most 2 has alpha < 3n/8 anyway.
      Literature status: TRUE at the pin.  Corollary 8 (l.249-253) gives alpha(G) >= 3n/8 for every 2-connected
      triangle-free subcubic G that is not one of the six, so no other graph qualifies; each of the six qualifies
      (l.205; by computation on the tables: orders 11, 14, 14, 19, 19, 22, independence numbers 4, 5, 5, 7, 7, 8),
      and the same-order pairs are not isomorphic (seven and eight 5-cycles in F_14^(1) and F_14^(2); eight and seven
      7-cycles in F_19^(1) and F_19^(2)).  Theorem statements read, proofs not verified.  The pinned status open is a
      literature item after integration (lit23, with Locke's conjecture of X285, by the same Corollary 8). *)
Definition bajnok_brinkmann_six_exceptional_graphs_statement : Prop :=
  [/\ forall G : sgraph, k_connected G 2 -> triangle_free G -> subcubic G -> 8 * α([set: G]) < 3 * #|G| ->
        exists i : 'I_6, inhabited (G ≃ x287_bb_graph i),
      forall i : 'I_6,
        [/\ k_connected (x287_bb_graph i) 2, triangle_free (x287_bb_graph i), subcubic (x287_bb_graph i) &
            8 * α([set: x287_bb_graph i]) < 3 * #|x287_bb_graph i|] &
      forall i j : 'I_6, i != j -> ~ inhabited (x287_bb_graph i ≃ x287_bb_graph j)].

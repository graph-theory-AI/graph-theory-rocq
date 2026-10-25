(** * Extremal.conjectures.X230 -- the X230 pilot wave: four extremal rows (2026-10-25)

    The first statement wave under the prospective contract of meta/faithfulness_policy.json
    (hard lint, classified local helpers, grounding certificates, an independent verifier).
    Rows: arxiv:1905.05312#00 (books versus triangles), arxiv:2108.00987#00 and
    arxiv:2108.00991#00 (threshold Ramsey multiplicity of odd cycles and of paths),
    arxiv:2311.01887#00 (Ramsey numbers of arbitrary growth).  Shared vocabulary is reused:
    [clique_count_size G 3] counts triangles (GTBase.clique_counts), [cycle_graph k] and
    [ordinal_path k] are C_k and the path on k vertices (GTBase), [compl G] is the
    complement, [has_subgraph G H] is "G contains H" (GTBase.common), [diso G H] is an
    isomorphism (coq-graph-theory). *)

From GTBase Require Export base.
From GTBase Require Import common clique_counts path_graphs.
From mathcomp Require Import all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x230 vocabulary ************************************************* *)

(** Book number at most [b]: every edge lies in at most [b] triangles, i.e. its two ends
    have at most [b] common neighbours (the book number is the largest such count). *)
Definition x230_book_at_most (G : sgraph) (b : nat) : Prop :=
  forall x y : G, x -- y -> #|[set z | x -- z & y -- z]| <= b.

(** The 3-prism on the labels 0..5: triangles {0,1,2} and {3,4,5} and the matching i -- i+3. *)
Definition x230_prism_rel (i j : nat) : bool :=
  (i != j) && (((i < 3) == (j < 3)) || (i %% 3 == j %% 3)).

(** [G] is S_{b,n} up to isomorphism: a labelling [p] of the vertices by the prism vertices
    0..5 under which adjacency is prism adjacency of the labels (each part independent, two
    prism-adjacent parts completely joined), with parts of sizes [b, b, s, b, b, t] for the
    labels 0..5, where [s] and [t] are the floor and ceiling halves of [n - 4b]: the two halves
    sit on the matched pair 2 -- 5. The subtraction is truncated; the row guards it by [4b < n],
    under which the sizes add up to [n]. *)
Definition x230_prism_blowup (b n : nat) (G : sgraph) : Prop :=
  exists p : G -> 'I_6,
    (forall x y : G, (x -- y) = x230_prism_rel (p x) (p y)) /\
    (forall i : 'I_6, #|[set x | p x == i]| =
       nth 0 [:: b; b; (n - 4 * b) %/ 2; b; b; (n - 4 * b) - (n - 4 * b) %/ 2] i).

(** The injective homomorphisms (embeddings) of [H] into [G], and the automorphisms of [H].
    Two embeddings have the same image (vertices and edges) iff they differ by an automorphism
    of [H], and automorphisms act freely on embeddings, so the copies of [H] in [G] (subgraphs
    isomorphic to [H], not necessarily induced) number #embeddings / #automorphisms, exactly. *)
Definition x230_embeddings (H G : sgraph) : {set {ffun H -> G}} :=
  [set f : {ffun H -> G} | injectiveb f & [forall x : H, [forall y : H, (x -- y) ==> (f x -- f y)]]].

Definition x230_automorphisms (H : sgraph) : {set {ffun H -> H}} :=
  [set f in x230_embeddings H H | [forall x : H, [forall y : H, (f x -- f y) ==> (x -- y)]]].

Definition x230_copies (H G : sgraph) : nat :=
  #|x230_embeddings H G| %/ #|x230_automorphisms H|.

(** A 2-colouring of the edges of K_n is a graph [G] on [n] vertices (one colour) and its
    complement (the other); its monochromatic copies of [H] are the copies in either. *)
Definition x230_mono_copies (H G : sgraph) : nat := x230_copies H G + x230_copies H (compl G).

(** [R] arrows [H]: every 2-colouring of K_R has a monochromatic copy of [H]. *)
Definition x230_arrows (R : nat) (H : sgraph) : Prop :=
  forall G : sgraph, #|G| = R -> has_subgraph G H \/ has_subgraph (compl G) H.

(** [R = r(H)], the (two-colour) Ramsey number of [H]. *)
Definition x230_ramsey_number (H : sgraph) (R : nat) : Prop :=
  x230_arrows R H /\ forall R' : nat, x230_arrows R' H -> R <= R'.

(** [m = m(H)], the threshold Ramsey multiplicity: the least number of monochromatic
    copies of [H] in a 2-colouring of K_{r(H)}. *)
Definition x230_threshold_multiplicity (H : sgraph) (m : nat) : Prop :=
  exists R : nat, [/\ x230_ramsey_number H R,
    forall G : sgraph, #|G| = R -> m <= x230_mono_copies H G
  & exists2 G : sgraph, #|G| = R & x230_mono_copies H G = m].

(** ** X230 statements ********************************************************* *)

(** Corpus row: arxiv:1905.05312#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1905.05312__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1905.05312__00.json
    English statement: (arXiv:1905.05312, "Books versus triangles at the extremal density",
      Conjecture 1.1)
      If n/6 <= b < n/4, then every graph on n vertices with at least floor(n^2/4) edges and
      book number at most b which is not the balanced complete bipartite graph has at least
      b^2 (n - 4b) triangles, with equality if and only if the graph is S_{b,n}.
    Definitions: [x230_book_at_most G b] - every edge has at most b common neighbours, i.e.
      book number at most b (this file); ['K_m,l] - the complete bipartite graph with parts of
      sizes m and l (coq-graph-theory), here with parts floor(n/2) and ceil(n/2) = n - floor(n/2);
      [x230_prism_blowup b n G] - G is S_{b,n} up to isomorphism, the blow-up of the 3-prism with
      parts b, b, b, b on four prism vertices and the floor and ceiling halves of n - 4b on the
      remaining matched pair (this file); [clique_count_size G 3] - the number of triangles
      (GTBase.clique_counts); [diso G H] - an isomorphism (coq-graph-theory); [E(G)] - the edge
      set (GTBase.base).
    Notes: n/6 <= b < n/4 is cleared to n <= 6b and 4b < n; the truncated subtraction n - 4b is
      guarded by 4b < n, and n - floor(n/2) never truncates. "Not the balanced complete
      bipartite graph" and "is S_{b,n}" are up to isomorphism. The source gives the part sizes
      of S_{b,n}, not their placement on the prism. With the two halves s, t of n - 4b on a
      matched pair the blow-up has floor(n^2/4) edges, book number b (as n <= 6b) and exactly
      b^2 (n - 4b) triangles. In one triangle they give b (b - s) (b - t) more triangles; on
      neither a triangle nor a matched pair, 3bn - 9b^2 edges, fewer than floor(n^2/4) unless
      n = 6b. Only the matched pair attains the conjectured count, so it is the placement read. *)
Definition books_versus_triangles_extremal_density_statement : Prop :=
  forall (n b : nat) (G : sgraph),
    n <= 6 * b -> 4 * b < n -> #|G| = n ->
    n ^ 2 %/ 4 <= #|E(G)| -> x230_book_at_most G b ->
    ~ inhabited (diso G 'K_(n %/ 2),(n - n %/ 2)) ->
    b ^ 2 * (n - 4 * b) <= clique_count_size G 3 /\
    (clique_count_size G 3 = b ^ 2 * (n - 4 * b) <-> x230_prism_blowup b n G).

(** Corpus row: arxiv:2108.00987#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2108.00987__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2108.00987__00.json
    English statement: (arXiv:2108.00987, "Threshold Ramsey multiplicity for odd cycles",
      Conjecture 4)
      For any sufficiently large odd integer k, m(C_k) = (k-1)!/2, where the threshold Ramsey
      multiplicity m(H) is the minimum number of monochromatic copies of H in a 2-colouring of
      the edges of the complete graph on r(H) vertices, r(H) being the Ramsey number of H.
    Definitions: [x230_threshold_multiplicity H m] - m = m(H) (this file); [x230_ramsey_number H R]
      - R = r(H), the least R with every 2-colouring of K_R containing a monochromatic copy of H
      (this file); [x230_mono_copies H G] - the copies of H in G plus those in its complement, G
      being one colour class of a 2-colouring of K_{|G|} (this file); [x230_copies H G] - the
      number of copies of H in G, #embeddings / #automorphisms of H (this file);
      [cycle_graph k] - C_k (GTBase.base).
    Notes: m(C_k) = (k-1)!/2 is cleared to 2 m = (k-1)!. Copies are subgraphs isomorphic to
      the pattern, not necessarily induced; their number is the number of embeddings divided
      by the number of automorphisms. "Sufficiently large" is an existential threshold K. *)
Definition threshold_ramsey_multiplicity_odd_cycles_statement : Prop :=
  exists K : nat, forall k : nat, K <= k -> odd k ->
    exists2 m : nat, x230_threshold_multiplicity (cycle_graph k) m & 2 * m = (k.-1)`!.

(** Corpus row: arxiv:2108.00991#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2108.00991__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2108.00991__00.json
    English statement: (arXiv:2108.00991, "Threshold Ramsey multiplicity for paths and even
      cycles", Conjecture 3)
      For sufficiently large k, if k is even then m(P_k) = k!/2, and if k is odd then
      m(P_k) = ((k-1)/4) (k-1)!, where P_k is the path on k vertices and m(H) is the threshold
      Ramsey multiplicity (the minimum number of monochromatic copies of H in a 2-colouring of
      the edges of K_{r(H)}).
    Definitions: [x230_threshold_multiplicity H m] - m = m(H) (this file); [ordinal_path k] - the
      path on k vertices (GTBase.path_graphs); the rest as for arxiv:2108.00987#00 (this file).
    Notes: the values are cleared to 2 m = k! (k even) and 4 m = (k-1) (k-1)! (k odd). P_k has
      k vertices: K_k contains k!/2 copies of it, the even-k value. *)
Definition threshold_ramsey_multiplicity_paths_statement : Prop :=
  exists K : nat, forall k : nat, K <= k ->
    exists2 m : nat, x230_threshold_multiplicity (ordinal_path k) m &
      (if odd k then 4 * m = k.-1 * (k.-1)`! else 2 * m = k`!).

(** Corpus row: arxiv:2311.01887#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2311.01887__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2311.01887__00.json
    English statement: (arXiv:2311.01887, "Graphs with arbitrary Ramsey number and
      connectivity", Conjecture 10)
      For all functions f from the naturals to the naturals with n <= f(n) <= r(K_n) and for
      all eps > 0, there is a sequence of graphs (G_n) with |V(G_n)| = n and
      (1 - eps) f(n) <= r(G_n) <= (1 + eps) f(n) for all sufficiently large n.
    Definitions: [x230_ramsey_number H R] - R = r(H) (this file); ['K_n] - the complete graph
      (GTBase.base).
    Notes: the subtraction 1 - eps is in rat, so nothing is truncated. "n <= f(n) <= r(K_n)" is
      read through the Ramsey number of K_n, which exists for every n. The conclusion asserts
      that r(G_n) exists and lies in the window. The source text asks for arbitrary graphs (the
      surrounding context discusses connected ones; the conjecture's text does not). *)
Definition ramsey_numbers_of_arbitrary_growth_statement : Prop :=
  forall f : nat -> nat,
    (forall n R : nat, x230_ramsey_number 'K_n R -> n <= f n <= R) ->
    forall eps : rat, (0 < eps)%R ->
      exists2 Gs : nat -> sgraph, (forall n : nat, #|Gs n| = n) &
        exists N : nat, forall n : nat, N <= n ->
          exists2 R : nat, x230_ramsey_number (Gs n) R &
            ((1 - eps) * (f n)%:R <= R%:R)%R /\ (R%:R <= (1 + eps) * (f n)%:R)%R.

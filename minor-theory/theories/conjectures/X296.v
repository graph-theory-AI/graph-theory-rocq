(** * Minor.conjectures.X296 -- v2 row: the Lescure-Meyniel conjecture, chromatic number k forces a weak immersion
      of K_k *)

From GTBase Require Import base.
From Minor.conjectures Require Import U7.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X296 statement ******************************************************)

(** Reused vocabulary: U7's [immersion] (Minor conjectures/U7.v), the immersion of the Open Problem Garden row
    coloring_and_immersion, whose walks may pass through branch vertices: the weak immersion of this row.  X296
    declares no helper of its own. *)

(** Corpus row: studies:std_lescure_meyniel_conjecture
    Site: none
    Review: none
    English statement: (Lescure and Meyniel; studies slice of the corpus, record arXiv:2510.05893)
      Every graph with chromatic number k contains a weak immersion of the complete graph K_k.
    Definitions: [immersion G H] - G contains an immersion of H: an injection f of the vertices of H into those of G
      and, for every edge uv of H, a walk in G from f(u) to f(v), the walks of distinct edges of H pairwise
      edge-disjoint; a walk may pass through any vertex, branch vertices included (Minor conjectures/U7.v);
      [χ([set: G])] - the chromatic number of G (coq-graph-theory); ['K_n] - the complete graph on n vertices.
    Notes: encoded as stated, with k the chromatic number of G.  A weak immersion asks for edge-disjoint paths that
      may pass through branch vertices (arXiv:2510.05893v1, 7 October 2025, israel2.tex l.82-101: conditions 1-3;
      condition 4, each path meets the branch vertices only at its ends, defines the strong immersion); U7's
      [immersion] is that notion, with walks, and a walk contains a path between its ends inside its own edges, so
      walks and paths give the same notion.  Degenerate instances: the graph with no vertex has chromatic number 0
      and immerses K_0.  The row is equivalent to U7's coloring_and_immersion_statement (chromatic number at least
      t > 0 gives an immersion of K_t; grounding_X296.v, g296_equiv_U7).  The conjecture is Conjecture 1.1 of Fox,
      Pach and Suk (l.103-107), attributed to Lescure and Meyniel (1989).  Literature: open at the pin; verified for
      4 <= k <= 6 by DeVos, Kawarabayashi, Mohar and Okamura, open for k >= 7 (l.109); the record proves it for
      graphs with fewer than 1.4k - 0.6 vertices, and for large k with fewer than (1.64 - eps)k (l.114-120). *)
Definition lescure_meyniel_weak_immersion_statement : Prop :=
  forall G : sgraph, immersion G 'K_(χ([set: G])).

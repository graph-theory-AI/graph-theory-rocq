(** * Minor.conjectures.X291 -- v2 row: Las Vergnas and Meyniel's Conjecture C, a quasi-K_t-minor gives a
      K_t-minor *)

From GraphTheory Require Import minor.
From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X291 vocabulary *****************************************************)

(** G admits a quasi-K_t-minor (Bonamy, Heinrich, Legrand-Duchesne and Narboni, arXiv:2103.10684v2, main.tex l.172,
    after Las Vergnas and Meyniel): t bags [B i], indexed by 'I_t (the source's B_1, ..., B_t), non-empty and
    pairwise disjoint, such that for any i <> j the union B_i u B_j induces a connected subgraph of G (GraphTheory's
    [connected], induced connectivity).  A K_t-minor asks each bag to be connected and an edge between any two bags;
    the quasi version drops the first and replaces it by the connected unions.  The source keeps the edge between
    two bags; it is not a separate conjunct here, since two non-empty disjoint sets with a connected union always
    have an edge between them (grounding_X291.v, [g291_union_edge]). *)
Definition x291_quasi_complete_minor (G : sgraph) (t : nat) : Prop :=
  exists B : 'I_t -> {set G},
    [/\ forall i, B i != set0,
        forall i j, i != j -> [disjoint B i & B j] &
        forall i j, i != j -> connected (B i :|: B j)].

(** ** X291 statement ******************************************************)

(** Corpus row: studies:std_las_vergnas_meyniel_conjecture_c_quasi_minors
    Site: none
    Review: none
    English statement: (Las Vergnas and Meyniel; studies slice of the corpus, record arXiv:2103.10684)
      For any t, any graph that admits a quasi-K_t-minor admits a K_t-minor.
    Definitions: [x291_quasi_complete_minor G t] - t non-empty pairwise disjoint bags of G, any two with a
      connected union (this file); [minor G 'K_t] - K_t is a minor of G (coq-graph-theory), i.e. t non-empty
      pairwise disjoint connected bags with an edge between any two.
    Notes: encoded as stated; pinned status open, but FALSE at the pin.  The statement is Conjecture C of Las
      Vergnas and Meyniel as Bonamy, Heinrich, Legrand-Duchesne and Narboni quote it (arXiv:2103.10684v2, main.tex
      l.178-180), after their definitions of K_p-minors and quasi-K_p-minors (l.172).  They report it known for
      t <= 10 (l.183-185) and refute it for large t: their Theorem th:mainfull (l.187-189) gives, for every
      eps > 0 and every large enough t, a graph with a quasi-K_t-minor and no K_((2/3 + eps) t)-minor; no explicit
      t is known (l.185), and the construction had been found independently before (l.296).  "Admits a
      K_t-minor" is [minor G 'K_t], as in U7.  The instances t = 0 (no bag; every graph has K_0 as a minor) and
      t = 1 (one non-empty bag; a graph with a vertex has K_1 as a minor) hold.  The status correction is a
      separate corpus item. *)
Definition las_vergnas_meyniel_quasi_minor_statement : Prop :=
  forall (t : nat) (G : sgraph), x291_quasi_complete_minor G t -> minor G 'K_t.

(** * Minor.conjectures.X214 -- Bondy-Murty minors and subdivisions rows (wave X214, 2026-09-23) *)

From GTBase Require Export base.
From Minor.foundations Require Import containment.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x214 vocabulary ***********************************************

    None.  The three rows are stated with library / GTBase vocabulary only:
    [k_connected] and [wagner_planar] (GTBase.base), [minor] and ['K_n]
    (coq-graph-theory), [χ(A)] (coq-graph-theory's [chi_mem]) and
    [has_subdivision] (Minor.foundations.containment). *)

(** ** X214 statements *****************************************************)

(** Corpus row: bm:bm-029
    Site: https://graph-theory-ai.github.io/graph-conjectures/bm/bm-029/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/bondy_murty_reviews/bm-029.json
    English statement: (Kelmans and Seymour; Bondy and Murty, "Graph Theory", Appendix A,
      unsolved problem 29)
      Every finite simple graph that is 5-connected and not planar contains a subdivision of
      the complete graph on five vertices.
    Definitions: [k_connected G 5] - G has more than five vertices and stays connected after
      deleting any set of fewer than five vertices (Whitney form, base/theories/base.v);
      [wagner_planar G] - G has neither a K5 minor nor a K3,3 minor, which by Wagner's theorem
      is exactly planarity (base/theories/base.v); [has_subdivision G H] - G contains a
      subdivision of H: injective branch vertices for the vertices of H together with
      internally disjoint paths for the edges of H, interiors avoiding all branch vertices
      (minor-theory/theories/foundations/containment.v); ['K_5] - the complete graph on five
      vertices (coq-graph-theory).
    Notes: planarity is expressed by Wagner's excluded-minor characterisation, so the
      hypothesis "non-planar" reads "G has a K5 minor or a K3,3 minor"; this is an
      axiom-free planarity predicate for finite simple graphs and needs no embedding layer.
      Subdivision containment is NOT required to be induced, matching the source.  The corpus
      records this row as solved (He, Wang and Yu, J. Combin. Theory Ser. B 144, 2020).
      Second reader (2026-09-23): the hypothesis is written [~ wagner_planar G], i.e. the
      negation of a conjunction of two negated minor relations, rather than the disjunction
      "G has a K5 minor or a K3,3 minor".  The two are classically equivalent (and [minor] is a
      decidable property of two finite graphs); the disjunction implies the negated form, so
      the encoded hypothesis holds at least as often and the encoded row is at least as strong
      as the source -- it can never be a weakening. *)
Definition kelmans_seymour_k5_subdivision_statement : Prop :=
  forall G : sgraph, k_connected G 5 -> ~ wagner_planar G -> has_subdivision G 'K_5.

(** Corpus row: bm:bm-041
    Site: https://graph-theory-ai.github.io/graph-conjectures/bm/bm-041/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/bondy_murty_reviews/bm-041.json
    English statement: (Hadwiger 1943; Bondy and Murty, "Graph Theory", Appendix A, unsolved
      problem 41)
      For every natural number k, every finite simple graph whose chromatic number is exactly
      k has the complete graph on k vertices as a minor.
    Definitions: [χ([set: G])] - the chromatic number of G (coq-graph-theory's [chi_mem]);
      [minor G H] - H is a minor of G, i.e. there is a branch-set map realising H
      (coq-graph-theory's [minor.v]); ['K_k] - the complete graph on k vertices
      (coq-graph-theory).
    Notes: "k-chromatic" is read as the exact equality [χ(G) = k], as in the source; the
      variant with [k <= χ(G)] is equivalent because a graph of chromatic number at least k
      has an induced subgraph of chromatic number exactly k, but the exact form is the one
      stated.  The corpus records this row as open (settled for k <= 6). *)
Definition hadwiger_chromatic_clique_minor_statement : Prop :=
  forall (k : nat) (G : sgraph), χ([set: G]) = k -> minor G 'K_k.

(** Corpus row: bm:bm-042
    Site: https://graph-theory-ai.github.io/graph-conjectures/bm/bm-042/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/bondy_murty_reviews/bm-042.json
    English statement: (Hajos 1961; Bondy and Murty, "Graph Theory", Appendix A, unsolved
      problem 42, restricted to k = 5 and k = 6)
      For k = 5 and for k = 6, every finite simple graph whose chromatic number is exactly k
      contains a subdivision of the complete graph on k vertices.
    Definitions: [χ([set: G])] - the chromatic number of G (coq-graph-theory's [chi_mem]);
      [has_subdivision G H] - G contains a subdivision of H
      (minor-theory/theories/foundations/containment.v); ['K_k] - the complete graph on k
      vertices (coq-graph-theory).
    Notes: the source asks the question only for k = 5 and k = 6, so the statement carries the
      disjunction [k = 5 \/ k = 6] as a hypothesis rather than quantifying over all k (Hajos'
      original conjecture for all k was refuted by Catlin for every k >= 7, and holds for
      k <= 4 by Dirac).  Subdivision containment is not required to be induced. *)
Definition hajos_k5_k6_subdivision_statement : Prop :=
  forall (k : nat) (G : sgraph),
    (k = 5) \/ (k = 6) -> χ([set: G]) = k -> has_subdivision G 'K_k.

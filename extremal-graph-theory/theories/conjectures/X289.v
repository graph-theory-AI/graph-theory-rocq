(** * Extremal.conjectures.X289 -- v2 rows: counting cycles by the number of edges (Kiraly's O(1.4^m) and 4-regular
      conjectures, and Conjecture 2 of Dvorak, Morrison, Noel, Norin and Postle) *)

From GTBase Require Import base.
From Extremal.foundations Require Import edge_cycles.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X289 statements ******************************************************** *)

(** Corpus row: studies:std_kir_ly_s_cycle_count_conjecture
    Site: none
    Review: none
    English statement: (Kiraly's cycle-count conjecture; studies slice of the corpus, record arXiv:1907.12091)
      The number of cycles in a simple graph with m edges is O(1.4^m).
    Definitions: [edge_family_cycle_count G] - the number of cycles of G, each counted once as its edge set
      (Extremal.foundations.edge_cycles, the canonical count of the cycle-lengths family; X84 and X85 count with
      it); [E(G)] - the edge set of G (coq-graph-theory sg_edge_set).
    Notes: encoded as stated: some natural constant C bounds the count by C * (7/5)^m for every simple graph,
      written c(G) * 5^m <= C * 7^m.  A real constant rounds up to a natural one, and no threshold on m is needed (a
      graph with fewer than m0 edges has at most 2^m0 cycles, which a constant absorbs).  A cycle is a simple cycle
      of a simple graph (Kiraly's convention, EGRES TR-2009-03 l.48-51), so it has at least three vertices and
      is counted once.  Source: Kiraly, "Maximum Number of Cycles and Hamiltonian Cycles in Sparse Graphs", EGRES
      Technical Report 2009-03, Conjecture 7.15 (l.729: "If G is a graph with m edges then c(G) <= c * 1.4^m").
      Literature status: TRUE at the pin, by Dvorak, Morrison, Noel, Norin and Postle, arXiv:1907.12091v1, Theorem
      1 (numcycles9.tex l.67-69: O(gamma^m) with gamma ~ 1.384 < 1.4; l.65 "Our first main result proves this
      conjecture"); recorded solved by lit5 (CORPUS_FEEDBACK 27).  Theorem statements read, proofs not verified.
      The row was classified under cycle-theory; it is authored here because cycle-theory cannot import the
      canonical count of Extremal.foundations.edge_cycles. *)
Definition kiraly_cycle_count_one_point_four_statement : Prop :=
  exists C : nat, forall G : sgraph,
    edge_family_cycle_count G * 5 ^ #|E(G)| <= C * 7 ^ #|E(G)|.

(** Corpus row: studies:std_kir_ly_s_cycle_count_conjecture_for_4_regular_gr
    Site: none
    Review: none
    English statement: (Kiraly's cycle-count conjecture for 4-regular graphs; studies slice of the corpus, record
      arXiv:1907.12091)
      A 4-regular simple graph with m edges has at most 1.99^{m/2} cycles.
    Definitions: [regular G 4] - every vertex has exactly four neighbours (GTBase base.v);
      [edge_family_cycle_count G] - the number of cycles of G, each counted once as its edge set
      (Extremal.foundations.edge_cycles); [E(G)] - the edge set of G (coq-graph-theory sg_edge_set).
    Notes: encoded as printed, with no constant: c <= 1.99^(m/2) is c^2 <= 1.99^m, written
      c(G)^2 * 100^m <= 199^m (exact for every m).  Kiraly's own wording (EGRES TR-2009-03, Conjecture 7.14, l.727:
      "If G is 4-regular then c(G) <= 1.99^n") counts vertices; n = m/2 for 4-regular graphs.  Literature status:
      FALSE as printed: K_5 is 4-regular with m = 10 and has 10 + 15 + 12 = 37 cycles, more than 1.99^5 ~ 31.21;
      kernel-checked in applications/kiraly_four_regular_disproof.v (kiraly_four_regular_cycle_count_disproved,
      through 37 explicit cycles of K_5).  The asymptotic form holds: Dvorak, Morrison, Noel, Norin and Postle,
      arXiv:1907.12091v1, Theorem 3 (numcycles9.tex l.120-122, O(1.365^m) cycles at average degree 4, which l.118
      says proves Kiraly's conjecture).  Recorded disproved by lit11 (CORPUS_FEEDBACK 28).  The row was classified
      under cycle-theory; it is authored here because cycle-theory cannot import the canonical count. *)
Definition kiraly_four_regular_cycle_count_statement : Prop :=
  forall G : sgraph, regular G 4 ->
    edge_family_cycle_count G ^ 2 * 100 ^ #|E(G)| <= 199 ^ #|E(G)|.

(** Corpus row: arxiv:1907.12091#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1907.12091__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1907.12091__00.json
    English statement: (Dvorak, Morrison, Noel, Norin and Postle, arXiv:1907.12091, Conjecture 2)
      Every simple graph with m edges has at most O(kappa_1^m) cycles, where kappa_1 = (2 + 2 sqrt 2)^(1/5) ~ 1.3701.
    Definitions: [edge_family_cycle_count G] - the number of cycles of G, each counted once as its edge set
      (Extremal.foundations.edge_cycles); [E(G)] - the edge set of G (coq-graph-theory sg_edge_set).
    Notes: encoded exactly, without reals: c <= C0 kappa_1^m is c^5 <= C0^5 (2 + 2 sqrt 2)^m, and a bound
      c^5 <= C (2 + 2 p / r)^m for every rational p / r >= sqrt 2 (that is 2 r^2 <= p^2, r > 0) is the bound at
      sqrt 2, since the inequality is closed and p / r decreases to sqrt 2; conversely 2 + 2 p / r >= 2 + 2 sqrt 2.
      Written c(G)^5 * r^m <= C * (2 r + 2 p)^m with one natural C for all G, p and r (a real constant rounds up; no
      threshold on m is needed, as in the O(1.4^m) row).  Source: arXiv:1907.12091v1, numcycles9.tex l.108-112
      ("We believe that this construction is the best possible ... Every simple graph with m edges has at most
      O(kappa_1^m) cycles"); kappa_1 is the base of Arman and Tsaturian's Omega(kappa_1^m) construction (l.71,
      Figure 1).  Literature status: OPEN at the pin. *)
Definition cycle_count_kappa_one_statement : Prop :=
  exists C : nat, forall (G : sgraph) (p r : nat),
    0 < r -> 2 * r ^ 2 <= p ^ 2 ->
    edge_family_cycle_count G ^ 5 * r ^ #|E(G)| <= C * (2 * r + 2 * p) ^ #|E(G)|.

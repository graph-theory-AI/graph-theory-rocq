(** * Hamilton.conjectures.implications_X211 — wave X211 dependency-graph EDGES

    Machine-checked implication EDGES between the X211 statements (Bondy–Murty
    Appendix A rows) and the already-committed U2 Hamiltonicity statements.  As
    everywhere in this layer, an edge is a RELATIVE theorem: a [Qed]-closed
    [Theorem A_statement -> B_statement] proved WITHOUT resolving either
    endpoint.  No [Axiom], no [Admitted].

    Corpus relations covered (meta/corpus_relations.json, built from the
    graph-conjectures clone's data/relations.json):

    - gc:e234  bm:bm-079 (Matthews–Sumner)  <->  opg:hamiltonian_cycles_in_line_graphs
      (Thomassen's line-graph conjecture), relation `equivalent_to`, verdict
      confirmed.  The EASY direction is proved below: line graphs are claw-free,
      so the claw-free hypothesis of Matthews–Sumner applies to every line
      graph.  The converse (Ryjáček's 1997 closure theorem: the closure of a
      claw-free graph is the line graph of a triangle-free graph, and it
      preserves both connectivity and Hamiltonicity) is NOT formalised here — it
      is a substantial theorem, not a relative implication — so the reverse edge
      is recorded as a candidate.
    - gc:e244  bm:bm-079 => bm:bm-065 (Bondy's dominating-cycle/circumference
      row, cycle-theory).  Not emitted: bm-065 has no Rocq statement yet (it is
      scheduled for wave X212), so the edge has no second endpoint. *)

From GTBase Require Import base.
From GraphTheory Require Import bij.
From Hamilton.conjectures Require Import X211 U2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Line graphs are claw-free

    In [line_graph G] a vertex is an edge of [G] and two of them are adjacent
    iff they are distinct and share an endpoint.  An induced claw would give an
    edge [c] of [G] together with three edges [l 0], [l 1], [l 2] of [G], each
    meeting [c] but pairwise NOT meeting each other.  Every [l i] meets [c] in
    one of its two endpoints [a], [b], so by pigeonhole two of them meet [c] in
    the SAME endpoint — hence meet each other, contradicting non-adjacency. *)
Lemma line_graph_claw_free (G : sgraph) : x211_claw_free (line_graph G).
Proof.
move=> S h.
pose c : induced S := h^-1 (inl ord0).
pose l (i : 'I_3) : induced S := h^-1 (inr i).
have adjc : forall i : 'I_3, (val (l i) : line_graph G) -- val c.
  move=> i; rewrite -induced_edge; rewrite (edge_diso' h (inr i) (inl ord0)).
  by rewrite /edge_rel /= /kb_rel.
have nadj : forall i j : 'I_3, i != j ->
    ~~ ((val (l i) : line_graph G) -- val (l j)).
  move=> i j ij; rewrite -induced_edge (edge_diso' h (inr i) (inr j)).
  by rewrite /edge_rel /= /kb_rel.
have ldist : forall i j : 'I_3, i != j ->
    (val (l i) : line_graph G) != val (l j).
  move=> i j ij; apply/negP => /eqP/val_inj/(@bij_injective' _ _ (diso_v h)) e.
  move: (f_equal (fun z : 'K_1,3 => if z is inr k then k else ord0) e) => /= eij.
  by move: ij; rewrite eij eqxx.
have shareP : forall u w : line_graph G,
    u -- w -> exists v : G, (v \in lg_ends u) && (v \in lg_ends w).
  by move=> u w; rewrite /edge_rel /= /lg_rel => /andP[_ /existsP[v hv]]; exists v.
have adjP : forall (u w : line_graph G) (v : G),
    u != w -> v \in lg_ends u -> v \in lg_ends w -> u -- w.
  move=> u w v uw vu vw; rewrite /edge_rel /= /lg_rel uw /=.
  by apply/existsP; exists v; rewrite vu vw.
have key : forall (i j : 'I_3) (v : G), i != j ->
    v \in lg_ends (val (l i)) -> v \in lg_ends (val (l j)) -> False.
  move=> i j v ij vi vj; have := nadj i j ij.
  by rewrite (adjP _ _ v (ldist i j ij) vi vj).
pose a := (val (val c)).1; pose b := (val (val c)).2.
have leafab : forall i : 'I_3,
    (a \in lg_ends (val (l i))) || (b \in lg_ends (val (l i))).
  move=> i; have [v /andP[vi vc]] := shareP _ _ (adjc i).
  have vab : (v == a) || (v == b) by move: vc; rewrite /lg_ends !inE.
  by case/orP: vab => /eqP <-; rewrite vi ?orbT.
have h0 := leafab (@Ordinal 3 0 isT).
have h1 := leafab (@Ordinal 3 1 isT).
have h2 := leafab (@Ordinal 3 2 isT).
case/orP: h0 => h0; case/orP: h1 => h1; case/orP: h2 => h2.
- exact: (key (@Ordinal 3 0 isT) (@Ordinal 3 1 isT) a isT h0 h1).
- exact: (key (@Ordinal 3 0 isT) (@Ordinal 3 1 isT) a isT h0 h1).
- exact: (key (@Ordinal 3 0 isT) (@Ordinal 3 2 isT) a isT h0 h2).
- exact: (key (@Ordinal 3 1 isT) (@Ordinal 3 2 isT) b isT h1 h2).
- exact: (key (@Ordinal 3 1 isT) (@Ordinal 3 2 isT) a isT h1 h2).
- exact: (key (@Ordinal 3 0 isT) (@Ordinal 3 2 isT) b isT h0 h2).
- exact: (key (@Ordinal 3 0 isT) (@Ordinal 3 1 isT) b isT h0 h1).
- exact: (key (@Ordinal 3 0 isT) (@Ordinal 3 1 isT) b isT h0 h1).
Qed.

(** ** Edge 1 (VERIFIED): Matthews–Sumner ==> Thomassen's line-graph conjecture

    Every 4-connected line graph is a 4-connected claw-free graph, so it is
    Hamiltonian by Matthews–Sumner.  ([U2.is_hamiltonian] and
    [GTBase.common.hamiltonian] are the same predicate: "there is a [seq] of
    vertices that is a [ucycle] of size [#|G|]".) *)
(*@EDGE from=matthews_sumner_four_connected_claw_free_statement to=hamiltonian_cycles_in_line_graphs_statement kind=implies status=verified proof=matthews_sumner_four_connected_claw_free_implies_hamiltonian_cycles_in_line_graphs cite="gc:e234; Matthews & Sumner 1984; Ryjacek, JCTB 70 (1997) 217-224 (closure)" note="Easy direction of the confirmed equivalence: line graphs are claw-free (line_graph_claw_free, proved in this file), so the 4-connected line graph hypothesis is a special case of the 4-connected claw-free hypothesis" *)
Theorem matthews_sumner_four_connected_claw_free_implies_hamiltonian_cycles_in_line_graphs :
  matthews_sumner_four_connected_claw_free_statement ->
  hamiltonian_cycles_in_line_graphs_statement.
Proof.
move=> MS G kc.
have [c hc] := MS (line_graph G) kc (@line_graph_claw_free G).
by exists c.
Qed.

(** ** Edge 2 (CANDIDATE): the converse direction of the same equivalence

    Thomassen's line-graph conjecture ==> Matthews–Sumner is the HARD direction
    of the corpus equivalence gc:e234: it needs Ryjáček's closure operator
    cl(G) (add, for every locally connected vertex, all edges inside its
    neighbourhood), the theorem that cl(G) is the line graph of a triangle-free
    graph, and the facts that the closure preserves connectivity and
    circumference.  None of that is available in this corpus, and it cannot be
    carried as a relative theorem, so the edge is recorded as a candidate and
    NOT cited as gc:e234 (the corpus relation is oriented bm-079 -> opg row, and
    the machine-readable endpoint check of meta/build_edge_graph.py compares
    from/to with that orientation). *)
(*@EDGE from=hamiltonian_cycles_in_line_graphs_statement to=matthews_sumner_four_connected_claw_free_statement kind=implies status=candidate proved=false cite="Ryjacek, On a closure concept in claw-free graphs, JCTB 70 (1997) 217-224; corpus relation e234 (equivalent_to, confirmed)" note="Hard direction: needs the Ryjacek closure (claw-free closure is a line graph of a triangle-free graph, preserving connectivity and circumference), a substantial unformalised theorem; not provable as a relative implication here" *)

(** ** Non-edges checked

    - [cantoni_planar_cubic_three_hamilton_cycles_statement],
      [thomassen_vertex_transitive_all_but_finitely_many_statement],
      [chvatal_toughness_hamiltonian_statement],
      [hypohamiltonian_minimum_degree_four_statement] and
      [grotschel_no_bipartite_hypotraceable_statement] carry no confirmed
      corpus relation to a formalised row (their `related_edges` lists are
      empty in meta/v2_wave_plan.json), and none of them specialises to, or
      follows from, a U2 statement: the hypothesis classes (planar cubic with
      exactly three Hamilton cycles; connected vertex-transitive above a size
      threshold; k-tough; hypohamiltonian of minimum degree 4; bipartite
      hypotraceable) are pairwise incomparable with the U2 ones (4-connected,
      r-regular, prisms, toroidal, line graphs).
    - [barnette_simple_four_polytope_hamiltonian_statement] is a BLOCKED
      placeholder (row bm-080); it is deliberately not an edge endpoint. *)

(** ** Axiom audit: the edge theorem is [Qed]-closed and axiom-free. *)
Print Assumptions line_graph_claw_free.
Print Assumptions matthews_sumner_four_connected_claw_free_implies_hamiltonian_cycles_in_line_graphs.

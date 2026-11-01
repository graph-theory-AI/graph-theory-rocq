(** * GTMisc.conjectures.X274 -- v2 rows: the Kalai-Meshulam conjecture, the linear arboricity conjecture, the
    Walther-Zamfirescu longest-path-transversal question *)

From GTBase Require Import base induced_cycles edge_colourings path_trees.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X274 statements *****************************************************)

(** Corpus row: studies:std_kalai_meshulam_conjecture
    Site: none
    Review: none
    English statement: (Kalai and Meshulam; studies slice of the corpus, record arXiv:1810.00065)
      For every ternary graph, the number of stable sets with even cardinality and the number with odd cardinality
      differ by at most one.  Equivalently, if f_G = sum over stable sets A of (-1)^|A|, then |f_G| <= 1.
    Definitions: [has_ordinal_induced_cycle G k] - an injective map from 'I_k to G whose images are adjacent exactly
      at cyclically consecutive positions, an induced cycle on k vertices (GTBase induced_cycles); "ternary" is
      inlined: no such cycle for any k >= 3 divisible by three; [stable A] - no edge of G inside A
      (coq-graph-theory); the sets A range over all of {set G}, the empty set included, as in f_G; e and o count the
      stable sets of even and of odd cardinality.
    Notes: encoded as stated: e <= o + 1 and o <= e + 1 is |e - o| <= 1, and f_G = e - o, so both sentences are
      this statement.  TRUE at the pin: Chudnovsky, Scott, Seymour and Spirkl, "Proof of the Kalai-Meshulam
      conjecture", arXiv:1810.00065v1 (main.tex l.86-94: Kalai and Meshulam's two conjectures, "both now
      theorems", this row being (1.2) at l.91-94; the abstract, l.71-77: "We prove this conjecture", with
      f_G = +-2 on cycles of length divisible by three, which counts the empty set).  "Ternary" is their
      definition (l.83: no induced cycle has length a multiple of three), read as X236 reads it ([x236_ternary],
      chromatic-theory X236.v l.27-28, for the row arxiv:1810.00065#00): lengths start at 3, since 3 divides 0 and
      every graph has the induced cycle on no vertex.  The body is inlined, not imported, since graph-theory-misc
      cannot import Chromatic.  The pinned status open is for a separate literature item. *)
Definition kalai_meshulam_even_odd_stable_sets_statement : Prop :=
  forall G : sgraph,
    (forall k : nat, 3 <= k -> 3 %| k -> ~ has_ordinal_induced_cycle G k) ->
    let e := #|[set A : {set G} | stable A && ~~ odd #|A|]| in
    let o := #|[set A : {set G} | stable A && odd #|A|]| in
    e <= o.+1 /\ o <= e.+1.

(** Corpus row: studies:std_linear_arboricity_conjecture
    Site: none
    Review: none
    English statement: (Akiyama, Exoo and Harary; studies slice of the corpus, record arXiv:1809.04716)
      Let G be a graph of maximum degree Delta.  Then, la(G) <= ceil((Delta + 1) / 2).
    Definitions: [Delta G] - the maximum degree, the maximum of #|N(v)| over the vertices (GTBase base; 0 on the
      empty graph); [ceil_div a b] - ceil(a / b) (GTBase base); [edge_colour_class col (pred1 i)] - the spanning
      subgraph of G carrying exactly the edges {x, y} with col {x, y} = i (GTBase edge_colourings);
      [linear_forest H] - H is a forest of maximum degree at most 2, a disjoint union of paths (GTBase path_trees).
      la(G), the linear arboricity, is the minimum number of edge-disjoint linear forests (forests whose components
      are paths) in G whose union is E(G) (arXiv:1809.04716v1, main.tex l.133; isolated vertices allowed, l.135);
      so la(G) <= k iff some colouring of the edges with k colours has every colour class a linear forest.
    Notes: encoded as stated.  OPEN at the pin: Ferber, Fox and Jain, "Towards the linear arboricity conjecture",
      arXiv:1809.04716v1 (13 September 2018, its only version), state it as Conjecture 1.1 (main.tex l.139-143)
      and prove la(G) <= Delta/2 + C Delta^(2/3 - alpha) for Delta-regular G (Theorem 1.3, l.156-162): progress,
      not the conjecture.  Their Remark 1.2 (l.145-147), equivalence with the regular case, does not restrict the
      row's domain.  The colouring is a map on all of {set G}; only its values on the edges matter, a class keeping
      exactly the edges of its colour.  G ranges over simple graphs, the source's setting (its bound la(G) <=
      Delta + 1 by Vizing's theorem, l.135, is a simple-graph bound); a multigraph version is not this row.  The
      empty graph and K_1 hold (Delta = 0, one colour, no edge: la(G) = 0, the colour unused).  Related rows:
      bm:bm-016 (cycle-theory X212, regular graphs, partial) and topological X23 (planar graphs): candidate edges,
      not in this wave. *)
Definition linear_arboricity_conjecture_statement : Prop :=
  forall G : sgraph,
    exists col : {set G} -> 'I_(ceil_div (Delta G + 1) 2),
      forall i, linear_forest (edge_colour_class col (pred1 i)).

(** Corpus row: studies:std_walther_zamfirescu_longest_path_transversal_ques
    Site: none
    Review: none
    English statement: (Walther and Zamfirescu; studies slice of the corpus, record arXiv:2505.08634)
      Does there exist an absolute constant c > 0 such that every connected graph G satisfies lpt(G) <= c?
    Definitions: [connected [set: G]] - G is connected (coq-graph-theory; the empty graph counts as connected); a
      path of G is a vertex sequence x :: p with consecutive vertices adjacent ([path (@sedge G) x p]) and no
      repeated vertex ([uniq (x :: p)]); it is longest when no path has more vertices ([size p], its number of
      edges, is maximal); lpt(G) <= c: a set T of at most c vertices meets every longest path (inlined).
    Notes: encoded as the affirmative answer, the corpus's precedent for question rows: one c > 0 for all graphs,
      a natural number since lpt(G) is one, and at least 1 since lpt(K_1) = 1, so a natural c with 0 < c loses
      nothing.  "Longest" means most vertices, equivalently most edges, as Norin,
      Steiner, Thomasse and Wollan define it (arXiv:2505.08634v2, main.tex l.84, footnote: a path attaining the
      maximum possible length).  OPEN at the pin: there (main.tex l.84; text l.62-65) the question "remains widely
      open", and no connected graph with lpt(G) > 3 is known.  Their Theorem 1 (main.tex l.89-94) gives
      lpt(G) <= min{sqrt(8n), 33 l^(5/9)} for connected G on n >= 2 vertices: progress, not an answer.  The empty
      graph holds (T = set0; it has no path), and so does K_1 (T = {v}).  The record 2505.08634 is also attached to
      studies:std_thomassen_s_conjecture_exponentially_many_3_colo, a misattachment recorded in
      meta/CORPUS_FEEDBACK.md item 58 (lit17); this row is the paper's subject.  The longest-path vocabulary of
      homomorphism-theory (U3.v [longest_path]) is not importable here, so the body is inlined; unlike U3's
      [is_path], which allows the empty sequence and so needs a guard 0 < #|G| there, a path here has a first
      vertex x, and no guard is needed. *)
Definition walther_zamfirescu_bounded_longest_path_transversal_statement : Prop :=
  exists c : nat, 0 < c /\
    forall G : sgraph, connected [set: G] ->
      exists T : {set G}, #|T| <= c /\
        forall (x : G) (p : seq G),
          path (@sedge G) x p -> uniq (x :: p) ->
          (forall (x' : G) (p' : seq G), path (@sedge G) x' p' -> uniq (x' :: p') -> size p' <= size p) ->
          exists2 v, v \in T & v \in x :: p.

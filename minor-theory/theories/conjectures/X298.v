(** * Minor.conjectures.X298 -- v2 rows: rooted complete minors, Holroyd's Strong Hadwiger conjecture (record
      arXiv:2209.00594) and Dvorak and Swart's rooted-minor-free realizations of colourings (arXiv:2504.07764) *)

From GTBase Require Import base colourings.
From GraphTheory Require Import minor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X298 statements *****************************************************)

(** Reused vocabulary: coq-graph-theory's [minor_rmap] (a model of a minor by branch sets), ['K_n] and [χ(A)],
    GTBase.colourings [proper_colouring].  A rooted model is a [minor_rmap] whose branch sets all meet the root
    set, written out in each statement.  X298 declares no helper of its own. *)

(** Corpus row: studies:std_strong_hadwiger_s_conjecture_holroyd
    Site: none
    Review: none
    English statement: (Holroyd; studies slice of the corpus, record arXiv:2209.00594)
      Let G be a graph with chi(G) = t, and let S be a colorful set in G.  Then G contains an S-rooted
      K_t-minor.
    Definitions: [χ([set: G])] - the chromatic number of G (coq-graph-theory); S is colorful when every proper
      colouring [col : G -> 'I_(χ([set: G]))] ([proper_colouring], GTBase.colourings: adjacent vertices get
      different colours) gives every colour to some vertex of S; an S-rooted K_t-minor is a map [phi] from the
      vertices of ['K_t] to vertex sets of G with [minor_rmap phi] (coq-graph-theory: the branch sets are
      non-empty, connected and pairwise disjoint, and adjacent vertices of K_t get sets joined by an edge) and
      every branch set meeting S.
    Notes: encoded as stated (arXiv:2209.00594v1, Martinsson and Steiner, source.tex l.137-139, their
      Conjecture 1.2, Holroyd's Strong Hadwiger conjecture of 1997), with t read off G as chi(G), as X214 states
      Hadwiger's conjecture.  A K_t-minor is t pairwise disjoint non-empty vertex sets, each inducing a connected
      graph, pairwise adjacent (l.122): [minor_rmap] on ['K_t].  S-rooted means that every branch set meets S,
      and S is colorful when every proper chi(G)-colouring has all chi(G) colours on S (l.133).  The graph with
      no vertex has chi 0 and the empty model.  Taking S = V(G) gives Hadwiger's conjecture (X214's
      [hadwiger_chromatic_clique_minor_statement]), which a later edge item may record.  Pinned status open;
      open at the pin: Holroyd proved t <= 3 and the record proves t = 4 (l.141-145, Theorem 1.3). *)
Definition holroyd_strong_hadwiger_statement : Prop :=
  forall (G : sgraph) (S : {set G}),
    (forall col : G -> 'I_(χ([set: G])), proper_colouring col ->
       forall i : 'I_(χ([set: G])), exists2 s, s \in S & col s = i) ->
    exists phi : ('K_(χ([set: G]))) -> {set G},
      minor_rmap phi /\ (forall i, phi i :&: S != set0).

(** Corpus row: arxiv:2504.07764#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2504.07764__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2504.07764__00.json
    English statement: (Dvorak and Swart, Conjecture 4 of arXiv:2504.07764)
      For every integer k >= 3, there exists a set X of vertices and a set C of k-colorings of X such that no
      X-rooted-K_k-minor-free graph G realizes C.
    Definitions: X is ['I_n], placed in a graph G by an injective map [x : 'I_n -> G]; a k-colouring of X is
      a function [{ffun 'I_n -> 'I_k}], and a set of k-colourings is a set [C] of them closed under colour
      permutations (with f, it holds [pi o f] for every bijective [pi : 'I_k -> 'I_k]); G is
      X-rooted-K_k-minor-free when no map [phi] from the vertices of ['K_k] to vertex sets of G has
      [minor_rmap phi] (coq-graph-theory: non-empty, connected, pairwise disjoint branch sets, adjacent vertices
      of K_k getting sets joined by an edge) with every branch set meeting the image of x; G realizes C when a
      colouring f is in C exactly when some proper colouring [col : G -> 'I_k] ([proper_colouring],
      GTBase.colourings) extends it, [col (x j) = f j] for every j.
    Notes: encoded as stated (arXiv:2504.07764v1, main.tex l.102-105; Conjecture 4 by the shared theorem
      counter, l.15-19).  A set of k-colorings is closed under permutations of colours, and G realizes C when X
      is a subset of V(G) and each f : X -> [k] is in C iff it extends to a proper k-colouring of G (l.38-42).
      X is chosen before G (l.103), so it is the index set 'I_n with an injective placement in G; the
      permutations are the bijections of 'I_k.  Models and X-rooted models (l.75-83) are [minor_rmap] with every
      branch set meeting the image of X.  Neither trivial witness works: the set of all colourings is realized
      by the edgeless graph on X, and the empty set by X beside a disjoint K_(k+1) (its rooted branch sets
      cannot be adjacent), so a witness C is neither (grounding_X298.v, at k = 3).  Holroyd's conjecture would
      imply this one (l.99-101; the row studies:std_strong_hadwiger_s_conjecture_holroyd of this wave), which a
      later edge item may record.  The paper proves the realization for X-rooted-K_(k+1)-minor-free
      K_(k+2)-minor-free graphs (Theorem 3, l.92-95).  Pinned status open; open at the pin. *)
Definition rooted_minor_free_unrealizable_colourings_statement : Prop :=
  forall k : nat, 3 <= k ->
  exists (n : nat) (C : {set {ffun 'I_n -> 'I_k}}),
    (forall (pi : 'I_k -> 'I_k) (f : {ffun 'I_n -> 'I_k}),
       bijective pi -> f \in C -> [ffun j => pi (f j)] \in C) /\
    (forall (G : sgraph) (x : 'I_n -> G), injective x ->
       ~ (exists phi : ('K_k) -> {set G},
            minor_rmap phi /\ (forall i, phi i :&: [set x j | j in 'I_n] != set0)) ->
       ~ (forall f : {ffun 'I_n -> 'I_k},
            f \in C <-> exists2 col : G -> 'I_k, proper_colouring col & forall j, col (x j) = f j)).

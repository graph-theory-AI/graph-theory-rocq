(** * Extremal.conjectures.X308 -- v2 rows: Engbers' questions on connected graphs of minimum degree at least delta:
      K_(delta,n-delta) maximises the number of H-colourings
      (studies:std_engbers_question_on_h_colourings_of_connected_gr) and uniquely maximises the number of proper
      q-colourings, q > 2
      (studies:std_engbers_question_on_maximising_proper_q_colourin) *)

From GTBase Require Import base colourings.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X308 vocabulary *****************************************************)

(** The source's H is "a simple graph, possibly with loops" (arXiv:1611.02911v2, source.tex l.56). X308 represents it
    as an sgraph H (its loopless part) with a set [L] of looped vertices. *)

(** [x308_lhom_count G L] is hom(G, H) for H with the loops [L]: the number of maps f : G -> H such that adjacent
    vertices go to adjacent vertices or to one looped vertex. *)
Definition x308_lhom_count (G H : sgraph) (L : {set H}) : nat :=
  #|[set f : {ffun G -> H} |
      [forall x : G, [forall y : G, (x -- y) ==> ((f x -- f y) || ((f x == f y) && (f x \in L)))]]]|.

(** The vertex set [C] spans a complete looped graph: every vertex of [C] is looped and any two distinct vertices of
    [C] are adjacent. *)
Definition x308_complete_looped (H : sgraph) (L : {set H}) (C : {set H}) : Prop :=
  C \subset L /\ (forall x y : H, x \in C -> y \in C -> x != y -> x -- y).

(** The vertex set [C] spans a complete balanced bipartite graph K_(l,l): no vertex of [C] is looped, and [C] has a
    part [A] with as many vertices as [C :\: A] such that two vertices of [C] are adjacent exactly when they lie on
    opposite sides. *)
Definition x308_complete_balanced_bipartite (H : sgraph) (L : {set H}) (C : {set H}) : Prop :=
  [disjoint C & L] /\
  exists A : {set H},
    [/\ A \subset C, #|A| = #|C :\: A|
      & forall x y : H, x \in C -> y \in C -> (x -- y) = (x \in A) (+) (y \in A)].

(** The uniqueness condition of Corollary 1.2, with the non-trivial guard: H has a component [C] (a nonempty connected
    vertex set closed under adjacency) that contains an edge or a loop and is neither a complete looped graph nor a
    complete balanced bipartite graph. *)
Definition x308_uniqueness_hyp (H : sgraph) (L : {set H}) : Prop :=
  exists C : {set H},
    [/\ C != set0, connected C, (forall x y : H, x \in C -> x -- y -> y \in C),
        (exists x y : H, [/\ x \in C, y \in C & x -- y]) \/ (C :&: L != set0)
      & ~ x308_complete_looped L C /\ ~ x308_complete_balanced_bipartite L C].

(** ** X308 statements *****************************************************)

(** Corpus row: studies:std_engbers_question_on_h_colourings_of_connected_gr
    Site: none
    Review: none
    English statement: (Engbers, J Graph Theory 85 (2017); answered by Guggiari and Scott, arXiv:1611.02911v2,
      source.tex l.71-74, Corollary 1.2, encoded in that form; the pinned question asks "uniquely" for every H)
      For every delta >= 3 and every graph H (simple, possibly with loops) there is a constant kappa(delta, H) such
      that every connected graph G on n >= kappa(delta, H) vertices with minimum degree at least delta satisfies
      hom(G, H) <= hom(K_(delta,n-delta), H); further, if H has a non-trivial component which is neither a complete
      looped graph nor a complete balanced bipartite graph, equality holds only for G = K_(delta,n-delta).
    Definitions: [x308_lhom_count G L] - hom(G, H) for the sgraph H with the looped vertices L (this file);
      [x308_uniqueness_hyp L] - H has a component with an edge or a loop that is neither complete looped
      ([x308_complete_looped]) nor complete balanced bipartite ([x308_complete_balanced_bipartite]) (this file);
      [min_degree_at_least G delta] - every vertex has at least delta neighbours (base.v); [connected [set: G]];
      [KB a b] - the complete bipartite graph K_(a,b); [diso] - graph isomorphism (coq-graph-theory).
    Notes: the pinned question asks whether K_(delta,n-delta) UNIQUELY maximises hom(G, H) for every graph H.  Its own
      record answers it in the form encoded here (Corollary 1.2, l.71-74; Theorem 1.1, l.64-67, for connected H): the
      maximisation holds for every H, and uniqueness needs the component condition.  The literal question is false:
      for H = K_2 = K_(1,1) every connected bipartite G has hom(G, H) = 2 (l.155-157), so K_(delta,n-delta) and
      K_(delta+1,n-delta-1) tie (CORPUS_FEEDBACK).  The component in the condition must be NON-TRIVIAL (an edge or a
      loop, l.178): a single unlooped vertex is neither complete looped nor complete balanced bipartite, yet for
      H = K_1 every G with an edge has hom(G, H) = 0; the proof treats maximum degree k >= 1 only (l.149, l.159,
      l.407).  [g308_not_trivially_true] in grounding_X308.v shows that the clause without the guard fails at K_1.
      Loops: an sgraph with a set of looped vertices is exactly a simple graph possibly with loops (at most one loop
      per vertex); components are those of the loopless part.  "Equality only for G = K" is encoded as a strict
      inequality for every G of the class not isomorphic to K_(delta,n-delta); isomorphic graphs have equal counts.
      "n >= kappa" is "exists N" after delta and H.  #|G| - delta is a truncated subtraction, exact once N >= delta
      (N may be taken that large), so K_(delta,n-delta) has n vertices.  Status: answered in the record (2018, before
      the pin); the pinned status is open, and any change is the maintainer's. *)
Definition engbers_connected_h_colouring_maximisation_statement : Prop :=
  forall (delta : nat) (H : sgraph) (L : {set H}),
    3 <= delta ->
    exists N : nat, forall G : sgraph,
      N <= #|G| -> connected [set: G] -> min_degree_at_least G delta ->
      x308_lhom_count G L <= x308_lhom_count (KB delta (#|G| - delta)) L /\
      (x308_uniqueness_hyp L -> ~ inhabited (diso G (KB delta (#|G| - delta))) ->
         x308_lhom_count G L < x308_lhom_count (KB delta (#|G| - delta)) L).

(** Corpus row: studies:std_engbers_question_on_maximising_proper_q_colourin
    Site: none
    Review: none
    English statement: (Engbers, J Graph Theory 85 (2017); as stated by Guggiari and Scott, arXiv:1611.02911v2,
      source.tex l.78-80, Corollary 1.3)
      Fix delta >= 3 and q > 2. Then, for n sufficiently large, K_(delta,n-delta) uniquely maximises the number of
      proper q-colourings amongst all connected graphs on n vertices with minimum degree at least delta.
    Definitions: [proper_colouring f] - adjacent vertices get different colours (colourings.v), counted over the maps
      G -> 'I_q; [min_degree_at_least G delta] (base.v); [connected [set: G]]; [KB a b] and [diso]
      (coq-graph-theory).
    Notes: "uniquely maximises" is encoded as a strict inequality for every G of the class not isomorphic to
      K_(delta,n-delta) (isomorphic graphs have equal counts); "n sufficiently large" is "exists N" after delta and q.
      For q > 2, K_q is neither complete looped nor complete balanced bipartite, so this is Theorem 1.1 at H = K_q
      (l.76); q = 2 is excluded because K_2 = K_(1,1).  #|G| - delta is a truncated subtraction, exact once N >= delta,
      so K_(delta,n-delta) has n vertices.  Status: answered affirmatively in the record (2018, before the pin); the
      pinned status is open, and any change is the maintainer's. *)
Definition engbers_connected_q_colouring_uniqueness_statement : Prop :=
  forall delta q : nat,
    3 <= delta -> 2 < q ->
    exists N : nat, forall G : sgraph,
      N <= #|G| -> connected [set: G] -> min_degree_at_least G delta ->
      ~ inhabited (diso G (KB delta (#|G| - delta))) ->
      #|[set f : {ffun G -> 'I_q} | proper_colouring f]| <
        #|[set f : {ffun KB delta (#|G| - delta) -> 'I_q} | proper_colouring f]|.

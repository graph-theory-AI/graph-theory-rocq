(** * Hypergraph.conjectures.U12 — milestone U12 (namespace Hypergraph, plan v4)

    Statement-only formalizations (axiom-free: no Conjecture/Axiom/Parameter/
    Admitted) of four OPEN problems on finite hypergraphs.

    CARRIERS ARE CHOSEN PER ROW (no blanket [sgraph]).  Every row is about
    finite hypergraphs, modelled — following each row's [rocq_idiom] — as a
    finite vertex type [T : finType] together with a family of hyperedges
    [E : {set {set T}}] (each hyperedge a vertex set).  Frankl's row (Row 1)
    operates directly on the set family [F : {set {set T}}], exactly as in the
    union-closed-sets formulation.

      - Row 1 (Frankl's union-closed sets): family [F : {set {set T}}],
        carrier [{set {set T}}];
      - Row 2 (Turán for 3-uniform hypergraphs): vertices [T : finType],
        hyperedges [E : {set {set T}}];
      - Row 3 (critical k-forests): vertices [T], hyperedges [E];
      - Row 4 (Ryser): vertices [T] with an r-part assignment [part : T -> 'I_r],
        hyperedges [E].

    No multigraph [edge]/[source]/[target] API is needed (object level is vertex
    SUBSETS), so we do not import coq-graph-theory's [mgraph]; [base] (which
    re-exports all_boot + the undirected vocabulary, [finset], [tuple], …) is the
    sole import.  No base primitive matches these hypergraph notions, so every
    primitive below is AREA-SPECIFIC (none is a cross-area [@MOVE-to-base]
    candidate at this point — they are hypergraph-only).

    AREA primitives introduced here (all hypergraph-specific): [union_closed]
    (union-closed-family, Row 1); [k_uniform] (uniform-hypergraph, Rows 2,3),
    [complete_sub] / [contains_complete] (complete-hypergraph K_m^{(k)} subobject,
    Row 2) — [#|E|] is the hyperedge-count directly; [berge_cycle] / [berge_acyclic]
    / [hg_connected] / [k_forest] / [k_tree] / [critical_k_forest] (k-forest,
    k-tree and forest-maximality "criticality", Row 3); [r_partite_uniform]
    (r-partite-uniform), [hg_matching] / [is_matching_number] (ν, matching-number),
    [hg_cover] / [is_cover_number] (τ, cover-number) (Row 4).

    NAMING: predicates carrying an existence/uniqueness extremal flavour use the
    [is_] prefix ([is_matching_number], [is_cover_number]); the [hg_] prefix on
    [hg_matching] / [hg_cover] / [hg_connected] dodges any clash with generic
    mathcomp vocabulary. *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ================================================================= *)
(** ** Shared hypergraph primitives *)

(** A [k]-uniform hyperedge family: every hyperedge has exactly [k] vertices. *)
Definition k_uniform (T : finType) (E : {set {set T}}) (k : nat) : Prop :=
  forall e : {set T}, e \in E -> #|e| = k.

(** ================================================================= *)
(** ** Row 1 — Frankl's union-closed sets conjecture  (OPEN)

    Source: "Conjecture Let F be a finite family of finite sets, not all empty,
    that is closed under taking unions.  Then there exists x such that x is an
    element of at least half the members of F."

    Carrier: the set family [F : {set {set T}}] over a finite vertex type [T]
    (finite sets ↦ finite [T]).  "Closed under taking unions" = [union_closed].
    "Not all empty" is the faithful non-triviality guard [exists2 A, A \in F &
    A != set0] (some member is nonempty; this also forces [F != set0]).  "x in at
    least half the members" = [#|F| <= 2 * #|members of F containing x|]
    (fraction-free). *)

(** A family closed under taking (pairwise, hence finite) unions. *)
Definition union_closed (T : finType) (F : {set {set T}}) : Prop :=
  forall A B : {set T}, A \in F -> B \in F -> (A :|: B) \in F.

(** Corpus row: opg:frankls_union_closed_sets_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/frankls_union_closed_sets_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/frankls_union_closed_sets_conjecture.json
    English statement: (Open Problem Garden, "Frankl's union-closed sets conjecture")
      Let F be a finite family of finite sets, not all empty, that is closed under taking
      unions.  Then some element x belongs to at least half of the members of F.
    Definitions: [union_closed F] - the union of any two members of F is again a member
      (hypergraph-theory/theories/conjectures/U12.v).
    Notes: hypergraphs and set families are modelled as a finite vertex type T together with a
      family of vertex subsets; here the carrier is the family F itself.  "At least half" is
      stated fraction-free as #|F| <= 2 * #|members of F containing x|.  "Not all empty" is the
      guard "some member of F is nonempty", which also forces F to be nonempty; it is
      load-bearing, since the family consisting of the empty set alone is union-closed and no
      element lies in any of its members. *)
Definition frankls_union_closed_sets_statement : Prop :=
  forall (T : finType) (F : {set {set T}}),
    union_closed F ->
    (exists2 A : {set T}, A \in F & A != set0) ->
    exists x : T, #|F| <= 2 * #|[set A in F | x \in A]|.

(** ================================================================= *)
(** ** Row 2 — Turán's problem for 3-uniform hypergraphs  (OPEN)

    Source (primary, K_4^{(3)}-free leg): "Conjecture Every simple 3-uniform
    hypergraph on 3n vertices which contains no complete 3-uniform hypergraph on
    four vertices has at most ½ n²(5n-3) hyperedges."

    Carrier: vertices [T : finType], hyperedges [E : {set {set T}}].  simple +
    3-uniform = [k_uniform E 3] (a [{set {set T}}] family is automatically simple:
    no repeated hyperedges).  "On 3n vertices" = [#|T| = 3 * n].  "Contains no
    complete 3-uniform hypergraph on four vertices" = no 4-set all of whose
    3-subsets are hyperedges = [~ contains_complete E 4 3].  Hyperedge count =
    [#|E|].  The bound ½ n²(5n-3) is stated fraction-free as
    [2 * #|E| <= n^2 * (5*n - 3)].  Guard [0 < n]. *)

(** [S] spans a complete [k]-uniform hypergraph: every [k]-subset of [S] is a
    hyperedge. *)
Definition complete_sub (T : finType) (E : {set {set T}}) (S : {set T}) (k : nat)
  : Prop :=
  forall e : {set T}, e \subset S -> #|e| = k -> e \in E.

(** [E] contains a complete [k]-uniform hypergraph on [m] vertices
    (a copy of K_m^{(k)}). *)
Definition contains_complete (T : finType) (E : {set {set T}}) (m k : nat) : Prop :=
  exists S : {set T}, #|S| = m /\ complete_sub E S k.

(** Corpus row: opg:turans_problem_for_hypergraphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/turans_problem_for_hypergraphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/turans_problem_for_hypergraphs.json
    English statement: (Open Problem Garden, "Turan's problem for hypergraphs")
      For every n at least 1, every simple 3-uniform hypergraph on 3n vertices that contains no
      complete 3-uniform hypergraph on four vertices has at most one half of n squared times
      (5n-3) hyperedges.
    Definitions: [k_uniform E k] - every hyperedge of E has exactly k vertices
      (hypergraph-theory/theories/conjectures/U12.v); [complete_sub E S k] - every k-element
      subset of S is a hyperedge of E (same file); [contains_complete E m k] - some m-element
      vertex set spans a complete k-uniform hypergraph inside E (same file).
    Notes: a hyperedge family is a [{set {set T}}], so simplicity (no repeated hyperedge) holds
      by construction.  The bound is stated fraction-free as 2 * #|E| <= n^2 * (5n - 3), and the
      guard [0 < n] keeps 5n - 3 out of natural truncation.  PARTIAL COVERAGE: the corpus row
      carries TWO conjectures - the one above and "every simple 3-uniform hypergraph on 2n
      vertices with no complete 3-uniform hypergraph on five vertices has at most n^2(n-1)
      hyperedges" - and only the first is formalised here (see
      meta/STATEMENT_IMPROVEMENTS.md). *)
Definition turans_problem_for_hypergraphs_statement : Prop :=
  forall (n : nat) (T : finType) (E : {set {set T}}),
    0 < n ->
    k_uniform E 3 ->
    #|T| = 3 * n ->
    ~ contains_complete E 4 3 ->
    2 * #|E| <= n ^ 2 * (5 * n - 3).

(** ================================================================= *)
(** ** Row 3 — Are critical k-forests tight?  (OPEN)

    Source: "Conjecture Let H be a k-uniform hypergraph.  If H is a critical
    k-forest, then it is a k-tree."

    Carrier: vertices [T : finType], hyperedges [E : {set {set T}}], with [E]
    [k]-uniform.  Hypergraph acyclicity is Berge-acyclicity ([berge_acyclic]):
    no Berge cycle (distinct vertices [v_i] and distinct hyperedges [e_i],
    [t >= 2], with [v_i ∈ e_i ∩ e_{i+1}] cyclically).  A [k]-forest is a
    [k]-uniform Berge-acyclic family; a [k]-tree is a connected [k]-forest
    ([hg_connected]: every two hyperedges are joined by an intersection-path of
    hyperedges).  "Critical" is read as forest-maximality: no new [k]-hyperedge
    can be added while staying Berge-acyclic.  The conjecture then asks whether a
    maximal [k]-forest is forced to be connected (a single [k]-tree).  Guards
    [0 < k] and the non-triviality requirement [E != set0] (the forest has at
    least one hyperedge — without it the empty family [E = set0] over a carrier
    with [#|T| < k] vacuously satisfies [critical_k_forest] yet fails [k_tree],
    refuting the statement; [E != set0] together with [k]-uniformity also forces
    [k <= #|T|]). *)

(** A Berge cycle of [E]: distinct vertices [vs] and distinct hyperedges [es]
    of common length [t >= 2], with [v_i ∈ e_i] and [v_i ∈ e_{i+1}] (cyclically,
    via [rot 1 es]) — each [v_i] links two consecutive hyperedges. *)
Definition berge_cycle (T : finType) (E : {set {set T}}) : Prop :=
  exists (vs : seq T) (es : seq {set T}),
    [/\ 2 <= size es,
        size vs = size es,
        uniq vs && uniq es,
        (forall e : {set T}, e \in es -> e \in E)
      & all (fun t : T * ({set T} * {set T}) =>
               let: (v, ef) := t in (v \in ef.1) && (v \in ef.2))
            (zip vs (zip es (rot 1 es)))].

(** Berge-acyclic = no Berge cycle. *)
Definition berge_acyclic (T : finType) (E : {set {set T}}) : Prop :=
  ~ berge_cycle E.

(** Connected hypergraph: nonempty, and any two hyperedges are joined by a path
    of hyperedges with consecutive members intersecting (Berge-connectivity). *)
Definition hg_connected (T : finType) (E : {set {set T}}) : Prop :=
  E != set0 /\
  forall e f : {set T}, e \in E -> f \in E ->
    exists p : seq {set T},
      [/\ path (fun a b => a :&: b != set0) e p,
          last e p = f
        & all (fun a => a \in E) p].

(** A [k]-forest: a [k]-uniform Berge-acyclic hyperedge family. *)
Definition k_forest (T : finType) (E : {set {set T}}) (k : nat) : Prop :=
  k_uniform E k /\ berge_acyclic E.

(** A [k]-tree: a connected [k]-forest. *)
Definition k_tree (T : finType) (E : {set {set T}}) (k : nat) : Prop :=
  k_forest E k /\ hg_connected E.

(** A critical [k]-forest: a [k]-forest that is maximal Berge-acyclic — adjoining
    any further [k]-hyperedge creates a Berge cycle. *)
Definition critical_k_forest (T : finType) (E : {set {set T}}) (k : nat) : Prop :=
  k_forest E k /\
  (forall e : {set T}, #|e| = k -> e \notin E -> berge_cycle (e |: E)).

(** Corpus row: opg:are_critical_k_forests_tight
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/are_critical_k_forests_tight/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/are_critical_k_forests_tight.json
    English statement: (Open Problem Garden, "Are critical k-forests tight?")
      For every k at least 1, every k-uniform hypergraph with at least one hyperedge that is a
      critical k-forest is a k-tree.
    Definitions: [k_uniform E k] - every hyperedge has exactly k vertices
      (hypergraph-theory/theories/conjectures/U12.v); [berge_cycle E] - there are t at least 2
      pairwise distinct vertices and t pairwise distinct hyperedges of E, arranged cyclically,
      with the i-th vertex lying in both the i-th and the (i+1)-st hyperedge (same file);
      [berge_acyclic E] - E has no Berge cycle (same file); [hg_connected E] - E is nonempty and
      any two of its hyperedges are joined by a chain of hyperedges of E with consecutive
      members intersecting (same file); [k_forest E k] - E is k-uniform and Berge-acyclic (same
      file); [k_tree E k] - a connected k-forest (same file); [critical_k_forest E k] - a
      k-forest to which no further k-element hyperedge can be added without creating a Berge
      cycle (same file).
    Notes: hypergraph acyclicity is read as Berge-acyclicity and "critical" as maximality among
      Berge-acyclic k-uniform families, so the conjecture becomes "a maximal k-forest is
      connected".  The guards are load-bearing: without [E != set0] the empty family over a
      carrier with fewer than k vertices vacuously satisfies [critical_k_forest] yet is not a
      k-tree, which would refute the statement; [E != set0] together with k-uniformity also
      forces k <= #|T|. *)
Definition are_critical_k_forests_tight_statement : Prop :=
  forall (k : nat) (T : finType) (E : {set {set T}}),
    0 < k ->
    E != set0 ->
    critical_k_forest E k ->
    k_tree E k.

(** ================================================================= *)
(** ** Row 4 — Ryser's conjecture  (OPEN)

    Source: "Conjecture Let H be an r-uniform r-partite hypergraph.  If ν is the
    maximum number of pairwise disjoint edges in H, and τ is the size of the
    smallest set of vertices which meets every edge, then τ ≤ (r-1)ν."

    Carrier: vertices [T : finType] with an r-part assignment [part : T -> 'I_r]
    (the r colour classes), hyperedges [E : {set {set T}}].  r-uniform r-partite =
    [r_partite_uniform part E r]: every hyperedge meets each of the [r] parts in
    exactly one vertex (so [|e| = r], one vertex per part).  ν (matching-number) =
    [is_matching_number E ν]: max size of a family of pairwise-disjoint hyperedges.
    τ (cover-number) = [is_cover_number E τ]: min size of a vertex set meeting
    every hyperedge.  Guard [1 < r] (i.e. [2 <= r]): this is the faithful domain
    of Ryser's conjecture.  At [r = 1] the bound degenerates to [τ <= 0] while
    [τ = ν > 0] whenever an edge exists, so [r = 1] would make the statement
    refutable rather than open; [r = 2] is König's theorem, [r = 3] is Aharoni's
    theorem, and the problem is open for [r >= 4].  ([1 < r] also keeps ['I_r]
    inhabited and makes [r - 1] the intended predecessor.) *)

(** r-uniform r-partite: every hyperedge has exactly one vertex in each part [j]. *)
Definition r_partite_uniform (T : finType) (r : nat) (part : T -> 'I_r)
  (E : {set {set T}}) : Prop :=
  forall e : {set T}, e \in E ->
    forall j : 'I_r, #|[set v in e | part v == j]| = 1.

(** A matching: a subfamily of pairwise-disjoint hyperedges. *)
Definition hg_matching (T : finType) (M E : {set {set T}}) : Prop :=
  M \subset E /\
  {in M &, forall e f : {set T}, e != f -> [disjoint e & f]}.

(** [nu] is the matching number ν(H): the maximum size of a matching. *)
Definition is_matching_number (T : finType) (E : {set {set T}}) (nu : nat) : Prop :=
  (exists M : {set {set T}}, hg_matching M E /\ #|M| = nu) /\
  (forall M : {set {set T}}, hg_matching M E -> #|M| <= nu).

(** A vertex cover: a vertex set meeting every hyperedge. *)
Definition hg_cover (T : finType) (X : {set T}) (E : {set {set T}}) : Prop :=
  forall e : {set T}, e \in E -> X :&: e != set0.

(** [tau] is the cover number τ(H): the minimum size of a vertex cover. *)
Definition is_cover_number (T : finType) (E : {set {set T}}) (tau : nat) : Prop :=
  (exists X : {set T}, hg_cover X E /\ #|X| = tau) /\
  (forall X : {set T}, hg_cover X E -> tau <= #|X|).

(** Corpus row: opg:rysers_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/rysers_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/rysers_conjecture.json
    English statement: (Open Problem Garden, "Ryser's conjecture")
      Let r be at least 2 and let H be an r-uniform r-partite hypergraph.  If nu is the maximum
      number of pairwise disjoint hyperedges of H and tau is the size of the smallest vertex set
      meeting every hyperedge, then tau is at most (r-1) times nu.
    Definitions: [r_partite_uniform part E] - every hyperedge meets each of the r parts, given
      by the vertex map part, in exactly one vertex, so it has exactly r vertices
      (hypergraph-theory/theories/conjectures/U12.v); [hg_matching M E] - M is a subfamily of E
      whose hyperedges are pairwise disjoint (same file); [is_matching_number E nu] - nu is
      attained by some matching and bounds the size of every matching (same file);
      [hg_cover X E] - the vertex set X meets every hyperedge (same file);
      [is_cover_number E tau] - tau is attained by some cover and is a lower bound for the size
      of every cover (same file).
    Notes: r-uniformity is not a separate hypothesis; it follows from meeting each of the r
      parts exactly once.  Both nu and tau are introduced as universally quantified numbers
      characterised by an "attained and extremal" pair, so no minimum or maximum operator is
      needed.  The guard [1 < r] is the faithful domain of Ryser's conjecture: at r = 1 the
      bound degenerates to tau <= 0 while tau = nu > 0 as soon as a hyperedge exists, which
      would make the row refutable instead of open.  r = 2 is Koenig's theorem, r = 3 is
      Aharoni's theorem, and the problem is open for r at least 4. *)
Definition rysers_statement : Prop :=
  forall (r : nat) (T : finType) (part : T -> 'I_r) (E : {set {set T}})
         (nu tau : nat),
    1 < r ->
    r_partite_uniform part E ->
    is_matching_number E nu ->
    is_cover_number E tau ->
    tau <= (r - 1) * nu.

(** * Minor.conjectures.X175 -- v2 clique count without K_t subdivision row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X175 vocabulary ***********************************************)

Definition x175_clique_count (G : sgraph) : nat :=
  #|[set S : {set G} | cliqueb S && (S != set0)]|.

Definition x175_path_internal {G : sgraph} (x y : G) (p : seq G) : {set G} :=
  [set z : G | (z \in x :: p) && (z != x) && (z != y)].

Definition x175_simple_path_between {G : sgraph} (x y : G) (p : seq G) : Prop :=
  [/\ uniq (x :: p), path (--) x p & last x p = y].

(** A subdivision of [K_t] in [G]: injective branch vertices, and internally
    vertex-disjoint simple paths between every branch pair. *)
Definition x175_Kt_subdivision (G : sgraph) (t : nat) : Prop :=
  exists branch : 'I_t -> G,
    injective branch /\
    exists route : 'I_t -> 'I_t -> seq G,
      [/\ (forall i j : 'I_t,
             i < j -> x175_simple_path_between (branch i) (branch j) (route i j)),
          (forall i j k : 'I_t,
             i < j ->
             branch k \notin x175_path_internal (branch i) (branch j) (route i j)) &
          forall i j i' j' : 'I_t,
             i < j -> i' < j' -> (i != i') || (j != j') ->
             [disjoint x175_path_internal (branch i) (branch j) (route i j) &
                       x175_path_internal (branch i') (branch j') (route i' j')]].

(** [3^(2t/3+o(t)) n] as the standard rational-epsilon eventual upper
    envelope.  For epsilon [a/b], raising to the positive power [3b] gives the
    finite integer inequality
    [cliques^(3b) <= 3^((2b+3a)t) * n^(3b)]. *)
Definition x175_subdivision_clique_asymptotic_bound
    (a b t n cliques : nat) : Prop :=
  cliques ^ (3 * b) <= (3 ^ ((2 * b + 3 * a) * t)) * (n ^ (3 * b)).

(** ** X175 statements *****************************************************)

(** Corpus row: arxiv:1606.06810#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1606.06810__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1606.06810__01.json
    English statement: (Fox and Wei 2018, conjecture in "On the number of cliques in graphs
      with a forbidden subdivision or immersion")
      For every positive rational number written as a over b, for all sufficiently large t,
      every finite simple graph G containing no subdivision of the complete graph on t
      vertices has at most 3 raised to the power (2/3 + a/b) times t, times the number of
      vertices of G, nonempty cliques.
    Definitions: [x175_clique_count G] - the number of nonempty cliques of G
      (minor-theory/theories/conjectures/X175.v); [x175_simple_path_between x y p] - p extends
      x to a path of pairwise distinct vertices ending at y (same file);
      [x175_path_internal x y p] - the internal vertices of that path (same file);
      [x175_Kt_subdivision G t] - G contains a subdivision of the complete graph on t
      vertices: t injectively chosen branch vertices, joined pairwise by simple paths whose
      interiors avoid all branch vertices and are pairwise disjoint (same file);
      [x175_subdivision_clique_asymptotic_bound a b t n cliques] - the cross-multiplied
      inequality cliques^(3b) <= 3^((2b+3a)t) * n^(3b) (same file); [eventually P] - P holds
      for all sufficiently large arguments (base/theories/asymptotics.v).
    Notes: the conjectured value 3^(2t/3+o(t)) n is an exact asymptotic; only the upper
      envelope is stated here, the matching lower-bound construction being source context.
      The o(t) term is realised in the standard finite way: for every positive rational
      epsilon = a/b the bound with exponent (2/3 + epsilon)t holds for all large enough t.
      Raising to the power 3b clears the denominators, since (2/3 + a/b) * 3b = 2b + 3a.
      Unlike X174, this row counts only NONEMPTY cliques. *)
Definition kt_subdivision_clique_count_asymptotic_statement : Prop :=
  forall a b : nat,
    0 < a -> 0 < b ->
    eventually (fun t =>
      forall G : sgraph,
        ~ x175_Kt_subdivision G t ->
        x175_subdivision_clique_asymptotic_bound
          a b t #|G| (x175_clique_count G)).

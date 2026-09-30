(** * GTMisc.conjectures.X20 -- v2 burning and monochromatic-component rows *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X20 vocabulary ************************************************)

Fixpoint x20_ball (G : sgraph) (r : nat) (x : G) : {set G} :=
  if r is r'.+1 then x20_ball r' x :|: \bigcup_(z in x20_ball r' x) N(z)
  else [set x].

Definition x20_ceil_sqrt (n t : nat) : Prop :=
  n <= t ^ 2 /\ forall s : nat, n <= s ^ 2 -> t <= s.

Definition x20_burning_cover (G : sgraph) (t : nat) : Prop :=
  exists c : 'I_t -> G,
    forall v : G, exists i : 'I_t,
      v \in x20_ball (t.-1 - val i) (c i).

Definition x20_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

Definition x20_colour_rel
    (G : sgraph) (k : nat) (col : {set G} -> 'I_k) (i : 'I_k) : rel G :=
  fun u v => (u -- v) && (col [set u; v] == i).

Definition x20_monochromatic_connected_set
    (G : sgraph) (k : nat) (col : {set G} -> 'I_k) (i : 'I_k)
    (S : {set G}) : Prop :=
  S != set0 /\
  forall u v : G, u \in S -> v \in S ->
    connect (x20_colour_rel col i) u v.

(** ** X20 statements ******************************************************)

(** Corpus row: studies:std_burning_number_conjecture
    Site: none
    Review: none
    English statement: (Bonato, Janssen and Roshanbin, burning number conjecture)
      For every non-empty connected finite simple graph G, if t is the least integer with
      |V(G)| <= t^2, then there are vertices c_0, ..., c_(t-1) such that every vertex of G lies
      within distance t-1-i of c_i for some i; that is, the burning number of G is at most
      ceil(sqrt |V(G)|).
    Definitions: [x20_ball r x] - the closed r-ball around x (this file);
      [x20_ceil_sqrt n t] - t is the least integer with n <= t^2, i.e. t = ceil(sqrt n) (this
      file); [x20_burning_cover G t] - a burning sequence of length t: a map from the t rounds
      to vertices such that every vertex is covered by the ball of radius t-1-i around the
      i-th chosen vertex (this file); [connected] - coq-graph-theory.
    Notes: the burning number is rendered by its covering characterization (a graph burns in t
      rounds exactly when such a sequence exists) rather than by a round-by-round fire
      process, which is the standard equivalent definition.  The ceiling of the square root is
      characterized relationally by [x20_ceil_sqrt] and passed in as a parameter. *)
Definition burning_number_conjecture_statement : Prop :=
  forall (G : sgraph) (t : nat),
    0 < #|G| ->
    connected [set: G] ->
    x20_ceil_sqrt #|G| t ->
    x20_burning_cover G t.

(** Corpus row: studies:std_gy_rf_s_s_rk_zy_monochromatic_component_conjectu
    Site: none
    Review: none
    English statement: (Gyarfas and Sarkozy, monochromatic component conjecture)
      For every k >= 3, every finite simple graph G and every colouring of the edges of G with
      k colours, if every vertex v satisfies k^2 * deg(v) >= (k^2 - (k-1)) * |V(G)| - the
      fraction-free form of minimum degree at least (1 - (k-1)/k^2) * n - then some colour i
      and some non-empty vertex set S are such that all pairs of S are connected inside the
      colour-i subgraph and |V(G)| <= (k-1) * |S|, i.e. |S| >= n/(k-1).
    Definitions: [x20_edge_set G] - the edges of G as two-element vertex sets (this file);
      [x20_colour_rel col i] - the adjacency relation of the colour-i subgraph (this file);
      [x20_monochromatic_connected_set col i S] - S is non-empty and any two of its vertices
      are joined by a colour-i path (this file); [connect] - reflexive transitive closure of a
      relation (MathComp).
    Notes: both inequalities of the source are cross-multiplied over naturals.  The
      monochromatic component is rendered as a set all of whose pairs are connected in the
      colour class rather than as a maximal connected component, which is enough for the
      order lower bound.  Edge colourings are given as maps from vertex pairs, so the colour of
      a non-edge is irrelevant. *)
Definition gyarfas_sarkozy_monochromatic_component_statement : Prop :=
  forall (k : nat) (G : sgraph) (col : {set G} -> 'I_k),
    3 <= k ->
    (forall v : G, k ^ 2 * #|N(v)| >= (k ^ 2 - (k - 1)) * #|G|)%N ->
    exists (i : 'I_k) (S : {set G}),
      x20_monochromatic_connected_set col i S /\
      (#|G| <= (k - 1) * #|S|)%N.

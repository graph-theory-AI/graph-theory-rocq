(** * Extremal.conjectures.X115 -- v2 Chvatal-Tuza odd induced cycles row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X115 vocabulary ***********************************************)

(** Internal adjacency of a vertex set: an edge of [G] both of whose ends lie
    in [S].  Reachability under this relation is connectedness of the induced
    subgraph [G[S]] using only [S]-internal edges. *)
Definition x115_scycle_rel (G : sgraph) (S : {set G}) : rel G :=
  fun x y => [&& x \in S, y \in S & x -- y].

Definition x115_connected (G : sgraph) (S : {set G}) : bool :=
  [forall x in S, [forall y in S, connect (x115_scycle_rel S) x y]].

(** Every vertex of [S] has exactly two neighbours inside [S], i.e. the induced
    subgraph [G[S]] is 2-regular. *)
Definition x115_two_regular (G : sgraph) (S : {set G}) : bool :=
  [forall x in S, #|N(x) :&: S| == 2].

(** [G[S]] is an induced cycle iff [S] has at least 3 vertices, is 2-regular,
    and is connected; it is *odd* when [#|S|] is odd.  A 2-regular connected
    graph on >= 3 vertices is exactly a cycle. *)
Definition x115_odd_induced_cycle (G : sgraph) (S : {set G}) : bool :=
  [&& 3 <= #|S|, odd #|S|, x115_two_regular S & x115_connected S].

Definition x115_count (G : sgraph) : nat :=
  #|[set S : {set G} | x115_odd_induced_cycle S]|.

(** Corpus row: studies:std_chv_tal_tuza_conjecture_on_maximum_odd_induced_c
    Site: none
    Review: none
    English statement: (Chvatal and Tuza 1988, "Chvatal-Tuza conjecture on maximum odd induced cycles")
      There are constants Cu, Cl > 0 and a threshold N such that for every n >= N: every graph
      G on n vertices has at most Cu * 3^n odd induced cycles cubed (count^3 <= Cu * 3^n), and
      some graph on n vertices attains 3^n <= Cl * count^3; that is, the maximum number of odd
      induced cycles on n vertices is of order 3^(n/3).
    Definitions: [x115_scycle_rel G S] - adjacency of G restricted to both ends inside S (X115.v);
      [x115_connected G S] - every two vertices of S are joined using only S-internal edges
      (X115.v); [x115_two_regular G S] - every vertex of S has exactly two neighbours inside S
      (X115.v); [x115_odd_induced_cycle G S] - S has at least 3 vertices, odd size, is
      2-regular and connected, which characterises an induced odd cycle (X115.v);
      [x115_count G] - the number of such vertex sets (X115.v).
    Notes: this row comes from the studies slice of the corpus, which has no site or review page,
      and is recorded as PARTIAL (a disclosed PROXY). The source's literal "is 3^(n/3)" is
      ill-posed over the naturals (3^(n/3) is irrational unless 3 divides n) and machine-refuted
      (K_6 already has at least 20 odd induced cycles, and 20^3 = 8000 > 729 = 3^6); the sharp
      asymptotic is also false (Morrison-Scott, arXiv:1603.02960, Theorem 1.6, which gives the
      maximum up to an O(n) additive term when n = 3 mod 6 and up to a constant factor
      otherwise, for n large). The body therefore encodes the resolved form, a two-sided
      constant-factor bound with a threshold, cubed to stay integral. This is strictly weaker
      than the literal source text (ledger). *)
Definition chvatal_tuza_max_odd_induced_cycles_statement : Prop :=
  exists Cu Cl N : nat,
    [/\ 0 < Cu, 0 < Cl,
        forall (n : nat) (G : sgraph),
          N <= n -> #|G| = n -> (x115_count G) ^ 3 <= Cu * 3 ^ n
      & forall n : nat,
          N <= n ->
          exists G : sgraph, #|G| = n /\ 3 ^ n <= Cl * (x115_count G) ^ 3].

(** * GTMisc.conjectures.XE1 -- Erdős open clean rows *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition xe1_coprime_adj (n : nat) (x y : 'I_n) : bool :=
  (x != y) && coprime (val x).+1 (val y).+1.

Definition xe1_rel_cycle (V : finType) (r : rel V) (c : seq V) : Prop :=
  ucycle r c /\ 2 < size c.

Definition xe1_all_small_odd_coprime_cycles (n : nat) (A : {set 'I_n}) : Prop :=
  forall ell : nat,
    odd ell -> 3 <= ell -> ell <= n %/ 3 + 1 ->
    exists c : seq 'I_n,
      xe1_rel_cycle (@xe1_coprime_adj n) c /\
      size c = ell /\
      forall x : 'I_n, x \in c -> x \in A.

Definition xe1_complete_tripartite_1_l_l (n ell : nat) (A : {set 'I_n}) : Prop :=
  exists X Y Z : {set 'I_n},
    X \subset A /\
    Y \subset A /\
    Z \subset A /\
    [disjoint X & Y] /\
    [disjoint X :|: Y & Z] /\
    #|X| = 1 /\
    #|Y| = ell /\
    #|Z| = ell /\
    forall x y : 'I_n,
      ((x \in X) && (y \in Y :|: Z) ||
       (x \in Y) && (y \in X :|: Z) ||
       (x \in Z) && (y \in X :|: Y)) ->
      xe1_coprime_adj x y.

(** Corpus row: erdos:883
    Site: none
    Review: none
    English statement: (Erdos problem #883)
      Two claims about the coprimality graph on {1, ..., n}, whose vertices are joined when
      they are coprime.  First, every subset A of size more than floor(n/2) + floor(n/3) -
      floor(n/6) contains, for every odd l with 3 <= l <= floor(n/3) + 1, a cycle on exactly l
      vertices of A in that graph.  Second, for every l >= 1 and every sufficiently large n,
      every such subset A contains a complete tripartite subgraph with parts of sizes 1, l and
      l, on 2l+1 vertices, all of whose cross pairs are coprime.
    Definitions: [xe1_coprime_adj] - distinct indices of {0, ..., n-1} whose successors, i.e.
      the integers 1 to n, are coprime (this file); [xe1_rel_cycle r c] - a uniform closed
      r-walk on more than two vertices, the same cycle notion as in the girth vocabulary (this
      file); [xe1_all_small_odd_coprime_cycles A] - the first claim above for a given A (this
      file); [xe1_complete_tripartite_1_l_l n l A] - three disjoint subsets of A of sizes 1, l,
      l with every cross pair coprime (this file); [ucycle], [coprime] - MathComp.
    Notes: the bound n/3 + 1 on the cycle length is rendered by integer division, [n %/ 3 + 1],
      and the cardinality threshold likewise by integer divisions, matching the floors of the
      source.  Vertices are the indices 0 to n-1 and represent the integers 1 to n through the
      successor, so coprimality is taken of val+1.  The corpus row asks two questions; the
      Rocq body is the conjunction of their positive answers. *)
Definition erdos_883_statement : Prop :=
  (forall n : nat, forall A : {set 'I_n},
      #|A| > n %/ 2 + n %/ 3 - n %/ 6 ->
      xe1_all_small_odd_coprime_cycles A) /\
  (forall ell : nat, 1 <= ell ->
      exists N : nat,
        forall n : nat, N <= n ->
        forall A : {set 'I_n},
          #|A| > n %/ 2 + n %/ 3 - n %/ 6 ->
          xe1_complete_tripartite_1_l_l ell A).

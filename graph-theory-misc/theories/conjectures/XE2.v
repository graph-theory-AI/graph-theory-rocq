(** * GTMisc.conjectures.XE2 -- Erdős solved clean rows *)

From GTMisc.conjectures Require Import XE1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition xe2_subgraph_of (H G : sgraph) : Prop :=
  exists f : H -> G, injective f /\ forall x y : H, x -- y -> f x -- f y.

Definition xe2_triangle_free_rel (V : finType) (r : rel V) : Prop :=
  forall x y z : V, r x y -> r y z -> r z x -> False.

Definition xe2_independent3 (V : finType) (r : rel V) (a b c : V) : Prop :=
  a != b /\ a != c /\ b != c /\ ~~ r a b /\ ~~ r a c /\ ~~ r b c.

(** Corpus row: erdos:715
    Site: none
    Review: none
    English statement: (Erdos problem #715)
      Two claims.  First, every non-empty 4-regular finite simple graph contains a non-empty
      3-regular subgraph.  Second, there is an r > 3 such that every non-empty r-regular finite
      simple graph contains a non-empty 3-regular subgraph.
    Definitions: [xe2_subgraph_of H G] - there is an injective edge-preserving map from H to G,
      i.e. G contains a copy of H, not necessarily induced (this file); [regular G d] - every
      vertex of G has degree d (GTBase).
    Notes: the guard r > 3 in the second claim is load-bearing: at r = 3 the host graph is
      itself a 3-regular subgraph (take H := G), so the question is non-trivial only for
      r > 3, the first claim being the case r = 4.  Both claims carry the non-emptiness guards
      [0 < #|G|] and [0 < #|H|], without which the empty graph would answer trivially.  The
      corpus status of the row is solved. *)
Definition erdos_715_statement : Prop :=
  (forall G : sgraph, 0 < #|G| -> regular G 4 ->
      exists H : sgraph, 0 < #|H| /\ xe2_subgraph_of H G /\ regular H 3) /\
  (exists r : nat, 3 < r /\
      forall G : sgraph, 0 < #|G| -> regular G r ->
        exists H : sgraph, 0 < #|H| /\ xe2_subgraph_of H G /\ regular H 3).

(** Corpus row: erdos:895
    Site: none
    Review: none
    English statement: (Erdos problem #895)
      There is an N such that for every n >= N and every triangle-free simple graph on
      {1, ..., n} there are three pairwise non-adjacent and pairwise distinct vertices a, b, c
      with a + b = c.
    Definitions: [xe2_triangle_free_rel r] - no three vertices are pairwise related (this
      file); [xe2_independent3 r a b c] - the three vertices are pairwise distinct and pairwise
      non-adjacent (this file).
    Notes: the graph is given as a symmetric irreflexive relation on the index type of size n,
      the index i standing for the integer i+1, so the arithmetic condition is written on the
      successors.  "For all sufficiently large n" is rendered by an explicit threshold N chosen
      before n.  The corpus status of the row is solved. *)
Definition erdos_895_statement : Prop :=
  exists N : nat,
    forall n : nat, N <= n ->
    forall r : rel 'I_n,
      symmetric r -> irreflexive r -> xe2_triangle_free_rel r ->
      exists a b c : 'I_n,
        (val a).+1 + (val b).+1 = (val c).+1 /\
        xe2_independent3 r a b c.

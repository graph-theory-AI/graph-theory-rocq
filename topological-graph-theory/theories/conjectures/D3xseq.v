(** * D3 crossing-sequences row via the genus crossing-number layer. *)

From GTBase Require Export base.
From Topological.foundations Require Import embedding crossing crossing_genus.

Set Implicit Arguments.
Unset Strict Implicit.

(** Corpus row: opg:crossing_sequences
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/crossing_sequences/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/crossing_sequences.json
    English statement: (Open Problem Garden, "Crossing sequences")
      Corpus claim: for every sequence (a_0, a_1, ..., 0) of non-negative integers that
      strictly decreases until it reaches 0, there is a graph that can be drawn on the
      surface of orientable (respectively non-orientable) genus i with a_i crossings but not
      with fewer.  Back-translation of the Rocq body: for every non-empty list a of naturals
      whose consecutive entries strictly decrease and whose last entry is 0, there is a
      CONNECTED finite simple graph G such that for every index i below the length of a, the
      genus-i crossing number of G is a_i, i.e. a_i crossing splits land G in orientable
      genus i and no fewer do.
    Definitions: [is_crossing_genus G i n] - n is the least number of crossing splits after
      which G embeds with Euler genus at most i
      (topological-graph-theory/theories/foundations/crossing_genus.v, built on
      [crossing.xsplit] and on [embeds_in_genus]/[euler_genus] of
      topological-graph-theory/theories/foundations/embedding.v); [connected] - coq-graph-
      theory connectivity, here on the full vertex set.
    Notes: PARTIAL PROXY, orientable half only.  (1) The witness is required to be CONNECTED
      and this is load-bearing: [euler_genus] is the connected-map Euler relation, exact on
      connected maps and understating on disconnected ones, and [xsplit] preserves
      connectivity (machine-checked, [crossing_genus.xsplit_connected]), so every split
      target of a connected witness stays connected and the Euler-genus side is exact.
      (2) Equality with the usual drawing genus-crossing number is still not validated,
      because the inherited [xsplit] model carries no local rotation/alternation data at
      crossing vertices.  (3) SCOPE: only the ORIENTABLE variant is formalized; the source's
      non-orientable "(resp.)" twin would be the analogous statement over
      [signed_embedding.semb_in_genus] and is not built here.  (4) The non-increasing shape
      that the source presupposes is a THEOREM here, not a hypothesis
      ([is_crossing_genus_nonincreasing]). *)
Definition crossing_sequences_statement : Prop :=
  forall a : seq nat,
    0 < size a ->
    (forall j : nat, j.+1 < size a -> nth 0 a j.+1 < nth 0 a j) ->
    nth 0 a (size a).-1 = 0 ->
    exists G : sgraph,
      connected [set: G] /\
      forall i : nat, i < size a -> is_crossing_genus G i (nth 0 a i).

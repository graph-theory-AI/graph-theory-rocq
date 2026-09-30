(** * Cycle.conjectures.X184 -- v2 antisymmetric Z5-flow row *)

From GraphTheory Require Import mgraph.
From GTBase Require Import base.
From Cycle.conjectures Require Import D1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X184 vocabulary ***********************************************)

Definition x184_out_cut (G : mgraph) (S : {set G}) : {set edge G} :=
  [set e : edge G | (source e \in S) && (target e \notin S)].

Definition x184_directed_k_edge_connected (G : mgraph) (k : nat) : Prop :=
  forall S : {set G},
    S != set0 -> S != [set: G] -> k <= #|x184_out_cut S|.

Definition x184_z5_antisymmetric_flow (G : mgraph) : Prop :=
  exists phi : edge G -> 'I_5,
    (forall e : edge G, phi e != ord0) /\
    forall v : G,
      ((\sum_(e : edge G | source e == v) val (phi e)) %% 5 =
       (\sum_(e : edge G | target e == v) val (phi e)) %% 5).

(** ** X184 statements *****************************************************)

(** Corpus row: arxiv:1701.03366#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1701.03366__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1701.03366__00.json
    English statement: (Esperet, de Joannis de Verclos, Le, Thomasse 2018, "Antisymmetric
      variant of Jaeger's weak 3-flow conjecture" of "Additive bases and flows in graphs")
      There is a natural number k such that every multigraph G whose intrinsic orientation
      is k-edge-connected in the directed sense, every vertex set other than the empty set
      and the full set having at least k edges leaving it, carries a map phi from the edges
      of G to the integers modulo 5 that never takes the value 0 and satisfies, at every
      vertex v, that the sum modulo 5 of the values on the edges with source v equals the
      sum modulo 5 of the values on the edges with target v.
    Definitions: [x184_out_cut S] - the edges with source in S and target outside S
      (X184.v); [x184_directed_k_edge_connected G k] - every vertex set other than the
      empty set and the whole vertex set has at least k out-edges (X184.v);
      [x184_z5_antisymmetric_flow G] - a nowhere-zero map to the integers modulo 5 whose
      sums modulo 5 balance at every vertex (X184.v).
    Notes: UNFAITHFUL, recorded by the faithfulness audit of 2026-07-17
      (meta/BLOCKED_RETARGETING_AUDIT.md, corpus verification_note): the defining
      ANTISYMMETRY property is absent from [x184_z5_antisymmetric_flow], which is exactly a
      nowhere-zero flow over the integers modulo 5 with the conservation written
      modulo 5. A Nesetril-Raspaud antisymmetric flow additionally requires the set B of
      used values to satisfy that B and the set of negatives of B are disjoint, so the
      Rocq body is a strictly weaker object than the conjectured one and the row is a
      proxy. *)
Definition z5_antisymmetric_flow_edge_connectivity_statement : Prop :=
  exists k : nat,
    forall G : mgraph,
      x184_directed_k_edge_connected G k ->
      x184_z5_antisymmetric_flow G.

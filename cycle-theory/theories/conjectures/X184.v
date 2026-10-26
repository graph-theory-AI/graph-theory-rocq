(** * Cycle.conjectures.X184 -- v2 antisymmetric Z5-flow row *)

From GraphTheory Require Import mgraph.
From GTBase Require Import base.
From Cycle.conjectures Require Import D1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X184 vocabulary ***********************************************)

(** Directed edge-connectivity: every proper nonempty set has at least [k] edges LEAVING it.  Not the
    source's notion (it calls a digraph k-edge-connected when its underlying graph is), so the statement
    no longer uses it (2026-10-26); the two definitions stay, byte-identical, as the excluded distinct
    variants that the simple_cuts migration spec records. *)
Definition x184_out_cut (G : mgraph) (S : {set G}) : {set edge G} :=
  [set e : edge G | (source e \in S) && (target e \notin S)].

Definition x184_directed_k_edge_connected (G : mgraph) (k : nat) : Prop :=
  forall S : {set G},
    S != set0 -> S != [set: G] -> k <= #|x184_out_cut S|.

(** A Z5-antisymmetric flow (Nesetril-Raspaud): a nowhere-zero Z5-flow whose
    set B of used values satisfies B /\ -B = empty, i.e. no two edges (equal or
    not) carry values summing to 0 modulo 5. *)
Definition x184_z5_antisymmetric_flow (G : mgraph) : Prop :=
  exists phi : edge G -> 'I_5,
    [/\ forall e : edge G, phi e != ord0,
        forall e e' : edge G, (val (phi e) + val (phi e')) %% 5 != 0
      & forall v : G,
          ((\sum_(e : edge G | source e == v) val (phi e)) %% 5 =
           (\sum_(e : edge G | target e == v) val (phi e)) %% 5)].

(** ** X184 statements *****************************************************)

(** Corpus row: arxiv:1701.03366#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1701.03366__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1701.03366__00.json
    English statement: (Esperet, de Joannis de Verclos, Le, Thomasse 2018, "Antisymmetric
      variant of Jaeger's weak 3-flow conjecture" of "Additive bases and flows in graphs")
      There is a natural number k such that every multigraph G, with its edges oriented
      from source to target, whose underlying graph is k-edge-connected (deleting fewer than
      k edges leaves it connected), carries a map phi from the edges of G to the integers
      modulo 5 that never takes the value 0, never takes two opposite values (no two edges,
      equal or not, have values summing to 0 modulo 5), and satisfies, at every vertex v,
      that the sum modulo 5 of the values on the edges with source v equals the sum modulo
      5 of the values on the edges with target v.
    Definitions: [edge_connected G k] - deleting fewer than k edges leaves an undirected walk
      between any two vertices (cycle-theory/theories/foundations/connectivity.v);
      [x184_z5_antisymmetric_flow G] - a nowhere-zero map to the integers modulo 5, no two
      of whose values are opposite, whose sums modulo 5 balance at every vertex (X184.v).
    Notes: RE-ENCODED 2026-10-26 (coordination/PROGRAMME.md, A1; Marc's decision 3 of 25
      October): the source calls a digraph t-edge-connected when its underlying graph is
      (p. 4), and the row's "directed k-edge-connected graph" is that notion. The earlier
      hypothesis [x184_directed_k_edge_connected] counted only the edges LEAVING each set,
      a strictly stronger hypothesis: two vertices joined by k parallel arcs u -> v are
      k-edge-connected but have no edge leaving {v}. The hypothesis is now the shared
      [edge_connected]. RE-ENCODED 2026-10-25 (coordination/PROGRAMME.md, A1). The faithfulness audit of
      2026-07-17 (meta/BLOCKED_RETARGETING_AUDIT.md) found the defining ANTISYMMETRY
      property absent: the flow object was a plain nowhere-zero flow over the integers
      modulo 5. A Nesetril-Raspaud antisymmetric flow also requires the set B of used
      values to be disjoint from the set of negatives of B, which is now the middle
      conjunct of [x184_z5_antisymmetric_flow] (for e = e' it already implies the
      nowhere-zero conjunct, 5 being odd; that conjunct is kept for readability). The old
      object was strictly weaker: two parallel edges with values 1 and 4 carry a flow of the
      old kind and no antisymmetric one. Per the pinned extracted context of the same
      paper's Conjecture 14, its Corollary 13(iv) gives a Z5-antisymmetric flow on every
      directed 12-edge-connected graph, and Conjecture 14 (k = 8) is the open case. *)
Definition z5_antisymmetric_flow_edge_connectivity_statement : Prop :=
  exists k : nat,
    forall G : mgraph,
      edge_connected G k ->
      x184_z5_antisymmetric_flow G.

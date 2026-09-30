(** * Infinite.conjectures.D4inf2 — Seymour's self-minor conjecture.

    "Every infinite graph is a proper minor of itself."  We encode the infinite
    MINOR RELATION combinatorially (branch-set model), NOT any well-quasi-order
    theory: a minor model of [H] in [G] is a family of disjoint, connected,
    nonempty branch sets realizing every [H]-edge.  Everything is a first-order
    [Prop] over the [iGraph] carrier (connectivity via [reachP], from
    foundations); no choice / cardinal / topology. *)

From GTBase Require Export base.
From Infinite Require Import foundations.igraph.
From mathcomp Require Import all_boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** An isomorphism of iGraphs: an adjacency-preserving bijection. *)
Definition iIso (G H : iGraph) : Prop :=
  exists f : iV G -> iV H,
    bijective f /\ (forall x y : iV G, iadj x y <-> iadj (f x) (f y)).

(** A MINOR MODEL of [H] in [G]: branch sets [b h ⊆ V(G)] that are nonempty,
    connected, pairwise disjoint, and realize every [H]-edge by a [G]-edge
    across the corresponding branch sets.  [iminor G H := ∃ such model] is the
    standard "H is a minor of G" (no condition on non-edges — minors may drop
    edges). *)
Definition minor_model (G H : iGraph) (b : iV H -> iV G -> Prop) : Prop :=
  [/\ (forall h : iV H, exists x, b h x),
      (forall h : iV H, connected_set (b h)),
      (forall (h1 h2 : iV H) (x : iV G), b h1 x -> b h2 x -> h1 = h2)
    & (forall h1 h2 : iV H, iadj h1 h2 ->
         exists x y, b h1 x /\ b h2 y /\ iadj x y) ].

(** [b] is a PROPER minor model: it performs at least one non-trivial minor
    operation — a vertex deletion, an edge contraction, or an edge deletion.
    This is the load-bearing guard: the IDENTITY model (singleton branch sets)
    satisfies NONE of the three, so it cannot witness the conjecture. *)
Definition proper_witness (G H : iGraph) (b : iV H -> iV G -> Prop) : Prop :=
     (exists x : iV G, forall h : iV H, ~ b h x)                 (* vertex deletion *)
  \/ (exists (h : iV H) (x y : iV G), b h x /\ b h y /\ x <> y)  (* edge contraction *)
  \/ (exists (h1 h2 : iV H) (x y : iV G),                        (* edge deletion:  *)
        ~ iadj h1 h2 /\ b h1 x /\ b h2 y /\ iadj x y).           (* a G-edge across non-adjacent branch sets *)

(** [G] is a PROPER MINOR of itself: some [H ≅ G] is a minor of [G] via a proper
    model. *)
Definition proper_self_minor (G : iGraph) : Prop :=
  exists (H : iGraph) (b : iV H -> iV G -> Prop),
    [/\ iIso H G, minor_model b & proper_witness b].

(** Corpus row: opg:seymours_self_minor_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/seymours_self_minor_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/seymours_self_minor_conjecture.json
    English statement: (Open Problem Garden, "Seymour's self-minor conjecture")
      Every infinite graph is a proper minor of itself: for every graph G whose
      vertex type contains an injective copy of the naturals there are a graph H
      isomorphic to G and a minor model of H inside G - an assignment to each
      H-vertex of a nonempty connected branch set, the branch sets pairwise
      disjoint, with every H-edge realised by a G-edge between the corresponding
      branch sets - which performs at least one nontrivial minor operation:
      either some G-vertex lies in no branch set (a vertex deletion), or some
      branch set contains two distinct vertices (an edge contraction), or some
      G-edge runs between the branch sets of two non-adjacent H-vertices (an
      edge deletion).
    Definitions: [iGraph]/[iV]/[iadj] and [infinite_graph G] (Dedekind
      infiniteness: nat injects into the vertices), [connected_set] (finite-walk
      reachability inside a Prop-subset, via [reachP]) - all in
      infinite-graph-theory/theories/foundations/igraph.v; [iIso G H] - an
      adjacency-preserving bijection (this file, D4inf2.v); [minor_model G H b]
      and [proper_witness G H b] and [proper_self_minor G] (D4inf2.v).
    Notes: the [infinite_graph] guard is load-bearing - finite graphs are
      provably NOT proper minors of themselves, so without it the statement is
      refutable.  [proper_witness] is the other load-bearing guard: the identity
      model (singleton branch sets, all edges kept) satisfies none of its three
      disjuncts, so it cannot witness the conjecture.  The minor relation is
      encoded combinatorially by branch sets; no well-quasi-order theory, choice
      or cardinal arithmetic is used. *)
Definition seymours_self_minor_statement : Prop :=
  forall G : iGraph, infinite_graph G -> proper_self_minor G.

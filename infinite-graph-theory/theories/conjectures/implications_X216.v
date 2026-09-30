(** * Infinite.conjectures.implications_X216 — wave X216 dependency-graph EDGES

    The single X216 node is [halin_hypomorphic_infinite_subgraph_statement]
    (bm:bm-003, Halin 1970).  The corpus records one relation touching it:

    - gc:e207  bm:bm-003  related_only  opg:reconstruction_conjecture.
      It is NOT an implication (the corpus argument is explicit: Halin's
      conjecture is about infinite graphs and the Reconstruction Conjecture
      about finite graphs with at least three vertices, so the hypothesis
      classes are disjoint and neither statement implies the other), and its
      other endpoint, [reconstruction_statement], lives in the
      reconstruction-theory package.  Cross-package and non-implicational, so no
      [@EDGE] record is committed.

    This file is therefore intentionally theorem-free and axiom-free. *)

From Infinite Require Import conjectures.X216.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* No machine-readable EDGE record: the only corpus relation on bm:bm-003 is the
   related_only edge e207 to opg:reconstruction_conjecture (reconstruction-theory),
   which asserts no implication in either direction. *)

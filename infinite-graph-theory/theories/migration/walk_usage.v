(** * Infinite.migration.walk_usage — B28 certificates: D4inf4's alternating walk usage, universality and its row

    Frozen verbatim at the fixed B27 016b868: D4inf4's recursive [walk_uses b x p a c] over the vertex Type of an
    [iDigraph] (the empty tail uses nothing; at [y :: p] the pair is the head step in the orientation of the polarity
    [b], or a usage of the tail at the flipped polarity; no [darc], no [alt_walk_from], propositional equality), the
    chain [universal] (for every two genuine arcs, the same [b], [x], [p] give a valid alternating walk using both)
    and the complete row [universal_highly_arc_transitive_digraphs_statement] (one digraph that is locally finite,
    highly arc transitive with the automorphism action unfolded, universal, and satisfies the three modelling guards:
    some arc, an infinite carrier, no sinks or sources).  Since B28 the live [walk_uses] is the instance
    [GTBase.walk_usage.alt_uses b x p a c] at [dV G]: the two recursions are certified equal by induction on [p], and
    [universal] and the row by pointwise transport.  [alt_walk_from] and every other D4inf4 definition stay live and
    unchanged.  No earlier migration snapshot reaches these declarations. *)

From GTBase Require Import base walk_usage.
From Infinite Require Import foundations.igraph conjectures.D4inf4.
From mathcomp Require Import all_boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Fixpoint walk_uses (G : iDigraph) (b : bool) (x : dV G) (p : seq (dV G)) (a c : dV G) : Prop :=
  match p with
  | [::] => False
  | y :: p' =>
      ((b = true /\ x = a /\ y = c) \/ (b = false /\ y = a /\ x = c))
      \/ walk_uses (~~ b) y p' a c
  end.

End Legacy.

Module D4inf4Legacy.

Definition universal (G : iDigraph) : Prop :=
  forall a1 c1 a2 c2 : dV G, darc a1 c1 -> darc a2 c2 ->
    exists (b : bool) (x : dV G) (p : seq (dV G)),
      alt_walk_from b x p /\ Legacy.walk_uses b x p a1 c1 /\ Legacy.walk_uses b x p a2 c2.

Definition universal_highly_arc_transitive_digraphs_statement : Prop :=
  exists G : iDigraph,
    [/\ d_locally_finite G, highly_arc_transitive G, D4inf4Legacy.universal G
      & [/\ d_has_arc G, d_infinite G & d_no_sink_source G] ].

End D4inf4Legacy.

(** The recursion: equal to the public alternating usage at every polarity and start, by induction on the tail. *)
Lemma walk_uses_compat (G : iDigraph) (b : bool) (x : dV G) (p : seq (dV G)) (a c : dV G) :
  Legacy.walk_uses b x p a c <-> walk_uses b x p a c.
Proof.
rewrite /walk_uses; elim: p b x => [|y p IH] b x //=.
by split=> -[h | h]; [left | right; apply/IH | left | right; apply/IH].
Qed.

Lemma universal_compat (G : iDigraph) : D4inf4Legacy.universal G <-> universal G.
Proof.
split=> h a1 c1 a2 c2 h1 h2; have [b [x [p [w [u1 u2]]]]] := h a1 c1 a2 c2 h1 h2;
  by exists b, x, p; split=> //; split; apply/walk_uses_compat.
Qed.

Lemma universal_highly_arc_transitive_digraphs_statement_compat :
  D4inf4Legacy.universal_highly_arc_transitive_digraphs_statement <->
  universal_highly_arc_transitive_digraphs_statement.
Proof.
by split=> -[G [lf hat u guards]]; exists G; split=> //; apply/universal_compat.
Qed.

Print Assumptions walk_uses_compat.
Print Assumptions universal_compat.
Print Assumptions universal_highly_arc_transitive_digraphs_statement_compat.

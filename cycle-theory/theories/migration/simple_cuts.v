(** Frozen count-one simple cuts at a69e27fedb17b9a509dc794b45f6e2aa5c8f4e9e.
    The old cut formula equals the public intersection formula on simple edges.
    Cyclic edge connectivity keeps its two cycle-containing-side premises.
    The whole Bondy row and its deepest B10 raw-cycle Original retain every
    guard and quantifier; B10's certificate source is unchanged. *)
From GTBase Require Import base common.
From GTBase Require simple_cuts.
From Cycle.conjectures Require Import X212.
From Cycle.migration Require genuine_cycle.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module GC := Cycle.migration.genuine_cycle.

Module Legacy.

Definition x212_edge_cut (G : sgraph) (S : {set G}) : {set {set G}} :=
  [set e in E(G) | #|e :&: S| == 1].

End Legacy.

Module X212Legacy.

Definition x212_cyclically_edge_connected (G : sgraph) (k : nat) : Prop :=
  forall S : {set G},
    x212_cycle_within S -> x212_cycle_within (~: S) -> k <= #|Legacy.x212_edge_cut S|.

Definition bondy_linear_cycle_cubic_statement : Prop :=
  exists p q : nat,
    [/\ 0 < p, 0 < q &
        forall G : sgraph,
          0 < #|G| -> regular G 3 -> k_connected G 3 ->
          X212Legacy.x212_cyclically_edge_connected G 4 ->
          exists c : seq G, x212_cycle c /\ p * #|G| <= q * size c].

End X212Legacy.

Module X212Original.

Definition cyclically_edge_connected (G : sgraph) (k : nat) : Prop :=
  forall S : {set G},
    GC.X212Legacy.cycle_within S -> GC.X212Legacy.cycle_within (~: S) ->
    k <= #|Legacy.x212_edge_cut S|.

Definition bondy_linear_cycle_cubic_statement : Prop :=
  exists p q : nat,
    [/\ 0 < p, 0 < q &
        forall G : sgraph,
          0 < #|G| -> regular G 3 -> k_connected G 3 ->
          X212Original.cyclically_edge_connected G 4 ->
          exists c : seq G, GC.Legacy.x212_cycle c /\ p * #|G| <= q * size c].

End X212Original.

Lemma x212_edge_cut_compat (G : sgraph) (S : {set G}) :
  Legacy.x212_edge_cut S = x212_edge_cut S.
Proof. exact: esym (GTBase.simple_cuts.cut_edges_count1 S). Qed.

Lemma x212_cyclically_edge_connected_compat (G : sgraph) (k : nat) :
  X212Legacy.x212_cyclically_edge_connected G k <-> x212_cyclically_edge_connected G k.
Proof.
split=> H S cyc cycC; have := H S cyc cycC.
- by rewrite x212_edge_cut_compat.
- by rewrite x212_edge_cut_compat.
Qed.

Lemma bondy_linear_cycle_cubic_statement_compat :
  X212Legacy.bondy_linear_cycle_cubic_statement <-> bondy_linear_cycle_cubic_statement.
Proof.
split=> -[p [q [p0 q0 H]]]; exists p, q; split=> // G G0 reg conn cyc.
- exact: H G G0 reg conn (proj2 (x212_cyclically_edge_connected_compat G 4) cyc).
- exact: H G G0 reg conn (proj1 (x212_cyclically_edge_connected_compat G 4) cyc).
Qed.

Lemma x212_cyclically_edge_connected_pre_genuine (G : sgraph) (k : nat) :
  X212Original.cyclically_edge_connected G k <-> GC.X212Legacy.cyclically_edge_connected G k.
Proof.
split=> H S cyc cycC; have := H S cyc cycC.
- by rewrite x212_edge_cut_compat.
- by rewrite x212_edge_cut_compat.
Qed.

Lemma x212_cyclically_edge_connected_original_compat (G : sgraph) (k : nat) :
  X212Original.cyclically_edge_connected G k <-> x212_cyclically_edge_connected G k.
Proof.
rewrite x212_cyclically_edge_connected_pre_genuine.
exact: GC.x212_cyclically_edge_connected_compat.
Qed.

Lemma bondy_linear_cycle_cubic_statement_original_compat :
  X212Original.bondy_linear_cycle_cubic_statement <-> bondy_linear_cycle_cubic_statement.
Proof.
rewrite -GC.bondy_linear_cycle_cubic_statement_compat.
split=> -[p [q [p0 q0 H]]]; exists p, q; split=> // G G0 reg conn cyc.
- exact: H G G0 reg conn (proj2 (x212_cyclically_edge_connected_pre_genuine G 4) cyc).
- exact: H G G0 reg conn (proj1 (x212_cyclically_edge_connected_pre_genuine G 4) cyc).
Qed.

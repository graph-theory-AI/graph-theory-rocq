(** * Packing.migration.induced_cycles — B23 certificates: XE1's induced cycle and Erdos #81

    Frozen verbatim at the fixed B22 baseline 7d8cc47: XE1's induced cycle [xe1_induced_cycle]
    ([ucycle], [2 < size c], and a chord clause with a redundant [x != y] premise before the edge
    premise and the inline Boolean test [((x, y) \in zip c (rot 1 c)) || ((y, x) \in zip c (rot 1 c))]),
    its chain [xe1_chordal] (every induced cycle has at most three vertices) and the complete row
    [erdos_81_statement] (a uniform constant [C] before [G] and [n]; every chordal graph on [n]
    vertices has a clique edge partition with [6 * m <= n ^ 2 + C * n]).  Since B23 the live
    [xe1_induced_cycle] is a transparent alias of [GTBase.induced_cycles.chordless_cycle]; the
    inline test is [seq_cyclic_consecutiveb] by conversion, but the distinctness premise is not,
    so [xe1_induced_cycle_compat] is an explicit iff through [cyclic_chordless_neq_edge].  The row
    copy keeps the unrelated M1 edge-partition vocabulary ([xe1_clique_edge_partition]) live.  No
    earlier complete frozen copy of this row exists. *)

From GTBase Require Import base induced_cycles.
From Packing.conjectures Require Import XE1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition xe1_induced_cycle (G : sgraph) (c : seq G) : Prop :=
  ucycle (--) c /\ 2 < size c /\
  forall x y : G, x \in c -> y \in c -> x != y -> x -- y ->
    ((x, y) \in zip c (rot 1 c)) || ((y, x) \in zip c (rot 1 c)).

End Legacy.

Module XE1Legacy.

Definition xe1_chordal (G : sgraph) : Prop :=
  forall c : seq G, Legacy.xe1_induced_cycle c -> size c <= 3.

Definition erdos_81_statement : Prop :=
  exists C : nat,
    forall (G : sgraph) (n : nat),
      #|G| = n -> XE1Legacy.xe1_chordal G ->
      exists m : nat, exists K : 'I_m -> {set G},
        xe1_clique_edge_partition K /\
        6 * m <= n ^ 2 + C * n.

End XE1Legacy.

(** ** Certificates *)

Lemma xe1_induced_cycle_compat (G : sgraph) (c : seq G) :
  Legacy.xe1_induced_cycle c <-> xe1_induced_cycle c.
Proof.
rewrite /xe1_induced_cycle; split=> -[uc [sz ch]].
- split=> //; split=> //; apply/cyclic_chordless_neq_edge.
  move=> x y xc yc nxy xy; exact: (ch x y xc yc nxy xy).
- split=> //; split=> // x y xc yc nxy xy.
  exact: (proj2 (cyclic_chordless_neq_edge c) ch x y xc yc nxy xy).
Qed.

Lemma xe1_chordal_compat (G : sgraph) : XE1Legacy.xe1_chordal G <-> xe1_chordal G.
Proof. by split=> h c hc; apply: h; apply/xe1_induced_cycle_compat. Qed.

Lemma erdos_81_statement_compat : XE1Legacy.erdos_81_statement <-> erdos_81_statement.
Proof.
split=> -[C h]; exists C => G n cn ch; apply: (h G n cn);
  by apply/xe1_chordal_compat.
Qed.

Print Assumptions xe1_induced_cycle_compat.
Print Assumptions xe1_chordal_compat.
Print Assumptions erdos_81_statement_compat.

(** * Chromatic.migration.consecutive_in_cycle — frozen cyclic-adjacency chains (library migration B4)

    Batch B, family [consecutive-in-cycle]
    (meta/library_primitives/consecutive-in-cycle.json).  [Legacy] freezes the
    conjecture-local helpers [x3_consecutive_in_cycle] (Prop) and
    [xe1_consecutive_in_cycle] (bool) verbatim as they stood at 49ddc03, before the
    migration: the pair [(u, v)] or [(v, u)] occurs in [zip c (rot 1 c)].  The live
    helpers now unfold to [GTBase.walks_paths.seq_cyclic_consecutive c u v] and
    [seq_cyclic_consecutiveb c u v], whose bodies are those same disjunctions, so
    every certificate below is a kernel-checked conversion.

    [X3Legacy] freezes X3's hole chain ([hole], the hole-length and constricting
    wrappers, [rainbow_hole_run]) and its four affected statements; [X160Legacy] the
    cross-module constricting row; [XE1Legacy] the diagonal count and odd-cycle
    predicate, and [XE2Legacy] the cross-module rows erdos:1091 and erdos:842 (whose
    [triangles_plus_hamilton_cycle] uses the XE1 helper negated and positively).
    The copies drop the wave prefix and refer to the frozen helpers as
    [Legacy.<name>]; definitions that do not reach a helper are the live ones.
    History follow-up: the rainbow-hole row also reaches family
    proper-colouring's (C5) helper [x3_proper_colouring].  [X3Legacy] keeps that
    live, C5-migrated helper by design, and C5's snapshot
    [Chromatic.migration.proper_colouring.X3Legacy] keeps the live
    [x3_rainbow_hole_run]; both stay verbatim.  [X3Original], at the end of this
    file, freezes the row end to end over C5's frozen colouring predicate and this
    family's frozen hole chain.  Source hashes, the exact substitutions and the
    per-row theorem names are recorded in
    meta/migration_reports/consecutive_in_cycle.md. *)

From GTBase Require Import base.
From GTBase Require induced_cycles.
From Chromatic.conjectures Require Import U8 X3 X160 XE1 XE2.
From Chromatic.migration Require proper_colouring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x3_consecutive_in_cycle (G : sgraph) (c : seq G) (u v : G) : Prop :=
  ((u, v) \in zip c (rot 1 c)) \/ ((v, u) \in zip c (rot 1 c)).

Definition xe1_consecutive_in_cycle (G : sgraph) (c : seq G) (u v : G) : bool :=
  ((u, v) \in zip c (rot 1 c)) || ((v, u) \in zip c (rot 1 c)).

End Legacy.

Module X3Legacy.

Definition hole (G : sgraph) (c : seq G) : Prop :=
  [/\ ucycle (--) c, 3 < size c &
      forall u v : G,
        u \in c -> v \in c -> u != v -> u -- v ->
        Legacy.x3_consecutive_in_cycle c u v].

Definition has_hole_length (G : sgraph) (L : nat) : Prop :=
  exists c : seq G, hole c /\ size c = L.

Definition holes_of_consecutive_lengths (G : sgraph) (ell : nat) : Prop :=
  exists t : nat,
    forall i : nat, 1 <= i -> i <= ell -> has_hole_length G (t + i).

Definition rainbow_hole_run
    (G : sgraph) (C : finType) (col : G -> C) (s : nat) : Prop :=
  exists (c : seq G) (r : nat),
    hole c /\ s <= size c /\ uniq (map col (take s (rot r c))).

Definition k_constricting (F : nat -> Prop) (k : nat) : Prop :=
  exists n : nat,
    forall G : sgraph,
      n <= χ([set: G]) ->
      k <= ω([set: G]) \/ exists L : nat, F L /\ has_hole_length G L.

Definition constricting (F : nat -> Prop) : Prop :=
  forall k : nat, k_constricting F k.

Definition bounded_clique_consecutive_hole_lengths_statement : Prop :=
  forall nu k : nat, 0 < nu -> 3 <= k ->
    exists n : nat,
      forall G : sgraph,
        ω([set: G]) < k -> n <= χ([set: G]) ->
        holes_of_consecutive_lengths G nu.

Definition bounded_gaps_sets_are_constricting_statement : Prop :=
  forall F : nat -> Prop,
    x3_positive_integer_set F ->
    x3_infinite_integer_set F ->
    x3_bounded_gaps F ->
    constricting F.

Definition rainbow_consecutive_vertices_in_hole_statement : Prop :=
  forall s kappa : nat, exists n : nat,
    forall (G : sgraph) (C : finType) (col : G -> C),
      ω([set: G]) <= kappa ->
      n <= χ([set: G]) ->
      x3_proper_colouring col ->
      rainbow_hole_run col s.

Definition clique_or_consecutive_holes_statement : Prop :=
  forall kappa ell : nat, exists c : nat,
    forall G : sgraph,
      c < χ([set: G]) ->
      kappa <= ω([set: G]) \/ holes_of_consecutive_lengths G ell.

End X3Legacy.

Module X160Legacy.

Definition density_zero_constricting_set_statement : Prop :=
  exists F : nat -> bool,
    [/\ x3_positive_integer_set (fun n : nat => F n),
        x3_infinite_integer_set (fun n : nat => F n),
        X3Legacy.constricting (fun n : nat => F n) &
        x160_density_zero F].

End X160Legacy.

Module XE1Legacy.

Definition cycle_diagonal_count (G : sgraph) (c : seq G) : nat :=
  #|[set p : G * G |
      [&& p.1 \in c, p.2 \in c, (enum_rank p.1 < enum_rank p.2)%N,
          p.1 -- p.2 & ~~ Legacy.xe1_consecutive_in_cycle c p.1 p.2]]|.

Definition odd_cycle_with_diagonals (G : sgraph) (d : nat) : Prop :=
  exists c : seq G,
    xe1_cycle c /\ odd (size c) /\ d <= cycle_diagonal_count c.

End XE1Legacy.

Module XE2Legacy.

Definition triangles_plus_hamilton_cycle (G : sgraph) (n : nat) : Prop :=
  exists (T : 'I_n -> {set G}) (c : seq G),
    #|G| = 3 * n /\
    (forall i : 'I_n, clique (T i) /\ #|T i| = 3) /\
    (forall i j : 'I_n, i != j -> [disjoint T i & T j]) /\
    ucycle (--) c /\
    size c = 3 * n /\
    (forall v : G, v \in c) /\
    (forall (i : 'I_n) (x y : G),
        x \in T i -> y \in T i -> x != y ->
        ~~ Legacy.xe1_consecutive_in_cycle c x y) /\
    forall x y : G, x -- y ->
      (exists i : 'I_n, x \in T i /\ y \in T i) \/
      Legacy.xe1_consecutive_in_cycle c x y.

Definition erdos_1091_statement : Prop :=
  (forall G : sgraph,
    ~ xe1_subgraph_of 'K_4 G ->
    χ([set: G]) = 4 ->
    XE1Legacy.odd_cycle_with_diagonals G 2) /\
  exists f : nat -> nat,
    xe1_unbounded f /\
    forall (r : nat) (G : sgraph),
      ~ xe1_subgraph_of 'K_4 G ->
      χ([set: G]) = 4 ->
      xe1_induced_subgraph_chi_le G r 3 ->
      XE1Legacy.odd_cycle_with_diagonals G (f r).

Definition erdos_842_statement : Prop :=
  forall (n : nat) (G : sgraph),
    triangles_plus_hamilton_cycle G n ->
    χ([set: G]) <= 3.

End XE2Legacy.

(** ** Certificates *)

(** B23 (2026-10-03): the live holes / induced cycles are now aliases of GTBase.induced_cycles, which
    states chordlessness without a distinctness premise and with the Boolean cyclic consecutiveness.
    The certificates below that reach them are therefore proved through its bridges instead of by
    conversion; their statements and every frozen body are unchanged. *)

Lemma x3_consecutive_in_cycle_compat (G : sgraph) (c : seq G) (u v : G) :
  Legacy.x3_consecutive_in_cycle c u v = x3_consecutive_in_cycle c u v.
Proof. by []. Qed.

Lemma xe1_consecutive_in_cycle_compat (G : sgraph) (c : seq G) (u v : G) :
  Legacy.xe1_consecutive_in_cycle c u v = xe1_consecutive_in_cycle c u v.
Proof. by []. Qed.

Lemma x3_hole_compat (G : sgraph) (c : seq G) : X3Legacy.hole c <-> x3_hole c.
Proof.
rewrite /x3_hole; split=> [[uc sz ch] | [uc [sz ch]]].
- split=> //; split=> //; apply/induced_cycles.cyclic_chordless_prop_neq_edge.
  move=> u v uc' vc' nuv uv; exact: (ch u v uc' vc' nuv uv).
- split=> // u v uc' vc' nuv uv.
  exact: (proj2 (induced_cycles.cyclic_chordless_prop_neq_edge c) ch u v uc' vc' nuv uv).
Qed.

Lemma x3_has_hole_length_compat (G : sgraph) (L : nat) :
  X3Legacy.has_hole_length G L <-> x3_has_hole_length G L.
Proof.
by split=> -[c [h s]]; exists c; split=> //; apply/x3_hole_compat.
Qed.

Lemma x3_holes_of_consecutive_lengths_compat (G : sgraph) (ell : nat) :
  X3Legacy.holes_of_consecutive_lengths G ell <-> x3_holes_of_consecutive_lengths G ell.
Proof.
by split=> -[t h]; exists t => i i1 il; apply/x3_has_hole_length_compat; apply: h.
Qed.

Lemma x3_rainbow_hole_run_compat (G : sgraph) (C : finType) (col : G -> C) (s : nat) :
  X3Legacy.rainbow_hole_run col s <-> x3_rainbow_hole_run col s.
Proof.
by split=> -[c [r [h rest]]]; exists c, r; split=> //; apply/x3_hole_compat.
Qed.

Lemma x3_k_constricting_compat (F : nat -> Prop) (k : nat) :
  X3Legacy.k_constricting F k <-> x3_k_constricting F k.
Proof.
split=> -[n h]; exists n => G chi; case: (h G chi) => [om | [L [FL hl]]];
  first [by left | by right; exists L; split=> //; apply/x3_has_hole_length_compat].
Qed.

Lemma x3_constricting_compat (F : nat -> Prop) :
  X3Legacy.constricting F <-> x3_constricting F.
Proof.
by split=> h k; apply/x3_k_constricting_compat; apply: h.
Qed.

Lemma bounded_clique_consecutive_hole_lengths_statement_compat :
  X3Legacy.bounded_clique_consecutive_hole_lengths_statement <->
  bounded_clique_consecutive_hole_lengths_statement.
Proof.
split=> h nu k nu0 k3; have [n hn] := h nu k nu0 k3; exists n => G om chi;
  by apply/x3_holes_of_consecutive_lengths_compat; apply: hn.
Qed.

Lemma bounded_gaps_sets_are_constricting_statement_compat :
  X3Legacy.bounded_gaps_sets_are_constricting_statement <->
  bounded_gaps_sets_are_constricting_statement.
Proof.
by split=> h F p i b; apply/x3_constricting_compat; apply: h.
Qed.

Lemma rainbow_consecutive_vertices_in_hole_statement_compat :
  X3Legacy.rainbow_consecutive_vertices_in_hole_statement <->
  rainbow_consecutive_vertices_in_hole_statement.
Proof.
split=> h s kappa; have [n hn] := h s kappa; exists n => G C col om chi pc;
  by apply/x3_rainbow_hole_run_compat; apply: hn.
Qed.

Lemma clique_or_consecutive_holes_statement_compat :
  X3Legacy.clique_or_consecutive_holes_statement <-> clique_or_consecutive_holes_statement.
Proof.
split=> h kappa ell; have [c hc] := h kappa ell; exists c => G chi;
  case: (hc G chi) => [om | ho];
  first [by left | by right; apply/x3_holes_of_consecutive_lengths_compat].
Qed.

Lemma density_zero_constricting_set_statement_compat :
  X160Legacy.density_zero_constricting_set_statement <->
  density_zero_constricting_set_statement.
Proof.
by split=> -[F [p i c d]]; exists F; split=> //; apply/x3_constricting_compat.
Qed.

Lemma xe1_cycle_diagonal_count_compat (G : sgraph) (c : seq G) :
  XE1Legacy.cycle_diagonal_count c = xe1_cycle_diagonal_count c.
Proof. by []. Qed.

Lemma xe1_odd_cycle_with_diagonals_compat (G : sgraph) (d : nat) :
  XE1Legacy.odd_cycle_with_diagonals G d <-> xe1_odd_cycle_with_diagonals G d.
Proof. exact: iff_refl. Qed.

Lemma xe2_triangles_plus_hamilton_cycle_compat (G : sgraph) (n : nat) :
  XE2Legacy.triangles_plus_hamilton_cycle G n <-> xe2_triangles_plus_hamilton_cycle G n.
Proof. exact: iff_refl. Qed.

Lemma erdos_1091_statement_compat : XE2Legacy.erdos_1091_statement <-> erdos_1091_statement.
Proof. exact: iff_refl. Qed.

Lemma erdos_842_statement_compat : XE2Legacy.erdos_842_statement <-> erdos_842_statement.
Proof. exact: iff_refl. Qed.

(** ** X3's rainbow-hole row before the B4 and C5 migrations *)

Module X3Original.

Definition rainbow_consecutive_vertices_in_hole_statement : Prop :=
  forall s kappa : nat, exists n : nat,
    forall (G : sgraph) (C : finType) (col : G -> C),
      ω([set: G]) <= kappa ->
      n <= χ([set: G]) ->
      proper_colouring.Legacy.x3_proper_colouring col ->
      X3Legacy.rainbow_hole_run col s.

End X3Original.

Lemma rainbow_consecutive_vertices_in_hole_statement_original_compat :
  X3Original.rainbow_consecutive_vertices_in_hole_statement <->
  rainbow_consecutive_vertices_in_hole_statement.
Proof.
split=> st s kappa; have [n hn] := st s kappa; exists n => G C col om chi pc;
  apply/x3_rainbow_hole_run_compat; apply: hn => //;
  by apply/proper_colouring.x3_proper_colouring_compat.
Qed.

(** * Chromatic.migration.induced_cycles — B23 certificates: X3's hole and its five rows

    Frozen verbatim at the fixed B22 baseline 7d8cc47: X3's hole [x3_hole] (a three-way
    conjunction: [ucycle], [3 < size c], and a chord clause with a redundant [u != v] premise before
    the edge premise and the consecutiveness stated as a proposition through B4's live
    [x3_consecutive_in_cycle]), its chains [x3_has_hole_length], [x3_holes_of_consecutive_lengths],
    [x3_rainbow_hole_run], [x3_k_constricting], [x3_constricting], the four complete X3 rows and
    the complete X160 row.  Since B23 the live [x3_hole] is a transparent alias of
    [GTBase.induced_cycles.hole]; the two are not convertible (conjunction shape, distinctness
    premise, Prop versus Boolean consecutiveness), so the certificate [x3_hole_compat] is an
    explicit iff through [cyclic_chordless_prop_neq_edge], and every chain and row certificate
    transports it.  The copies keep the other families' live helpers ([x3_consecutive_in_cycle] of
    B4, [x3_proper_colouring] of C5, the integer-set and density vocabulary).

    The complete earlier rows are reused with their owners' certificates: B4's
    [X3Legacy.bounded_clique_consecutive_hole_lengths_statement],
    [X3Legacy.bounded_gaps_sets_are_constricting_statement],
    [X3Legacy.clique_or_consecutive_holes_statement] and [X160Legacy.density_zero_constricting_set_statement]
    (raw pair formula throughout), and B4's [X3Original.rainbow_consecutive_vertices_in_hole_statement]
    (C5's frozen colouring with B4's frozen hole chain). *)

From GTBase Require Import base induced_cycles.
From Chromatic.conjectures Require Import U8 X3 X160.
From Chromatic.migration Require consecutive_in_cycle.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module B4 := Chromatic.migration.consecutive_in_cycle.

Module Legacy.

Definition x3_hole (G : sgraph) (c : seq G) : Prop :=
  [/\ ucycle (--) c, 3 < size c &
      forall u v : G,
        u \in c -> v \in c -> u != v -> u -- v ->
        x3_consecutive_in_cycle c u v].

End Legacy.

Module X3Legacy.

Definition x3_has_hole_length (G : sgraph) (L : nat) : Prop :=
  exists c : seq G, Legacy.x3_hole c /\ size c = L.

Definition x3_holes_of_consecutive_lengths (G : sgraph) (ell : nat) : Prop :=
  exists t : nat,
    forall i : nat, 1 <= i -> i <= ell -> X3Legacy.x3_has_hole_length G (t + i).

Definition x3_rainbow_hole_run
    (G : sgraph) (C : finType) (col : G -> C) (s : nat) : Prop :=
  exists (c : seq G) (r : nat),
    Legacy.x3_hole c /\ s <= size c /\ uniq (map col (take s (rot r c))).

Definition x3_k_constricting (F : nat -> Prop) (k : nat) : Prop :=
  exists n : nat,
    forall G : sgraph,
      n <= χ([set: G]) ->
      k <= ω([set: G]) \/ exists L : nat, F L /\ X3Legacy.x3_has_hole_length G L.

Definition x3_constricting (F : nat -> Prop) : Prop :=
  forall k : nat, X3Legacy.x3_k_constricting F k.

Definition bounded_clique_consecutive_hole_lengths_statement : Prop :=
  forall nu k : nat, 0 < nu -> 3 <= k ->
    exists n : nat,
      forall G : sgraph,
        ω([set: G]) < k -> n <= χ([set: G]) ->
        X3Legacy.x3_holes_of_consecutive_lengths G nu.

Definition bounded_gaps_sets_are_constricting_statement : Prop :=
  forall F : nat -> Prop,
    x3_positive_integer_set F ->
    x3_infinite_integer_set F ->
    x3_bounded_gaps F ->
    X3Legacy.x3_constricting F.

Definition rainbow_consecutive_vertices_in_hole_statement : Prop :=
  forall s kappa : nat, exists n : nat,
    forall (G : sgraph) (C : finType) (col : G -> C),
      ω([set: G]) <= kappa ->
      n <= χ([set: G]) ->
      x3_proper_colouring col ->
      X3Legacy.x3_rainbow_hole_run col s.

Definition clique_or_consecutive_holes_statement : Prop :=
  forall kappa ell : nat, exists c : nat,
    forall G : sgraph,
      c < χ([set: G]) ->
      kappa <= ω([set: G]) \/ X3Legacy.x3_holes_of_consecutive_lengths G ell.

End X3Legacy.

Module X160Legacy.

Definition density_zero_constricting_set_statement : Prop :=
  exists F : nat -> bool,
    [/\ x3_positive_integer_set (fun n : nat => F n),
        x3_infinite_integer_set (fun n : nat => F n),
        X3Legacy.x3_constricting (fun n : nat => F n) &
        x160_density_zero F].

End X160Legacy.

(** ** The hole: an explicit iff with the canonical view *)

Lemma x3_hole_compat (G : sgraph) (c : seq G) : Legacy.x3_hole c <-> x3_hole c.
Proof.
rewrite /x3_hole; split=> [[uc sz ch] | [uc [sz ch]]].
- split=> //; split=> //; apply/cyclic_chordless_prop_neq_edge.
  move=> u v uc' vc' nuv uv; exact: (ch u v uc' vc' nuv uv).
- split=> // u v uc' vc' nuv uv.
  exact: (proj2 (cyclic_chordless_prop_neq_edge c) ch u v uc' vc' nuv uv).
Qed.

(** ** Chains *)

Lemma x3_has_hole_length_compat (G : sgraph) (L : nat) :
  X3Legacy.x3_has_hole_length G L <-> x3_has_hole_length G L.
Proof. by split=> -[c [h s]]; exists c; split=> //; apply/x3_hole_compat. Qed.

Lemma x3_holes_of_consecutive_lengths_compat (G : sgraph) (ell : nat) :
  X3Legacy.x3_holes_of_consecutive_lengths G ell <-> x3_holes_of_consecutive_lengths G ell.
Proof. by split=> -[t h]; exists t => i i1 il; apply/x3_has_hole_length_compat; apply: h. Qed.

Lemma x3_rainbow_hole_run_compat (G : sgraph) (C : finType) (col : G -> C) (s : nat) :
  X3Legacy.x3_rainbow_hole_run col s <-> x3_rainbow_hole_run col s.
Proof. by split=> -[c [r [h rest]]]; exists c, r; split=> //; apply/x3_hole_compat. Qed.

Lemma x3_k_constricting_compat (F : nat -> Prop) (k : nat) :
  X3Legacy.x3_k_constricting F k <-> x3_k_constricting F k.
Proof.
split=> -[n h]; exists n => G chi; case: (h G chi) => [om | [L [FL hl]]];
  first [by left | by right; exists L; split=> //; apply/x3_has_hole_length_compat].
Qed.

Lemma x3_constricting_compat (F : nat -> Prop) :
  X3Legacy.x3_constricting F <-> x3_constricting F.
Proof. by split=> h k; apply/x3_k_constricting_compat; apply: h. Qed.

(** ** The five complete current rows *)

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
Proof. by split=> h F p i b; apply/x3_constricting_compat; apply: h. Qed.

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
  X160Legacy.density_zero_constricting_set_statement <-> density_zero_constricting_set_statement.
Proof. by split=> -[F [p i c d]]; exists F; split=> //; apply/x3_constricting_compat. Qed.

(** ** The five complete earlier rows, reused from B4 with B4's own certificates *)

Lemma bounded_clique_consecutive_hole_lengths_statement_original_compat :
  Chromatic.migration.consecutive_in_cycle.X3Legacy.bounded_clique_consecutive_hole_lengths_statement <->
  bounded_clique_consecutive_hole_lengths_statement.
Proof. exact: B4.bounded_clique_consecutive_hole_lengths_statement_compat. Qed.

Lemma bounded_gaps_sets_are_constricting_statement_original_compat :
  Chromatic.migration.consecutive_in_cycle.X3Legacy.bounded_gaps_sets_are_constricting_statement <->
  bounded_gaps_sets_are_constricting_statement.
Proof. exact: B4.bounded_gaps_sets_are_constricting_statement_compat. Qed.

Lemma rainbow_consecutive_vertices_in_hole_statement_original_compat :
  Chromatic.migration.consecutive_in_cycle.X3Original.rainbow_consecutive_vertices_in_hole_statement <->
  rainbow_consecutive_vertices_in_hole_statement.
Proof. exact: B4.rainbow_consecutive_vertices_in_hole_statement_original_compat. Qed.

Lemma clique_or_consecutive_holes_statement_original_compat :
  Chromatic.migration.consecutive_in_cycle.X3Legacy.clique_or_consecutive_holes_statement <->
  clique_or_consecutive_holes_statement.
Proof. exact: B4.clique_or_consecutive_holes_statement_compat. Qed.

Lemma density_zero_constricting_set_statement_original_compat :
  Chromatic.migration.consecutive_in_cycle.X160Legacy.density_zero_constricting_set_statement <->
  density_zero_constricting_set_statement.
Proof. exact: B4.density_zero_constricting_set_statement_compat. Qed.

Print Assumptions x3_hole_compat.
Print Assumptions x3_has_hole_length_compat.
Print Assumptions x3_holes_of_consecutive_lengths_compat.
Print Assumptions x3_rainbow_hole_run_compat.
Print Assumptions x3_k_constricting_compat.
Print Assumptions x3_constricting_compat.
Print Assumptions bounded_clique_consecutive_hole_lengths_statement_compat.
Print Assumptions bounded_gaps_sets_are_constricting_statement_compat.
Print Assumptions rainbow_consecutive_vertices_in_hole_statement_compat.
Print Assumptions clique_or_consecutive_holes_statement_compat.
Print Assumptions density_zero_constricting_set_statement_compat.
Print Assumptions bounded_clique_consecutive_hole_lengths_statement_original_compat.
Print Assumptions bounded_gaps_sets_are_constricting_statement_original_compat.
Print Assumptions rainbow_consecutive_vertices_in_hole_statement_original_compat.
Print Assumptions clique_or_consecutive_holes_statement_original_compat.
Print Assumptions density_zero_constricting_set_statement_original_compat.

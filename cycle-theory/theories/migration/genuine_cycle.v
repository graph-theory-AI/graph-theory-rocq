(** * Cycle.migration.genuine_cycle — frozen genuine cycles of X212, X9 and the cycle XE1/XE2
    rows (library migration B10)

    Batch B, family [genuine-cycle] (meta/library_primitives/genuine-cycle.json).
    [Legacy] freezes, verbatim as they stood at the B10 baseline 00d6bb3, X212's
    BOOLEAN [x212_cycle] ([ucycleb (--) c && (2 < size c)]) and the Prop helpers
    [x9_genuine_cycle] and XE1's [xe1_cycle] ([ucycle (--) c /\ 2 < size c]).  The
    live helpers now unfold to [GTBase.walks_paths.seq_cycleb (--) c] and
    [GTBase.walks_paths.seq_cycle (--) c], whose bodies are these terms, so the
    per-row certificates are kernel-checked conversions and the Boolean/Prop
    signatures are unchanged.  [X212Legacy] freezes the longest cycle, cycle-within
    and cyclic edge connectivity chain and Smith's, Bondy's and Birmele's rows;
    [X9Legacy] the two X9 rows; [XE1Legacy] the cycle-or-edge pieces and #184;
    [XE2Legacy] the cross-file cycle length predicates and #641, #71, #752, #815, all
    with this family's helpers only.

    History.  [X9Original] gives the complete minimum-degree chord row before B4 and
    B10: B4's frozen chord count (Cycle.migration.consecutive_in_cycle.X9Legacy) with
    this family's frozen cycle; B4's X9Legacy row is unchanged.  Hashes and
    substitutions: meta/migration_reports/genuine_cycle.md. *)

From GTBase Require Import base.
From Cycle.conjectures Require Import X212 X9 XE1 XE2.
From Cycle.migration Require consecutive_in_cycle.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x212_cycle (G : sgraph) (c : seq G) : bool :=
  ucycleb (--) c && (2 < size c).

Definition x9_genuine_cycle (G : sgraph) (c : seq G) : Prop :=
  ucycle (--) c /\ 2 < size c.

Definition xe1_cycle (G : sgraph) (c : seq G) : Prop :=
  ucycle (--) c /\ 2 < size c.

End Legacy.

Module X212Legacy.

Definition longest_cycle (G : sgraph) (c : seq G) : Prop :=
  Legacy.x212_cycle c /\ forall c' : seq G, Legacy.x212_cycle c' -> size c' <= size c.

Definition cycle_within (G : sgraph) (S : {set G}) : Prop :=
  exists c : seq G, Legacy.x212_cycle c /\ {subset c <= S}.

Definition cyclically_edge_connected (G : sgraph) (k : nat) : Prop :=
  forall S : {set G},
    cycle_within S -> cycle_within (~: S) -> k <= #|x212_edge_cut S|.

Definition smith_two_longest_cycles_statement : Prop :=
  forall (k : nat) (G : sgraph) (c d : seq G),
    2 <= k -> k_connected G k ->
    longest_cycle c -> longest_cycle d ->
    k <= #|x212_cycle_vertices c :&: x212_cycle_vertices d|.

Definition bondy_linear_cycle_cubic_statement : Prop :=
  exists p q : nat,
    [/\ 0 < p, 0 < q &
        forall G : sgraph,
          0 < #|G| -> regular G 3 -> k_connected G 3 ->
          cyclically_edge_connected G 4 ->
          exists c : seq G, Legacy.x212_cycle c /\ p * #|G| <= q * size c].

Definition birmele_long_cycle_transversal_statement : Prop :=
  forall (k : nat) (G : sgraph),
    3 <= k ->
    (forall c d : seq G,
       Legacy.x212_cycle c -> k <= size c -> Legacy.x212_cycle d -> k <= size d ->
       exists x : G, (x \in c) && (x \in d)) ->
    exists S : {set G},
      #|S| <= k /\
      forall c : seq G, Legacy.x212_cycle c -> k <= size c -> exists x : G, (x \in S) && (x \in c).

End X212Legacy.

Module X9Legacy.

Definition proper_edge_coloured_short_cycle_statement : Prop :=
  forall (n r : nat) (G : sgraph) (col : {set G} -> 'I_n),
    0 < n -> 0 < r -> #|G| = n ->
    @x9_colour_classes_large G n r col ->
    exists c : seq G,
      @Legacy.x9_genuine_cycle G c /\
      size c <= ceil_div n r /\
      @x9_cycle_incident_edges_properly_coloured G n col c.

Definition min_degree_three_linearly_many_chords_cycle_statement : Prop :=
  exists cnum cden : nat,
    0 < cnum /\ 0 < cden /\
    forall G : sgraph,
      0 < #|G| ->
      (forall v : G, 3 <= #|N(v)|) ->
      exists c : seq G,
        @Legacy.x9_genuine_cycle G c /\
        cden * @x9_cycle_chord_count G c >= cnum * size c.

End X9Legacy.

Module X9Original.

Definition min_degree_three_linearly_many_chords_cycle_statement : Prop :=
  exists cnum cden : nat,
    0 < cnum /\ 0 < cden /\
    forall G : sgraph,
      0 < #|G| ->
      (forall v : G, 3 <= #|N(v)|) ->
      exists c : seq G,
        @Legacy.x9_genuine_cycle G c /\
        cden * @Cycle.migration.consecutive_in_cycle.X9Legacy.cycle_chord_count G c >= cnum * size c.

End X9Original.

Module XE1Legacy.

Definition cycle_or_edge_piece (G : sgraph) (P : {set {set G}}) : Prop :=
  (exists c : seq G, Legacy.xe1_cycle c /\ P = xe1_cycle_edges c) \/
  (exists e : {set G}, e \in xe1_edge_set G /\ P = [set e]).

Definition erdos_184_statement : Prop :=
  exists C : nat,
    forall G : sgraph,
      exists m : nat, exists P : 'I_m -> {set {set G}},
        m <= C * #|G| /\
        xe1_pairwise_edge_disjoint P /\
        xe1_covers_edges P /\
        forall i : 'I_m, cycle_or_edge_piece (P i).

End XE1Legacy.

Module XE2Legacy.

Definition cycle_lengths (G : sgraph) (L : seq nat) : Prop :=
  uniq L /\
  forall ell : nat,
    ell \in L <->
    exists c : seq G, Legacy.xe1_cycle c /\ size c = ell.

Definition all_cycle_lengths_in (G : sgraph) (P : nat -> Prop) : Prop :=
  exists c : seq G, Legacy.xe1_cycle c /\ P (size c).

Definition erdos_641_statement : Prop :=
  exists f : nat -> nat,
    forall (k : nat) (G : sgraph),
      1 <= k ->
      f k <= χ([set: G]) ->
      exists C : 'I_k -> seq G,
        (forall i : 'I_k, Legacy.xe1_cycle (C i)) /\
        (forall i j : 'I_k, xe2_same_vertex_set (C i) (C j)) /\
        xe2_edge_disjoint_cycles C.

Definition erdos_71_statement : Prop :=
  forall P : nat -> Prop,
    xe2_arithmetic_progression P ->
    xe2_contains_even P ->
    exists c : nat,
      forall G : sgraph,
        0 < #|G| ->
        average_degree_geq G c 1 ->
        all_cycle_lengths_in G P.

Definition erdos_752_statement : Prop :=
  forall s : nat, 1 <= s ->
    exists C k0 : nat,
      0 < C /\
      forall (k : nat) (G : sgraph),
        0 < #|G| ->
        k0 <= k ->
        xe2_min_degree_at_least G k ->
        girth_geq G (2 * s).+1 ->
        exists L : seq nat, cycle_lengths G L /\ k ^ s <= C * size L.

Definition erdos_815_statement : Prop :=
  forall k : nat, 3 <= k ->
    exists N : nat,
      forall (n : nat) (G : sgraph),
        N <= n ->
        #|G| = n ->
        #|xe1_edge_set G| = 2 * n - 2 ->
        xe2_proper_induced_subgraphs_min_degree_le2 G ->
        exists c : seq G, Legacy.xe1_cycle c /\ size c = k.

End XE2Legacy.

(** ** Certificates *)

Lemma x212_cycle_compat (G : sgraph) (c : seq G) : Legacy.x212_cycle c = x212_cycle c.
Proof. by []. Qed.

Lemma x9_genuine_cycle_compat (G : sgraph) (c : seq G) :
  Legacy.x9_genuine_cycle c = x9_genuine_cycle c.
Proof. by []. Qed.

Lemma xe1_cycle_compat (G : sgraph) (c : seq G) : Legacy.xe1_cycle c = xe1_cycle c.
Proof. by []. Qed.

Lemma x212_longest_cycle_compat (G : sgraph) (c : seq G) :
  X212Legacy.longest_cycle c <-> x212_longest_cycle c.
Proof. exact: iff_refl. Qed.

Lemma x212_cycle_within_compat (G : sgraph) (S : {set G}) :
  X212Legacy.cycle_within S <-> x212_cycle_within S.
Proof. exact: iff_refl. Qed.

Lemma x212_cyclically_edge_connected_compat (G : sgraph) (k : nat) :
  X212Legacy.cyclically_edge_connected G k <-> x212_cyclically_edge_connected G k.
Proof. exact: iff_refl. Qed.

Lemma smith_two_longest_cycles_statement_compat :
  X212Legacy.smith_two_longest_cycles_statement <-> smith_two_longest_cycles_statement.
Proof. exact: iff_refl. Qed.

Lemma bondy_linear_cycle_cubic_statement_compat :
  X212Legacy.bondy_linear_cycle_cubic_statement <-> bondy_linear_cycle_cubic_statement.
Proof. exact: iff_refl. Qed.

Lemma birmele_long_cycle_transversal_statement_compat :
  X212Legacy.birmele_long_cycle_transversal_statement <-> birmele_long_cycle_transversal_statement.
Proof. exact: iff_refl. Qed.

Lemma proper_edge_coloured_short_cycle_statement_compat :
  X9Legacy.proper_edge_coloured_short_cycle_statement <-> proper_edge_coloured_short_cycle_statement.
Proof. exact: iff_refl. Qed.

Lemma min_degree_three_linearly_many_chords_cycle_statement_compat :
  X9Legacy.min_degree_three_linearly_many_chords_cycle_statement <->
  min_degree_three_linearly_many_chords_cycle_statement.
Proof. exact: iff_refl. Qed.

(** Before B4 and B10: B4's frozen chord count and this family's frozen cycle. *)
Lemma min_degree_three_linearly_many_chords_cycle_statement_original_compat :
  X9Original.min_degree_three_linearly_many_chords_cycle_statement <->
  min_degree_three_linearly_many_chords_cycle_statement.
Proof. exact: iff_refl. Qed.

Lemma xe1_cycle_or_edge_piece_compat (G : sgraph) (P : {set {set G}}) :
  XE1Legacy.cycle_or_edge_piece P <-> xe1_cycle_or_edge_piece P.
Proof. exact: iff_refl. Qed.

Lemma erdos_184_statement_compat : XE1Legacy.erdos_184_statement <-> erdos_184_statement.
Proof. exact: iff_refl. Qed.

Lemma xe2_cycle_lengths_compat (G : sgraph) (L : seq nat) :
  XE2Legacy.cycle_lengths G L <-> xe2_cycle_lengths G L.
Proof. exact: iff_refl. Qed.

Lemma xe2_all_cycle_lengths_in_compat (G : sgraph) (P : nat -> Prop) :
  XE2Legacy.all_cycle_lengths_in G P <-> xe2_all_cycle_lengths_in G P.
Proof. exact: iff_refl. Qed.

Lemma erdos_641_statement_compat : XE2Legacy.erdos_641_statement <-> erdos_641_statement.
Proof. exact: iff_refl. Qed.

Lemma erdos_71_statement_compat : XE2Legacy.erdos_71_statement <-> erdos_71_statement.
Proof. exact: iff_refl. Qed.

Lemma erdos_752_statement_compat : XE2Legacy.erdos_752_statement <-> erdos_752_statement.
Proof. exact: iff_refl. Qed.

Lemma erdos_815_statement_compat : XE2Legacy.erdos_815_statement <-> erdos_815_statement.
Proof. exact: iff_refl. Qed.

Print Assumptions x212_cycle_compat.
Print Assumptions x9_genuine_cycle_compat.
Print Assumptions xe1_cycle_compat.
Print Assumptions smith_two_longest_cycles_statement_compat.
Print Assumptions bondy_linear_cycle_cubic_statement_compat.
Print Assumptions birmele_long_cycle_transversal_statement_compat.
Print Assumptions proper_edge_coloured_short_cycle_statement_compat.
Print Assumptions min_degree_three_linearly_many_chords_cycle_statement_compat.
Print Assumptions min_degree_three_linearly_many_chords_cycle_statement_original_compat.
Print Assumptions erdos_184_statement_compat.
Print Assumptions erdos_641_statement_compat.
Print Assumptions erdos_71_statement_compat.
Print Assumptions erdos_752_statement_compat.
Print Assumptions erdos_815_statement_compat.

(** * Cycle.migration.cycle_edges — frozen cyclic edge extractors of X9, X24 and the cycle XE1/XE2
    rows (library migration B11)

    Batch B, family [cycle-edges] (meta/library_primitives/cycle-edges.json).  [Legacy]
    freezes, verbatim as they stood at the B11 baseline 0a0203e, X9's and X24's raw ORDERED
    lists [map (fun p => [set p.1; p.2]) (zip c (rot 1 c))] and XE1's actual-edge filter
    [xe1_cycle_edges] (adjacent endpoints of [c] whose pair occurs in [zip c (rot 1 c)] in
    either order).  The live helpers now unfold to [GTBase.walks_paths.seq_cycle_edge_list c]
    and [GTBase.walks_paths.seq_cycle_graph_edge_set c], whose bodies are these terms, so every
    per-row certificate is a kernel-checked conversion.  [X9Legacy], [X24Legacy], [XE1Legacy]
    and [XE2Legacy] freeze the affected chains and rows (X9's incident-edge colouring and
    proper-edge-coloured short cycle row, X24's rainbow cycle and row, XE1's cycle-or-edge
    pieces and #184, XE2's cross-file edge-disjoint cycles and #641) with this family's helpers
    only.

    History.  Complete rows over the earlier families' frozen copies:
    - [X9Original] (B10+B11): B10's frozen genuine cycle with this family's frozen colouring
      chain;
    - [XE1Original] (B10+B11): #184 over B10's frozen cycle and this family's frozen edge filter;
    - [XE2Original] (B10+B11): #641 over B10's frozen cycle and this family's frozen
      edge-disjoint cycles;
    - [X24Original] (C2+B11): the C2 one-factorization chain (pre-M1 edge set, pre-C2 perfect
      matching) with this family's frozen rainbow cycle.
    The B10 and C2 per-row snapshots stay unchanged; they still call live chains of this family
    and are documented in both specs.  M1's edge-set aliases ([x9_edge_set], [xe1_edge_set])
    stay live in these rows: M1 froze only its helpers there.  Hashes and substitutions:
    meta/migration_reports/cycle_edges.md. *)

From GTBase Require Import base.
From Cycle.conjectures Require Import X9 X24 XE1 XE2.
From Cycle.migration Require genuine_cycle perfect_matching.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The earlier families' frozen copies, without Import. *)
Module B10 := Cycle.migration.genuine_cycle.
Module C2 := Cycle.migration.perfect_matching.

Module Legacy.

Definition x9_cycle_edges (G : sgraph) (c : seq G) : seq {set G} :=
  map (fun p : G * G => [set p.1; p.2]) (zip c (rot 1 c)).

Definition x24_cycle_edge_seq (G : sgraph) (c : seq G) : seq {set G} :=
  map (fun p : G * G => [set p.1; p.2]) (zip c (rot 1 c)).

Definition xe1_cycle_edges (G : sgraph) (c : seq G) : {set {set G}} :=
  [set e : {set G} |
      [exists p : G * G,
        [&& p.1 \in c, p.2 \in c, p.1 -- p.2,
            e == [set p.1; p.2] &
            (((p.1, p.2) \in zip c (rot 1 c)) ||
             ((p.2, p.1) \in zip c (rot 1 c)))]]].

End Legacy.

Module X9Legacy.

Definition cycle_incident_edges_properly_coloured
    (G : sgraph) (n : nat) (col : {set G} -> 'I_n) (c : seq G) : Prop :=
  forall e f : {set G},
    e \in @Legacy.x9_cycle_edges G c ->
    f \in @Legacy.x9_cycle_edges G c ->
    e != f ->
    ~~ [disjoint e & f] ->
    col e != col f.

Definition proper_edge_coloured_short_cycle_statement : Prop :=
  forall (n r : nat) (G : sgraph) (col : {set G} -> 'I_n),
    0 < n -> 0 < r -> #|G| = n ->
    @x9_colour_classes_large G n r col ->
    exists c : seq G,
      @x9_genuine_cycle G c /\
      size c <= ceil_div n r /\
      @cycle_incident_edges_properly_coloured G n col c.

End X9Legacy.

Module X9Original.

Definition proper_edge_coloured_short_cycle_statement : Prop :=
  forall (n r : nat) (G : sgraph) (col : {set G} -> 'I_n),
    0 < n -> 0 < r -> #|G| = n ->
    @x9_colour_classes_large G n r col ->
    exists c : seq G,
      @B10.Legacy.x9_genuine_cycle G c /\
      size c <= ceil_div n r /\
      @X9Legacy.cycle_incident_edges_properly_coloured G n col c.

End X9Original.

Module X24Legacy.

Definition rainbow_cycle
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (c : seq G) : Prop :=
  ucycle (--) c /\ 2 < size c /\ uniq (map col (Legacy.x24_cycle_edge_seq c)).

Definition one_factorization_long_rainbow_cycle_statement : Prop :=
  forall (n : nat) (col : {set 'K_n} -> 'I_(n.-1)),
    2 < n ->
    ~~ odd n ->
    x24_one_factorization col ->
    exists c : seq (complete n),
      rainbow_cycle col c /\
      (n - 2 <= size c)%N.

End X24Legacy.

Module X24Original.

Definition one_factorization_long_rainbow_cycle_statement : Prop :=
  forall (n : nat) (col : {set 'K_n} -> 'I_(n.-1)),
    2 < n ->
    ~~ odd n ->
    C2.X24Legacy.one_factorization col ->
    exists c : seq (complete n),
      X24Legacy.rainbow_cycle col c /\
      (n - 2 <= size c)%N.

End X24Original.

Module XE1Legacy.

Definition cycle_or_edge_piece (G : sgraph) (P : {set {set G}}) : Prop :=
  (exists c : seq G, xe1_cycle c /\ P = Legacy.xe1_cycle_edges c) \/
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

Module XE1Original.

Definition cycle_or_edge_piece (G : sgraph) (P : {set {set G}}) : Prop :=
  (exists c : seq G, B10.Legacy.xe1_cycle c /\ P = Legacy.xe1_cycle_edges c) \/
  (exists e : {set G}, e \in xe1_edge_set G /\ P = [set e]).

Definition erdos_184_statement : Prop :=
  exists C : nat,
    forall G : sgraph,
      exists m : nat, exists P : 'I_m -> {set {set G}},
        m <= C * #|G| /\
        xe1_pairwise_edge_disjoint P /\
        xe1_covers_edges P /\
        forall i : 'I_m, cycle_or_edge_piece (P i).

End XE1Original.

Module XE2Legacy.

Definition edge_disjoint_cycles
    (G : sgraph) (k : nat) (C : 'I_k -> seq G) : Prop :=
  forall i j : 'I_k, i != j ->
    [disjoint Legacy.xe1_cycle_edges (C i) & Legacy.xe1_cycle_edges (C j)].

Definition erdos_641_statement : Prop :=
  exists f : nat -> nat,
    forall (k : nat) (G : sgraph),
      1 <= k ->
      f k <= χ([set: G]) ->
      exists C : 'I_k -> seq G,
        (forall i : 'I_k, xe1_cycle (C i)) /\
        (forall i j : 'I_k, xe2_same_vertex_set (C i) (C j)) /\
        edge_disjoint_cycles C.

End XE2Legacy.

Module XE2Original.

Definition erdos_641_statement : Prop :=
  exists f : nat -> nat,
    forall (k : nat) (G : sgraph),
      1 <= k ->
      f k <= χ([set: G]) ->
      exists C : 'I_k -> seq G,
        (forall i : 'I_k, B10.Legacy.xe1_cycle (C i)) /\
        (forall i j : 'I_k, xe2_same_vertex_set (C i) (C j)) /\
        XE2Legacy.edge_disjoint_cycles C.

End XE2Original.

(** ** Certificates *)

Lemma x9_cycle_edges_compat (G : sgraph) (c : seq G) : Legacy.x9_cycle_edges c = x9_cycle_edges c.
Proof. by []. Qed.

Lemma x24_cycle_edge_seq_compat (G : sgraph) (c : seq G) :
  Legacy.x24_cycle_edge_seq c = x24_cycle_edge_seq c.
Proof. by []. Qed.

Lemma xe1_cycle_edges_compat (G : sgraph) (c : seq G) : Legacy.xe1_cycle_edges c = xe1_cycle_edges c.
Proof. by []. Qed.

Lemma x9_cycle_incident_edges_properly_coloured_compat
    (G : sgraph) (n : nat) (col : {set G} -> 'I_n) (c : seq G) :
  X9Legacy.cycle_incident_edges_properly_coloured col c <->
  x9_cycle_incident_edges_properly_coloured col c.
Proof. exact: iff_refl. Qed.

Lemma proper_edge_coloured_short_cycle_statement_compat :
  X9Legacy.proper_edge_coloured_short_cycle_statement <-> proper_edge_coloured_short_cycle_statement.
Proof. exact: iff_refl. Qed.

(** Before B10 and B11: B10's frozen cycle and this family's frozen colouring chain. *)
Lemma proper_edge_coloured_short_cycle_statement_original_compat :
  X9Original.proper_edge_coloured_short_cycle_statement <-> proper_edge_coloured_short_cycle_statement.
Proof. exact: iff_refl. Qed.

Lemma x24_rainbow_cycle_compat (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (c : seq G) :
  X24Legacy.rainbow_cycle col c <-> x24_rainbow_cycle col c.
Proof. exact: iff_refl. Qed.

Lemma one_factorization_long_rainbow_cycle_statement_compat :
  X24Legacy.one_factorization_long_rainbow_cycle_statement <->
  one_factorization_long_rainbow_cycle_statement.
Proof. exact: iff_refl. Qed.

(** Before C2 and B11: C2's frozen one-factorization chain (through C2's own certificate) and
    this family's frozen rainbow cycle. *)
Lemma one_factorization_long_rainbow_cycle_statement_original_compat :
  X24Original.one_factorization_long_rainbow_cycle_statement <->
  one_factorization_long_rainbow_cycle_statement.
Proof.
by split=> H n col n2 even fact; apply: (H n col n2 even);
  apply/C2.x24_one_factorization_compat.
Qed.

Lemma xe1_cycle_or_edge_piece_compat (G : sgraph) (P : {set {set G}}) :
  XE1Legacy.cycle_or_edge_piece P <-> xe1_cycle_or_edge_piece P.
Proof. exact: iff_refl. Qed.

Lemma erdos_184_statement_compat : XE1Legacy.erdos_184_statement <-> erdos_184_statement.
Proof. exact: iff_refl. Qed.

Lemma xe1_cycle_or_edge_piece_original_compat (G : sgraph) (P : {set {set G}}) :
  XE1Original.cycle_or_edge_piece P <-> xe1_cycle_or_edge_piece P.
Proof. exact: iff_refl. Qed.

(** Before B10 and B11: B10's frozen cycle and this family's frozen edge filter. *)
Lemma erdos_184_statement_original_compat : XE1Original.erdos_184_statement <-> erdos_184_statement.
Proof. exact: iff_refl. Qed.

Lemma xe2_edge_disjoint_cycles_compat (G : sgraph) (k : nat) (C : 'I_k -> seq G) :
  XE2Legacy.edge_disjoint_cycles C <-> xe2_edge_disjoint_cycles C.
Proof. exact: iff_refl. Qed.

Lemma erdos_641_statement_compat : XE2Legacy.erdos_641_statement <-> erdos_641_statement.
Proof. exact: iff_refl. Qed.

(** Before B10 and B11: B10's frozen cycle and this family's frozen edge-disjoint cycles. *)
Lemma erdos_641_statement_original_compat : XE2Original.erdos_641_statement <-> erdos_641_statement.
Proof. exact: iff_refl. Qed.

Print Assumptions x9_cycle_edges_compat.
Print Assumptions x24_cycle_edge_seq_compat.
Print Assumptions xe1_cycle_edges_compat.
Print Assumptions proper_edge_coloured_short_cycle_statement_compat.
Print Assumptions proper_edge_coloured_short_cycle_statement_original_compat.
Print Assumptions one_factorization_long_rainbow_cycle_statement_compat.
Print Assumptions one_factorization_long_rainbow_cycle_statement_original_compat.
Print Assumptions erdos_184_statement_compat.
Print Assumptions erdos_184_statement_original_compat.
Print Assumptions erdos_641_statement_compat.
Print Assumptions erdos_641_statement_original_compat.

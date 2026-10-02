(** * Cycle.migration.perfect_matching -- frozen perfect-matching certificates (C2, 2026-10-02)

    Family: "perfect-matching" (meta/library_primitives/perfect-matching.json); cycle row of
    X24.  Canonical primitive: [GTBase.common.perfect_matching] (a
    [connectivity.matching] covering every vertex), whose API and grounding
    live in base/theories/common.v; public downstream client
    base/theories/examples/perfect_matching.v; generated report
    meta/migration_reports/perfect_matching.md (from
    perfect_matching.spec.json); record meta/LIBRARY_MIGRATION_C2.md.

    ** Frozen source

    [Legacy] freezes the migrated helper [x24_perfect_matching] verbatim as it
    stood at 9e03072, together with the pre-M1 comprehension body of
    [x24_edge_set] (X24.v at 061154c; M1 froze the same text as
    [Cycle.migration.simple_edges.Legacy.edge_set] and the live name has been
    the transparent alias [sg_edge_set G] since), so that the frozen helper
    resolves through no alias of any migration.  [X24Legacy] freezes the
    affected chain of the statement, the statement included, with every
    reference to a frozen name replaced by its frozen copy and the [x24_]
    prefix of the chain name dropped: [x24_one_factorization] (not migrated;
    it reaches the helper) becomes [X24Legacy.one_factorization];
    [x24_rainbow_cycle] and [x24_cycle_edge_seq] reach no migrated name and
    are used as they are.  The report checks every frozen copy against the
    source text at its commit modulo exactly these identifier substitutions.

    ** Certificates

    [x24_edge_set_compat] is the chain certificate of the edge set;
    [x24_perfect_matching_compat] is the helper certificate (frozen "every
    vertex lies in exactly one member" body <-> live alias = canonical
    [perfect_matching], through [perfect_matching_exactly_oneP]);
    [x24_one_factorization_compat] is the chain certificate;
    [one_factorization_long_rainbow_cycle_statement_compat] is the row
    certificate.  The statement body, its status and its documented notes
    (parity hypothesis, affirmative form of a question row) are unchanged.

    Axiom-free: no Axiom/Parameter/Admitted; Print Assumptions at the end. *)

From GTBase Require Import base common.
From Cycle.conjectures Require Import X24.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

(** [x24_edge_set] before M1: X24.v lines 11-13 at 061154c, verbatim
    (the text of Cycle.migration.simple_edges.Legacy.edge_set). *)
Definition x24_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

(** X24.v lines 14-16 at 9e03072, verbatim; [x24_edge_set] is the frozen
    comprehension above. *)
Definition x24_perfect_matching (G : sgraph) (M : {set {set G}}) : Prop :=
  M \subset x24_edge_set G /\
  forall v : G, #|[set e in M | v \in e]| = 1.

End Legacy.

(** ** Helper certificates *)

(** The pre-M1 edge set is the live alias (restates
    Cycle.migration.simple_edges.x24_edge_set_compat so that this certificate
    is self-contained). *)
Lemma x24_edge_set_compat (G : sgraph) :
  Legacy.x24_edge_set G = x24_edge_set G.
Proof. by rewrite /x24_edge_set sg_edge_setE. Qed.

(** The migrated helper: the frozen exact-one-incidence body is the canonical
    perfect matching. *)
Lemma x24_perfect_matching_compat (G : sgraph) (M : {set {set G}}) :
  Legacy.x24_perfect_matching M <-> x24_perfect_matching M.
Proof.
rewrite /Legacy.x24_perfect_matching x24_edge_set_compat /x24_perfect_matching.
exact: iff_sym (perfect_matching_exactly_oneP M).
Qed.

(** ** X24: the chain and the statement *)

Module X24Legacy.

(** X24.v lines 18-21 at 9e03072 with [x24_perfect_matching] ->
    [Legacy.x24_perfect_matching], [x24_edge_set] -> [Legacy.x24_edge_set] and
    the [x24_] prefix dropped. *)
Definition one_factorization
    (n : nat) (col : {set 'K_n} -> 'I_(n.-1)) : Prop :=
  forall i : 'I_(n.-1),
    Legacy.x24_perfect_matching [set e in Legacy.x24_edge_set 'K_n | col e == i].

(** X24.v lines 54-61 at 9e03072 with [x24_one_factorization] ->
    [one_factorization]. *)
Definition one_factorization_long_rainbow_cycle_statement : Prop :=
  forall (n : nat) (col : {set 'K_n} -> 'I_(n.-1)),
    2 < n ->
    ~~ odd n ->
    one_factorization col ->
    exists c : seq (complete n),
      x24_rainbow_cycle col c /\
      (n - 2 <= size c)%N.

End X24Legacy.

Lemma x24_one_factorization_compat (n : nat) (col : {set 'K_n} -> 'I_(n.-1)) :
  X24Legacy.one_factorization col <-> x24_one_factorization col.
Proof.
rewrite /X24Legacy.one_factorization /x24_one_factorization x24_edge_set_compat.
by split=> H i; apply/x24_perfect_matching_compat; exact: H.
Qed.

(** studies:std_akbari_etesami_mahini_mahmoody_question_on_long (unchanged). *)
Lemma one_factorization_long_rainbow_cycle_statement_compat :
  X24Legacy.one_factorization_long_rainbow_cycle_statement <->
  one_factorization_long_rainbow_cycle_statement.
Proof.
by split=> H n col n2 even fact; apply: (H n col n2 even);
  apply/x24_one_factorization_compat.
Qed.

Print Assumptions x24_edge_set_compat.
Print Assumptions x24_perfect_matching_compat.
Print Assumptions x24_one_factorization_compat.
Print Assumptions one_factorization_long_rainbow_cycle_statement_compat.

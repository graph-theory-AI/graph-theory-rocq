(** * Packing.migration.matching -- frozen matching certificates (C1, 2026-10-02)

    Family: "matching" (meta/library_primitives.json), simple-graph edge-family
    representation; packing rows of X15 and X18.  Canonical primitive: upstream
    [GraphTheory.connectivity.matching]; API and grounding in
    theories/foundations/matching.v; public downstream client in
    theories/examples/matching.v; generated report
    meta/migration_reports/matching.md (from matching.spec.json, with the
    source hash and git blob of every frozen declaration); record
    meta/LIBRARY_MIGRATION_C1.md.

    ** Frozen source

    [Legacy] freezes the migrated helper [x15_matching] verbatim as it stood
    at 9e03072, together with the pre-M1 comprehension body of
    [x15_edge_set] (X15.v at 061154c; M1 froze the same text as
    [Packing.migration.simple_edges.Legacy.edge_set] and the live name has
    been the transparent alias [sg_edge_set G] since), so that the frozen
    helper resolves through no alias of any migration.

    [X15Legacy] and [X18Legacy] freeze the affected dependency chain of each
    statement, the statements included, with every reference to a helper of
    this family or of M1 replaced by its frozen copy: [x15_edge_partition]
    and [x15_edge_family] (not migrated; frozen because the statements reach
    [x15_edge_set] through them) become [X15Legacy.edge_partition] and
    [X15Legacy.edge_family]; [x18_perfect_matching] (not migrated; it reaches
    [x15_matching]) becomes [X18Legacy.perfect_matching].  Names that no
    migration touched ([Delta], [bipartite], [ceil_div], [KB],
    [sg_edge_set]) resolve to the live library.  The report checks every
    frozen copy against the source text at its commit modulo exactly these
    identifier substitutions, so no frozen text contains a live name of the
    family.

    ** Certificates

    [x15_matching_compat] is the helper certificate (frozen body <-> live
    alias = upstream [matching]); [x15_edge_set_compat],
    [x15_edge_partition_compat], [x15_edge_family_compat] and
    [x18_perfect_matching_compat] are the chain certificates.  Every
    statement has its own old/new theorem
    [<formal_name>_compat : XnnLegacy.<formal_name> <-> <formal_name>].  No
    statement body, status or documented discrepancy (X15 REFUTED/PROVED
    notes, the X18 partial row) is changed.

    Axiom-free: no Axiom/Parameter/Admitted; Print Assumptions at the end. *)

From GTBase Require Import base common.
From Packing.foundations Require Import matching edge_partitions edge_families.
From Packing.conjectures Require Import X15 X18.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

(** [x15_edge_set] before M1: X15.v lines 11-13 at 061154c, verbatim
    (the text of Packing.migration.simple_edges.Legacy.edge_set). *)
Definition x15_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

(** X15.v lines 14-16 at 9e03072, verbatim; [x15_edge_set] is the frozen
    comprehension above. *)
Definition x15_matching (G : sgraph) (M : {set {set G}}) : Prop :=
  M \subset x15_edge_set G /\
  forall v : G, #|[set e in M | v \in e]| <= 1.

End Legacy.

(** ** Helper certificates *)

(** The pre-M1 edge set is the live alias (restates
    Packing.migration.simple_edges.x15_edge_set_compat so that this
    certificate is self-contained). *)
Lemma x15_edge_set_compat (G : sgraph) :
  Legacy.x15_edge_set G = x15_edge_set G.
Proof. by rewrite /x15_edge_set sg_edge_setE. Qed.

(** The migrated helper: the frozen "at most one member through each vertex"
    body is the upstream matching predicate. *)
Lemma x15_matching_compat (G : sgraph) (M : {set {set G}}) :
  Legacy.x15_matching M <-> x15_matching M.
Proof.
rewrite /Legacy.x15_matching x15_edge_set_compat /x15_matching.
exact: iff_sym (matching_at_most_oneP M).
Qed.

(** ** X15: the chain and the five statements *)

Module X15Legacy.

(** X15.v lines 18-26 at 9e03072 with [x15_edge_set] -> [Legacy.x15_edge_set]
    and the [x15_] prefix of the two chain names dropped. *)
Definition edge_partition
    (G : sgraph) (m : nat) (E : 'I_m -> {set {set G}}) : Prop :=
  (forall e : {set G},
      (e \in Legacy.x15_edge_set G) = [exists i : 'I_m, e \in E i]) /\
  forall i j : 'I_m, i != j -> [disjoint E i & E j].

Definition edge_family
    (G : sgraph) (m : nat) (E : 'I_m -> {set {set G}}) : Prop :=
  forall i : 'I_m, E i \subset Legacy.x15_edge_set G.

(** X15.v lines 49-55, 76-86, 89-100, 106-117 and 124-135 at 9e03072 with
    [x15_matching] -> [Legacy.x15_matching], [x15_edge_set] ->
    [Legacy.x15_edge_set], [x15_edge_partition] -> [edge_partition] and
    [x15_edge_family] -> [edge_family]. *)
Definition fair_matching_edge_partition_statement : Prop :=
  forall (m : nat) (H : sgraph) (E : 'I_m -> {set {set H}}),
    edge_partition E ->
    exists M : {set {set H}},
      Legacy.x15_matching M /\
      forall i : 'I_m,
        (#|E i| %/ (Delta H + 2) <= #|M :&: E i|)%N.

Definition bipartite_matching_underrepresentation_statement : Prop :=
  forall m : nat, exists c : nat,
    forall (G : sgraph) (E : 'I_m -> {set {set G}}),
      bipartite G ->
      0 < Delta G ->
      edge_family E ->
      exists S : {set {set G}},
        Legacy.x15_matching S /\
        (#|Legacy.x15_edge_set G| %/ Delta G <= #|S| + c)%N /\
        forall i : 'I_m,
          #|S :&: E i| <= ceil_div #|E i| (Delta G).

Definition bipartite_matching_underrepresentation_llm_statement : Prop :=
  forall m : nat, exists c : nat,
    c <= 32 * (m + 1)^3 /\
    forall (G : sgraph) (E : 'I_m -> {set {set G}}),
      bipartite G ->
      0 < Delta G ->
      edge_family E ->
      exists S : {set {set G}},
        Legacy.x15_matching S /\
        (#|Legacy.x15_edge_set G| %/ Delta G <= #|S| + c)%N /\
        forall i : 'I_m,
          #|S :&: E i| <= ceil_div #|E i| (Delta G).

Definition bipartite_matching_underrepresentation_llm2_statement : Prop :=
  forall m : nat, exists c : nat,
    c <= (m + 1)^2 * (16*m + 29) /\
    forall (G : sgraph) (E : 'I_m -> {set {set G}}),
      bipartite G ->
      0 < Delta G ->
      edge_family E ->
      exists S : {set {set G}},
        Legacy.x15_matching S /\
        (#|sg_edge_set G| %/ Delta G <= #|S| + c)%N /\
        forall i : 'I_m,
          #|S :&: E i| <= ceil_div #|E i| (Delta G).

Definition bipartite_matching_underrepresentation_llm3_statement : Prop :=
  forall m : nat, exists c : nat,
    c <= 12 * m + 14 /\
    forall (G : sgraph) (E : 'I_m -> {set {set G}}),
      bipartite G ->
      0 < Delta G ->
      edge_family E ->
      exists S : {set {set G}},
        Legacy.x15_matching S /\
        (#|sg_edge_set G| %/ Delta G <= #|S| + c)%N /\
        forall i : 'I_m,
          #|S :&: E i| <= ceil_div #|E i| (Delta G).

End X15Legacy.

Lemma x15_edge_partition_compat
    (G : sgraph) (m : nat) (E : 'I_m -> {set {set G}}) :
  X15Legacy.edge_partition E <-> x15_edge_partition E.
Proof.
by rewrite /X15Legacy.edge_partition /x15_edge_partition
  /edge_partitions.edge_partition x15_edge_set_compat.
Qed.

Lemma x15_edge_family_compat
    (G : sgraph) (m : nat) (E : 'I_m -> {set {set G}}) :
  X15Legacy.edge_family E <-> x15_edge_family E.
Proof.
by rewrite /X15Legacy.edge_family /x15_edge_family
  /edge_families.edge_family x15_edge_set_compat.
Qed.

(** arxiv:1611.03196#02 (REFUTED, unchanged). *)
Lemma fair_matching_edge_partition_statement_compat :
  X15Legacy.fair_matching_edge_partition_statement <->
  fair_matching_edge_partition_statement.
Proof.
split=> H m G E partE.
- have [M [mM bound]] := H m G E ((x15_edge_partition_compat E).2 partE).
  by exists M; split=> //; apply/x15_matching_compat.
- have [M [mM bound]] := H m G E ((x15_edge_partition_compat E).1 partE).
  by exists M; split=> //; apply/x15_matching_compat.
Qed.

(** arxiv:1611.03196#03 (PROVED in foundations/fair_matching.v, unchanged). *)
Lemma bipartite_matching_underrepresentation_statement_compat :
  X15Legacy.bipartite_matching_underrepresentation_statement <->
  bipartite_matching_underrepresentation_statement.
Proof.
split=> H m; have [c Hc] := H m; exists c => G E bipG dpos famE.
- have [S [mS [size parts]]] :=
    Hc G E bipG dpos ((x15_edge_family_compat E).2 famE).
  exists S; split; first exact/x15_matching_compat.
  by split=> //; rewrite -x15_edge_set_compat.
- have [S [mS [size parts]]] :=
    Hc G E bipG dpos ((x15_edge_family_compat E).1 famE).
  exists S; split; first exact/x15_matching_compat.
  by split=> //; rewrite x15_edge_set_compat.
Qed.

(** LLM-proof variant with the explicit bound 32 (m+1)^3 (no corpus row). *)
Lemma bipartite_matching_underrepresentation_llm_statement_compat :
  X15Legacy.bipartite_matching_underrepresentation_llm_statement <->
  bipartite_matching_underrepresentation_llm_statement.
Proof.
split=> H m; have [c [cle Hc]] := H m; exists c; split=> // G E bipG dpos famE.
- have [S [mS [size parts]]] :=
    Hc G E bipG dpos ((x15_edge_family_compat E).2 famE).
  exists S; split; first exact/x15_matching_compat.
  by split=> //; rewrite -x15_edge_set_compat.
- have [S [mS [size parts]]] :=
    Hc G E bipG dpos ((x15_edge_family_compat E).1 famE).
  exists S; split; first exact/x15_matching_compat.
  by split=> //; rewrite x15_edge_set_compat.
Qed.

(** LLM-proof variant with the bound (m+1)^2 (16m+29) (no corpus row). *)
Lemma bipartite_matching_underrepresentation_llm2_statement_compat :
  X15Legacy.bipartite_matching_underrepresentation_llm2_statement <->
  bipartite_matching_underrepresentation_llm2_statement.
Proof.
split=> H m; have [c [cle Hc]] := H m; exists c; split=> // G E bipG dpos famE.
- have [S [mS [size parts]]] :=
    Hc G E bipG dpos ((x15_edge_family_compat E).2 famE).
  by exists S; split; first exact/x15_matching_compat.
- have [S [mS [size parts]]] :=
    Hc G E bipG dpos ((x15_edge_family_compat E).1 famE).
  by exists S; split; first exact/x15_matching_compat.
Qed.

(** LLM-proof variant with the bound 12m + 14 (no corpus row). *)
Lemma bipartite_matching_underrepresentation_llm3_statement_compat :
  X15Legacy.bipartite_matching_underrepresentation_llm3_statement <->
  bipartite_matching_underrepresentation_llm3_statement.
Proof.
split=> H m; have [c [cle Hc]] := H m; exists c; split=> // G E bipG dpos famE.
- have [S [mS [size parts]]] :=
    Hc G E bipG dpos ((x15_edge_family_compat E).2 famE).
  by exists S; split; first exact/x15_matching_compat.
- have [S [mS [size parts]]] :=
    Hc G E bipG dpos ((x15_edge_family_compat E).1 famE).
  by exists S; split; first exact/x15_matching_compat.
Qed.

(** ** X18: the chain and the two statements *)

Module X18Legacy.

(** X18.v lines 34-36 at 9e03072 with [x15_matching] -> [Legacy.x15_matching]
    and the [x18_] prefix dropped. *)
Definition perfect_matching (G : sgraph) (M : {set {set G}}) : Prop :=
  Legacy.x15_matching M /\
  forall v : G, #|[set e in M | v \in e]| = 1.

(** X18.v lines 86-93 and 108-116 at 9e03072 with [x15_edge_partition] ->
    [X15Legacy.edge_partition], [x18_perfect_matching] -> [perfect_matching]
    and [x15_matching] -> [Legacy.x15_matching]. *)
Definition knn_fair_perfect_matching_statement : Prop :=
  forall (n m : nat) (E : 'I_m -> {set {set KB n n}}) (j : 'I_m),
    0 < n ->
    X15Legacy.edge_partition E ->
    exists F : {set {set KB n n}},
      perfect_matching F /\
      (forall i : 'I_m, i != j -> (#|E i| %/ n <= #|F :&: E i|)%N) /\
      (#|E j| %/ n - 1 <= #|F :&: E j|)%N.

Definition brualdi_stein_partial_transversal_statement : Prop :=
  forall (n : nat) (E : 'I_n -> {set {set KB n n}}),
    0 < n ->
    X15Legacy.edge_partition E ->
    (forall i : 'I_n, #|E i| = n) ->
    exists M : {set {set KB n n}},
      Legacy.x15_matching M /\
      (n.-1 <= #|M|)%N /\
      forall i : 'I_n, #|M :&: E i| <= 1.

End X18Legacy.

(** Since C2 (2026-10-02) the live [x18_perfect_matching] is the alias of
    [GTBase.common.perfect_matching]; the frozen body above is unchanged and the
    certificate goes through [perfect_matching_exactly_oneP]. *)
Lemma x18_perfect_matching_compat (G : sgraph) (M : {set {set G}}) :
  X18Legacy.perfect_matching M <-> x18_perfect_matching M.
Proof.
rewrite /X18Legacy.perfect_matching /x18_perfect_matching perfect_matching_exactly_oneP.
split=> -[mM one]; split=> //.
- exact: matching_subset ((x15_matching_compat M).1 mM).
- by apply/x15_matching_compat/matching_at_most_oneP; split=> // v; rewrite one.
Qed.

(** arxiv:1611.03196#01 (partial row, unchanged). *)
Lemma knn_fair_perfect_matching_statement_compat :
  X18Legacy.knn_fair_perfect_matching_statement <->
  knn_fair_perfect_matching_statement.
Proof.
split=> H n m E j npos partE.
- have [F [pmF bounds]] := H n m E j npos ((x15_edge_partition_compat E).2 partE).
  by exists F; split=> //; apply/x18_perfect_matching_compat.
- have [F [pmF bounds]] := H n m E j npos ((x15_edge_partition_compat E).1 partE).
  by exists F; split=> //; apply/x18_perfect_matching_compat.
Qed.

(** studies:std_brualdi_stein_conjecture (unchanged). *)
Lemma brualdi_stein_partial_transversal_statement_compat :
  X18Legacy.brualdi_stein_partial_transversal_statement <->
  brualdi_stein_partial_transversal_statement.
Proof.
split=> H n E npos partE sizes.
- have [M [mM bounds]] :=
    H n E npos ((x15_edge_partition_compat E).2 partE) sizes.
  by exists M; split=> //; apply/x15_matching_compat.
- have [M [mM bounds]] :=
    H n E npos ((x15_edge_partition_compat E).1 partE) sizes.
  by exists M; split=> //; apply/x15_matching_compat.
Qed.

Print Assumptions x15_edge_set_compat.
Print Assumptions x15_matching_compat.
Print Assumptions x15_edge_partition_compat.
Print Assumptions x15_edge_family_compat.
Print Assumptions x18_perfect_matching_compat.
Print Assumptions fair_matching_edge_partition_statement_compat.
Print Assumptions bipartite_matching_underrepresentation_statement_compat.
Print Assumptions bipartite_matching_underrepresentation_llm_statement_compat.
Print Assumptions bipartite_matching_underrepresentation_llm2_statement_compat.
Print Assumptions bipartite_matching_underrepresentation_llm3_statement_compat.
Print Assumptions knn_fair_perfect_matching_statement_compat.
Print Assumptions brualdi_stein_partial_transversal_statement_compat.
